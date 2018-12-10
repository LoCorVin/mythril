
from ethereum import utils
from mythril.analysis.symbolic import SymExecWrapper
from mythril.support.loader import DynLoader
from mythril.ether.soliditycontract import SolidityContract
from mythril.laser.ethereum.state import MachineState, GlobalState, Account, Environment, CalldataType
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.ethereum.instructions import keccak_map

from mythril.annotary.sn_utils import get_sourcecode_and_mapping, flatten, find_contract_idx_range, get_containing_file
from mythril.annotary.transactiontrace import TransactionTrace
from mythril.annotary.z3utility import are_z3_satisfiable
from mythril.annotary.calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi, get_calldata_name_map
from mythril.annotary.coderewriter import write_code, get_code, replace_comments_with_whitespace, apply_rewriting
from mythril.annotary.codeparser import find_matching_closed_bracket, newlines, get_newlinetype, find_first_uncommented_str
from mythril.annotary.stateprocessing import AnnotationProcessor
from mythril.annotary.annotation import annotation_kw, init_annotation, increase_rewritten_pos, comment_out_annotations, expand_rew
from mythril.annotary.ast_parser import get_contract_ast, get_function_asts, get_function_param_tuples, get_function_term_positions, get_struct_map
from mythril.annotary.storage_members import extract_storage_map
from mythril.annotary.ast_parser import get_all_nested_dicts_with_kv_pairs, get_all_functions_for_contract
import sys
import faulthandler
import signal
from threading import Thread
from multiprocessing.dummy import Pool as ThreadPool
from concurrent.futures import ThreadPoolExecutor
import platform
import time

from mythril.annotary.config import Config

from mythril.annotary.transchainstrategy import BackwardChainStrategy

from z3 import BitVec,eq, simplify
from os.path import exists, isdir, dirname, isfile, join
from os import makedirs, chdir, listdir
from re import finditer, escape
from shutil import rmtree, copy
from re import DOTALL
from functools import reduce
from mythril.annotary.debugc import printd
from mythril.annotary.annotation import get_origin_pos_line_col, Status

from json import dumps

project_name = "annotary"

tmp_dir_name = project_name + "_tmp"

laser_strategy = "dfs"


class SolidityFunction:

    def __init__(self, f_ast, file_code, calldata_name_map):
        attributes = f_ast['attributes']



        self.ast = f_ast
        self.constant = attributes['constant']
        self.implemented = attributes['implemented']
        self.modifiers = attributes['modifiers'] if 'modfiers' in attributes else None
        self.payable = attributes['payable']
        self.stateMutability = attributes['stateMutability']
        self.visibility = attributes['visibility']
        self.name = attributes['name']
        self.isConstructor = attributes['isConstructor']
        self.params = []
        self.src = f_ast['src']


        self.start = int(self.src[:self.src.index(":")])
        self.length = int(self.src[self.src.index(":") + 1:self.src.rfind(":")])
        self.file_idx = int(self.src[self.src.rfind(":")+1:])
        self.end = int(self.start + self.length)


        self.code = file_code[self.start:self.end]

        self.head = self.code[:find_first_uncommented_str(self.code, "{")]

        self.params = get_function_param_tuples(f_ast)
        params = ""
        for param in self.params:
            params += param[1] + ","

        if len(params) > 0:
            params = params[:len(params)-1]
        if self.isConstructor:
            self.signature = "(" + params + ")"
            self.hash = ""
        else:
            self.signature = self.name + "(" + params + ")"
            self.hash = utils.sha3(self.signature)[:4].hex()

        self.calldata_name_map = calldata_name_map[self.signature] if self.signature in calldata_name_map else []

        # Parses the positions in the function where exution might terminated due to a return
        self.return_types, self.terminating_pos = get_function_term_positions(f_ast)


class SymbolicCodeExtension:

    def __init__(self, symbolic_name, contract_name, extension_byte_size, predefined_map={}):
        self.symbolic_name = symbolic_name
        self.contract_name = contract_name
        self.extension_byte_size = extension_byte_size
        self.predifined_map = predefined_map

    def __len__(self):
        return self.extension_byte_size

    def __getitem__(self, item):
        if item in self.predifined_map:
            return self.predifined_map[item]
        return BitVec(self.symbolic_name + "_" + self.contract_name + "[" + str(item) + "]", 256)


def find_all(a_str, sub):
    start = 0
    while True:
        start = a_str.find(sub, start)
        if start == -1:
            return
        yield start
        start += len(sub)


def count_elements(source, elements):
    ret = 0
    for element in elements:
        ret += source.count(element)
    return ret


def replace_index(text, toReplace, replacement, index):
    return text[:index] + replacement + text[(index + len(toReplace)):]







def augment_with_ast_info(contract):
    """
        Parses the ast to find all positions where a contract might terminate with a transactions execution.
    """
    contract.functions = []
    contract_file = get_containing_file(contract)
    ast = contract_file.ast



    contract.ast = get_contract_ast(ast, contract.name) # Attention, here we write over a already filled variable


    f_asts = get_all_functions_for_contract(contract)


    # f_asts = get_function_asts(contract.ast)
    contract.calldata_name_map = get_calldata_name_map(abi_json_to_abi(contract.abi))
    for f_ast in f_asts:
        file = get_containing_file(contract)
        contract.functions.append(SolidityFunction(f_ast, file.data, contract.calldata_name_map))
        if f_ast in contract.implemented_functions:
            contract.implemented_functions[contract.implemented_functions.index(f_ast)] = contract.functions[-1]





def get_sorting_priority(rew_text):
    if rew_text == "{":
        return 0
    elif rew_text.startswith("function"):
        return 1
    elif rew_text.startswith("var"):
        return 2
    elif rew_text.startswith("super."):
        return 3
    elif rew_text.startswith("assert"):
        return 4
    elif rew_text == "return":
        return 5
    elif rew_text == "*/":
        return 6
    elif rew_text == "}":
        return 7
    return 8



def get_contract_code(contract):
    crange = find_contract_idx_range(contract)
    contract_code = get_containing_file(contract).data[crange[0]:crange[2]]
    return contract_code
"""
    Here it might be better to split annotations into the containing constraint an the prefix and sufix
"""

class Annotary:

    def __init__(self, solc_args, config_file):

        self.filename_map = {} # from tmp filename to original filename

        self.solc_args = solc_args

        self.config = Config(config_file)

        self.wd = "/tmp"
        self.tmp_dir = None
        self.contract_name = None
        self.annotation_map = {}
        self.annotated_contracts = []

        self.origin_file = {}

        self.storage_map = {}

    def create_tmp_dir(self):
        self.tmp_dir = self.wd + "/" + tmp_dir_name

        if exists(self.tmp_dir) and isdir(self.tmp_dir):
            rmtree(self.tmp_dir)
        makedirs(self.tmp_dir)

    def set_contract_name(self, contract_name):
        self.contract_name = contract_name

    def copy_files_to_tmp(self, files):
        for file in files:
            dirna = dirname(file)
            if dirna and not exists(dirna):
                makedirs(dirna)
            filename = file
            if "/" in filename:
                filename = filename[filename.rfind("/")+1:]
            copy(file, self.tmp_dir + "/" + filename)
            if file.endswith(".sol"):
                code = get_code(self.tmp_dir + "/" + filename)
                code = replace_comments_with_whitespace(code)
                write_code(self.tmp_dir + "/" + filename, code)
                self.origin_file[self.tmp_dir + "/" + filename] = comment_out_annotations(self.tmp_dir + "/" + filename)
                self.filename_map[self.tmp_dir + "/" + filename] = file

    def copy_dir_content_to_tmp(self, dirpath):
        src_files = listdir(dirpath)
        for file_name in src_files:
            full_file_name = join(dirpath, file_name)
            if isfile(full_file_name):
                copy(full_file_name, self.tmp_dir)
                # Todo consider subdirectories and symbolic links

    def provide_resources(self, contracts, address, eth, dynld, sigs, max_depth=None):
        self.contracts = contracts
        self.address = address
        self.eth = eth
        self.dynld = dynld
        self.max_depth = max_depth
        self.sigs = sigs

    def get_lineno_stop_inst(self):
        pass


    def parse_annotations(self):
        struct_map = get_struct_map(flatten([contract.solidity_files for contract in self.contracts]))
        # Todo from which contract to parse?
        for contract in self.contracts:
            if self.contract_name and contract.name != self.contract_name:
                continue


            contract_file = get_containing_file(contract)
            contract.contract_range = find_contract_idx_range(contract)
            code = contract_file.data[contract.contract_range[0]:contract.contract_range[2]]


            augment_with_ast_info(contract)

            # Todo Saving Storage Mapping with mappings in contract might not be necessary
            self.storage_map[contract.name] = extract_storage_map(contract, struct_map)
            contract.storage_map = self.storage_map[contract.name]

            for function in contract.functions:
                function.terminating_pos = list(map(lambda pos: (pos[0] - contract.contract_range[0], pos[1]), function.terminating_pos))

            for kw in annotation_kw:
                annot_iterator = finditer(escape('/*@') + escape(kw), code)
                annot_iter = next(annot_iterator, None)
                if annot_iter and contract.name not in self.annotation_map:
                    self.annotation_map[contract.name] = []
                while annot_iter:
                    origin = get_origin_pos_line_col(contract_file.data[:contract.contract_range[0]+annot_iter.start()])
                    annotation = init_annotation(contract, code, annot_iter.group(), kw, annot_iter.start(),
                                                    annot_iter.end(), origin, self.config)
                    if annotation:
                        self.annotation_map[contract.name].append(annotation)
                    annot_iter = next(annot_iterator, None)



    def build_annotated_contracts(self):
        file_rewritings = {}

        for contract in self.contracts:
            if contract.name not in self.annotation_map:
                continue
            annotations = self.annotation_map[contract.name]
            sol_file = get_containing_file(contract)
            file_code = sol_file.data

            contract_range = find_contract_idx_range(contract)
            contract_code = file_code[contract_range[0]:(contract_range[2] + 1)]

            # Todo Subtract contract offset

            contract_prefix = file_code[:contract_range[0]]
            contract_suffix = file_code[(contract_range[2] + 1):]

            contract_prefix_as_rew = expand_rew("", contract_code, (contract_prefix, 0))

            rew_contract_code = contract_code

            rewritings = []

            for annotation in annotations:
                rewritings.extend(annotation.rewrite_code(file_code, contract_code, contract_range))

            rewriting_set = []
            for rewriting in rewritings:
                if rewriting not in rewriting_set:
                    rewriting_set.append(rewriting)
            rewritings = rewriting_set

            rewritings = sorted(rewritings, key=lambda rew:(rew.pos, rew.gname, get_sorting_priority(rew.text)))

            for rew_idx in range(len(rewritings)):
                rew = rewritings[rew_idx]
                rew_contract_code = apply_rewriting(rew_contract_code, rew)
                increase_rewritten_pos(rewritings, rewritings[rew_idx], get_newlinetype(file_code))

            increase_rewritten_pos(rewritings, contract_prefix_as_rew, get_newlinetype(file_code))

            rew_file_code = contract_prefix + rew_contract_code + contract_suffix

            # in line should be done for every annotation later
            #printd("----")
            #printd(rew_file_code)
            #printd("----")
            printd("Rewritten code")
            printd(rew_file_code)
            write_code(sol_file.filename, rew_file_code)

            annotation_contract = SolidityContract(sol_file.filename, contract.name, solc_args=self.solc_args)
            augment_with_ast_info(annotation_contract)
            annotation_contract.rewritings = rewritings
            # Todo maybe i dont need this
            annotation_contract.origin_file_code = file_code
            annotation_contract.original_contract = contract
            self.annotated_contracts.append(annotation_contract)

            for annotation in self.annotation_map[contract.name]:
                annotation.set_annotation_contract(annotation_contract)

            write_code(sol_file.filename, file_code)



    def get_traces_and_build_violations(self, contract):
        dynloader = DynLoader(self.eth) if self.dynld else None

        # Building ignore lists for transactions and constructor executions
        create_ignore_list = []
        trans_ignore_list = []

        # ignore_list = []

        for annotation in self.annotation_map[contract.name]:
            create_ignore_list.extend(annotation.get_creation_ignore_list())
            trans_ignore_list.extend(annotation.get_trans_ignore_list())

        counter = 0

        # Used to run annotations violation build in traces construction in parallel
        annotationsProcessor = None
        if any([len( annotation.viol_rew_instrs) > 0 for annotation in self.annotation_map[contract.name]]):
            annotationsProcessor = AnnotationProcessor(contract.creation_disassembly.instruction_list,
                                        contract.disassembly.instruction_list, create_ignore_list, trans_ignore_list,
                                        contract)

        # Symbolic execution of construction and transactions
        printd("Constructor and Transaction")

        constr_calldata_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))
        sym_code_extension = SymbolicCodeExtension("calldata", contract.name, constr_calldata_len)

        global keccak_map
        keccak_map = {}
        if self.max_depth:
            self.config.mythril_depth = self.max_depth
        printd("Sym Exe: " + str(contract.name))
        start = time.time()
        sym_transactions = SymExecWrapper(contract, self.address, laser_strategy, dynloader, max_depth=self.config.mythril_depth,
                                          prepostprocessor=annotationsProcessor, code_extension=sym_code_extension) # Todo Mix the annotation Processors or mix ignore listst
        contract.states = []

        contract.states = sym_transactions.laser.state_id_assigner.states
        contract.config = self.config

        end = time.time()
        # print(end - start)
        if annotationsProcessor:
            printd("Construction Violations: " + str(len(reduce(lambda x, y: x + y, annotationsProcessor.create_violations, []))))
            printd("Transaction Violations: " + str(len(reduce(lambda x, y: x + y, annotationsProcessor.trans_violations, []))))

        # Add found violations to the annotations they violated
        # Todo Extract violations from only one symbolic execution
        for ign_idx in range(len(trans_ignore_list)):
            annotation = trans_ignore_list[ign_idx][4]
            #mapping = get_sourcecode_and_mapping(trans_ignore_list[ign_idx][2]['address'], contract.disassembly.instruction_list, contract.mappings)
            annotation.add_violations(annotationsProcessor.trans_violations[ign_idx], contract, length=0,
                    vio_description="An assert with the annotations condition would fail here.")

        for ign_idx in range(len(create_ignore_list)):
            annotation = create_ignore_list[ign_idx][4]
            #mapping = get_sourcecode_and_mapping(create_ignore_list[ign_idx][2]['address'], contract.creation_disassembly.instruction_list, contract.creation_mappings)
            annotation.add_violations(annotationsProcessor.create_violations[ign_idx], contract, length=0,
                                      vio_description="An assert with the annotations condition would fail here.")

        for annotation in self.annotation_map[contract.name]:
            annotation.build_violations(sym_transactions)


        # Build traces from the regular annotation ignoring global states
        # create_traces = get_construction_traces(sym_creation)
        # Todo change traces extraction in a way to use mappings to differentiate between construction and transaction
        start_time = time.time()
        create_traces, trans_traces = get_traces(sym_transactions, contract)
        printd("--- %s seconds ---" % (time.time() - start_time))

        return create_traces, trans_traces

    def build_traces_and_violations(self):
        for contract in self.annotated_contracts:
            const_traces, trans_traces = self.get_traces_and_build_violations(contract)
            contract.const_traces = const_traces
            contract.trans_traces = trans_traces






    def check_annotations(self):

        self.build_annotated_contracts()
        self.build_traces_and_violations()


        printd("Chain_building")
        # Individual violation processing, set states and filter those where it is not decided for chaining

        # Chaining and status update until all have fixed states or a certain limit is reached
        for contract in self.annotated_contracts:
            annotations = self.annotation_map[contract.name]
            chain_strat = BackwardChainStrategy(contract.const_traces, contract.trans_traces, annotations, self.config)
            printd("Start")

            if self.config.mythril_depth > 0 and self.config.chain_verification:
                chain_strat.check_violations()

            for annotation in annotations:
                status = annotation.status
                for violation in annotation.violations:
                    if violation.status.value > status.value:
                        status = violation.status
                annotation.status = status

            printd("Stop")
        # Todo Maybe filter violations if the annotation is only broken if it was broken before

        # Todo Set status, perform trace chaining strategy. Update Status

        # Todo Return the annotations with violation information


    def get_annotation_json(self):
        return dumps({contract_name: [annotation.get_dictionary(self.filename_map) for annotation in annotations] for contract_name,
                                                annotations in self.annotation_map.items()}, sort_keys=True, indent=4)


    def enter_tmp_dir(self):
        chdir(self.tmp_dir)

    def exit_tmp_dir(self):
        chdir(self.wd)

    def delete_tmp_dir(self):
        chdir(self.wd)
        if exists(self.tmp_dir) and isdir(self.tmp_dir):
            rmtree(self.tmp_dir)

    def notarize(self):
        # Todo Instantiate an instance of Mythril, analyze and print the result
        # Todo Find how they are storing results
        pass

def is_storage_primitive(storage):
    if storage:
        for index, content in storage._storage.items():
            if isinstance(content, int) or not eq(content, BitVec("storage[" + str(index) + "]", 256)):
                return False
    return True



def get_traces(statespace, contract):
    states = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            state.contract = contract
            states.append(state)

    printd("Sequential Tracebuilding")
    results = [get_trace_for_state(state) for state in states]
    printd("Finished")

    return [trace for trace_type, trace in results if trace is not None and trace_type == "c"], \
            [trace for trace_type, trace in results if trace is not None and trace_type == "t"]


def get_trace_for_state(state):
    ''' Returns a representation of a transaction trace if this state marks a transaction en, if not None is returned'''
    instruction = state.get_current_instruction()
    if instruction['opcode'] in ["STOP", "RETURN"]:
        storage = state.environment.active_account.storage
        if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
            if isinstance(state.current_transaction, ContractCreationTransaction):
                istr_list = state.contract.creation_disassembly.instruction_list
                mappings = state.contract.creation_mappings
            else:
                istr_list = state.contract.disassembly.instruction_list
                mappings = state.contract.mappings

            mapping = get_sourcecode_and_mapping(instruction['address'], istr_list, mappings)

            if mapping:

                trace = TransactionTrace(state, state.contract)
                if isinstance(state.current_transaction, ContractCreationTransaction):
                    return "c", trace
                else:
                    return "t", trace
            # The case with no mapping at a STOP or RETURN instruction is ignore
    return None, None


def get_traces_parallel(statespace, contract):
    faulthandler.dump_traceback(file=sys.stderr, all_threads=True)
    states = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            if state.get_current_instruction()['opcode'] in ["STOP", "RETURN"]:
                state.contract = contract
                states.append(state)

    #print("Parallel Trace building")
    #signal.signal(signal.SIGSEGV, sig_handler)
    #max_threads = 2
    #results = [None]*len(states)
    #threads = [Thread(target=get_traces_mod, args=(states, results, i, max_threads)) for i in range(max_threads)]
    #for thread in threads:
    #    thread.start()
    #for thread in threads:
    #    thread.join()
    pool = ThreadPool(4)
    results = pool.map(get_trace_for_state, states)
    pool.close()
    pool.join()
    #results = []
    #with ThreadPoolExecutor(max_workers=4) as e:
        #for state in states:
        #    results.append(e.submit(get_trace_for_state, state))
        #results = [result.result() for result in results]
        ##results = e.map(get_trace_for_state, states)

    print("Finished")
    print(results)

    return [trace for trace_type, trace in results if trace is not None and trace_type == "c"], \
           [trace for trace_type, trace in results if trace is not None and trace_type == "t"]

def get_traces_mod(states,results, nr, mod):
    i = nr
    print(len(states))
    while i < len(states):
        results[i] = get_trace_for_state(states[i])
        print(i)
        i += mod


def get_construction_traces(statespace):
    printd("get_constructor_traces")
    num_elimi_traces= 0
    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode']  in ["STOP", "RETURN"]:
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state))
                else:
                    num_elimi_traces += 1
    printd("Construction traces: " + str(len(traces)) + " eliminated: " + str(num_elimi_traces))
    return traces

def get_constr_glbstate(contract, address):

    mstate = MachineState(gas=10000000)

    minimal_const_byte_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))

    # better would be to append symbolic params to the bytecode such that the codecopy instruction that copies the
    # params into memory takes care of placing them onto the memory with the respective size.
    for i in range(int(minimal_const_byte_len / 32)):
        mstate.mem_extend(128 + 32 * i, 32)
        mstate.memory.insert(128 + 32 * i, BitVec('calldata_' + contract.name + '[' + str(i * 32)+ "]", 256))


    # Todo Replace pure placement of enough symbolic 32 Byte-words with placement of symbolic variables that contain
    # the name of the solidity variables

    accounts = {address: Account(address, contract.disassembly, contract_name=contract.name)}

    environment = Environment(
        accounts[address],
        BitVec("caller", 256),
        [],
        BitVec("gasprice", 256),
        BitVec("callvalue", 256),
        BitVec("origin", 256),
        calldata_type=CalldataType.SYMBOLIC,
    )

    # Todo find source for account info, maybe the std statespace?

    return GlobalState(accounts, environment, None, mstate)

def get_t_indexed_environment(active_account, index):

        # Initialize the execution environment

        environment = Environment(
            active_account,
            BitVec("caller_"+str(index), 256),
            [],
            BitVec("gasprice_"+str(index), 256),
            BitVec("callvalue_"+str(index), 256),
            BitVec("origin_"+str(index), 256),
            calldata_type=CalldataType.SYMBOLIC,
        )

        return environment

#def get_t_indexed_globstate(active_account, index):
#    environment = get_t_indexed_environment(active_account, index)
#    # Todo is this just some set of preset accounts? How should we deal with it
#    return GlobalState(self.accounts, environment)

