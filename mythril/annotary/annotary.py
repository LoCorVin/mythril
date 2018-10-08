
from ethereum import utils
from mythril.analysis.symbolic import SymExecWrapper
from mythril.support.loader import DynLoader
from mythril.ether.soliditycontract import SolidityContract
import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum.state import MachineState, GlobalState, Account, Environment, CalldataType
from mythril.laser.ethereum.transaction import ContractCreationTransaction

from .sn_utils import get_sourcecode_and_mapping, flatten
from .transactiontrace import TransactionTrace
from .z3utility import are_z3_satisfiable
from .calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi, get_calldata_name_map
from .coderewriter import write_code, get_code, replace_comments_with_whitespace, apply_rewriting
from .codeparser import find_matching_closed_bracket, newlines, get_newlinetype
from .stateprocessing import AnnotationProcessor
from .annotation import annotation_kw, init_annotation, increase_rewritten_pos, comment_out_annotations, expand_rew
from .ast_parser import get_contract_ast, get_function_asts, get_function_param_tuples, get_function_term_positions, get_struct_map
from .storage_members import extract_storage_map

from z3 import BitVec,eq
from os.path import exists, isdir, dirname, isfile, join
from os import makedirs, chdir, listdir, getcwd
from re import finditer, escape
from shutil import rmtree, copy
from re import findall, DOTALL
from functools import reduce
from .debugc import printd

project_name = "annotary"

tmp_dir_name = project_name + "_tmp"

laser_strategy = "dfs"


class SolidityFunction:

    def __init__(self, f_ast, calldata_name_map):
        attributes = f_ast['attributes']


        self.constant = attributes['constant']
        self.implemented = attributes['implemented']
        self.modifiers = attributes['modifiers']
        self.payable =  attributes['payable']
        self.stateMutability = attributes['stateMutability']
        self.visibility = attributes['visibility']
        self.name = attributes['name']
        self.isConstructor = attributes['isConstructor']
        self.params = []

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

        self.calldata_name_map = calldata_name_map[self.signature]

        # Parses the positions in the function where exution might terminated due to a return
        self. return_types, self.terminating_pos = get_function_term_positions(f_ast)


class SymbolicCodeExtension:

    def __init__(self, symbolic_name, contract_name, extension_byte_size):
        self.symbolic_name = symbolic_name
        self.contract_name = contract_name
        self.extension_byte_size = extension_byte_size

    def __len__(self):
        return self.extension_byte_size

    def __getitem__(self, item):
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


def get_containing_file(contract):
    contract_name = contract.name
    containing_file = None
    for sol_file in contract.solidity_files:
        contract_idx = next(finditer(r'contract\s*' + escape(contract_name) + r'(.*?){', sol_file.data, flags=DOTALL), None)
        if contract_idx:
            containing_file = sol_file
            break
    return containing_file




"""
    Parses the ast to find all positions where a contract might terminate with a transactions execution.
"""
def augment_with_ast_info(contract):
    contract.functions = []
    contract_file = get_containing_file(contract)
    ast = contract_file.ast
    contract.ast = get_contract_ast(ast, contract.name) # Attention, here we write over a already filled variable
    f_asts = get_function_asts(contract.ast)
    contract.calldata_name_map = get_calldata_name_map(abi_json_to_abi(contract.abi))
    for f_ast in f_asts:
        contract.functions.append(SolidityFunction(f_ast, contract.calldata_name_map))


def find_contract_idx_range(contract):
    containing_file = get_containing_file(contract)
    contract_idx = next(finditer(r'contract\s*' + escape(contract.name) + r'(.*?){', containing_file.data, flags=DOTALL), None)

    start_head = contract_idx.start()
    end_head = contract_idx.end() - 1
    end_contract = find_matching_closed_bracket(containing_file.data, end_head)
    return start_head, end_head, end_contract

def get_sorting_priority(rew_text):
    if rew_text == "{":
        return 0
    elif rew_text.startswith("var"):
        return 1
    elif rew_text.startswith("assert"):
        return 2
    elif rew_text == "return":
        return 3
    elif rew_text == "*/":
        return 4
    elif rew_text == "}":
        return 5
    return 6

def get_contract_code(contract):
    crange = find_contract_idx_range(contract)
    contract_code = get_containing_file(contract).data[crange[0]:crange[2]]
    return contract_code
"""
    Here it might be better to split annotations into the containing constraint an the prefix and sufix
"""


#def parse_annotation_info(filedata):
#    annotations = []
#    for inv in findall(r'/*@invariant\<([^\)]+)\>;(\r\n|\r|\n)', filedata):
#        match_inv = "/*@invariant<" + inv[0] + ">;"
#        for pos in find_all(filedata, match_inv + inv[1]):
#            line = count_elements(filedata[:pos], newlines) + 1
#            col = pos - max(map(lambda x: filedata[:pos].rfind(x), newlines))
#            annotations.append((pos, line, col, '//invariant(', inv[0], ")", inv[1]))
#    return set(annotations)

#def parse_annotation_info(code):
#    annotations = []
#    for kw in annotation_kw:
#        annot_iterator = finditer(r'/*@' + escape(kw), code)
#        annot_iter = next(annot_iterator, None)
#        while annot_iter:
#            print(annot_iter.group())
#            print(code[annot_iter.start():annot_iter.end()])
#            annotation = init_annotation(code, annot_iter.group(), kw, annot_iter.start(), annot_iter.end())
#            annotations.append(annotation)
#            annot_iter = next(annot_iterator, None)


#def read_write_file(filename):
#    with open(filename, 'r') as file:
#        filedata = file.read()
#
#    annotations = parse_annotation_info(filedata)
#
#    annotations = sorted(list(annotations), key=lambda x: x[0], reverse=True)
#    for annotation in annotations:
#        filedata = replace_index(filedata, annotation[3] + annotation[4] + annotation[5] + annotation[6], "assert("
#                                 + annotation[4] + ");" + annotation[6], annotation[0])
    # Replace the target string
    # filedata = filedata.replace('@ensure', '@invariant')
    # filedata = filedata.replace('@invariant', '@ensure')

#    with open(filename, 'w') as file:
#        file.write(filedata)
#    return annotations

class Annotary:

    def __init__(self, solc_args):
        self.solc_args = solc_args

        self.wd = getcwd()
        self.tmp_dir = None
        self.annotation_map = {}
        self.annotated_contracts = []

        self.storage_map = {}

    def create_tmp_dir(self):
        self.tmp_dir = self.wd + "/" + tmp_dir_name

        if exists(self.tmp_dir) and isdir(self.tmp_dir):
            rmtree(self.tmp_dir)
        makedirs(tmp_dir_name)

    def copy_files_to_tmp(self, files):
        for file in files:
            dirna = dirname(file)
            if dirna and not exists(dirna):
                makedirs(dirna)
            copy(file, self.tmp_dir + "/" + file)
            if file.endswith(".sol"):
                code = get_code(self.tmp_dir + "/" + file)
                code = replace_comments_with_whitespace(code)
                write_code(self.tmp_dir + "/" + file, code)
                comment_out_annotations(self.tmp_dir + "/" + file)


    def copy_dir_content_to_tmp(self, dirpath):
        src_files = listdir(dirpath)
        for file_name in src_files:
            full_file_name = join(dirpath, file_name)
            if isfile(full_file_name):
                copy(full_file_name, self.tmp_dir)
                # Todo consider subdirectories and symbolic links

    def provide_resources(self, contracts, address, eth, dynld, sigs, max_depth=50):
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

            # Todo Saving Storage Mapping with mappings in contract might not be necessary
            self.storage_map[contract.name] = extract_storage_map(contract, struct_map)
            contract.storage_map = self.storage_map[contract.name]


            code = get_containing_file(contract).data
            contract_range = find_contract_idx_range(contract)
            contract.contract_range = contract_range
            code = code[contract_range[0]:contract_range[2]]


            augment_with_ast_info(contract)
            for function in contract.functions:
                function.terminating_pos = list(map(lambda pos: (pos[0] - contract_range[0], pos[1]), function.terminating_pos))

            for kw in annotation_kw:
                annot_iterator = finditer(r'/*@' + escape(kw), code)
                annot_iter = next(annot_iterator, None)
                if annot_iter and contract.name not in self.annotation_map:
                    self.annotation_map[contract.name] = []
                while annot_iter:
                    
                    annotation = init_annotation(contract, code, annot_iter.group(), kw, annot_iter.start(), annot_iter.end())
                    if annotation:
                        self.annotation_map[contract.name].append(annotation)
                    annot_iter = next(annot_iterator, None)



    def build_annotated_contracts(self):


        for contract in self.contracts:
            if contract.name not in self.annotation_map:
                continue
            annotations = self.annotation_map[contract.name]
            sol_file = get_containing_file(contract)
            origin_file_code = sol_file.data

            contract_range = find_contract_idx_range(contract)
            origin_contract_code = origin_file_code[contract_range[0]:(contract_range[2] + 1)]

            # Todo Subtract contract offset

            contract_prefix = origin_file_code[:contract_range[0]]
            contract_suffix = origin_file_code[(contract_range[2] + 1):]

            contract_prefix_as_rew = expand_rew(origin_contract_code, (contract_prefix, 0))

            rew_contract_code = origin_contract_code

            rewritings = []

            for annotation in annotations:
                rewritings.extend(annotation.rewrite_code(origin_contract_code, contract_range))

            rewriting_set = []
            for rewriting in rewritings:
                if rewriting not in rewriting_set:
                    rewriting_set.append(rewriting)
            rewritings = rewriting_set

            rewritings = sorted(rewritings, key=lambda rew:(rew.pos, get_sorting_priority(rew.text)))

            for rew_idx in range(len(rewritings)):
                rew = rewritings[rew_idx]
                rew_contract_code = apply_rewriting(rew_contract_code, rew)
                increase_rewritten_pos(rewritings, rewritings[rew_idx], get_newlinetype(origin_file_code))

            increase_rewritten_pos(rewritings, contract_prefix_as_rew, get_newlinetype(origin_file_code))

            rew_file_code = contract_prefix + rew_contract_code + contract_suffix

            # in line should be done for every annotation later
            #printd("----")
            #printd(rew_file_code)
            #printd("----")
            write_code(sol_file.filename, rew_file_code)

            anotation_contract = SolidityContract(sol_file.filename, contract.name, solc_args=self.solc_args)
            augment_with_ast_info(anotation_contract)
            self.annotated_contracts.append(anotation_contract)

            for annotation in self.annotation_map[contract.name]:
                annotation.set_annotation_contract(anotation_contract)

            write_code(sol_file.filename, origin_file_code)



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
        #print("Constructor print")
        #for instr in contr_to_const.disassembly.instruction_list:
        #    ret = get_sourcecode_and_mapping(instr['address'], contr_to_const.disassembly.instruction_list, contract.creation_mappings)
        #    if ret:
        #        code = get_containing_file(contract).data[ret.offset:ret.offset + ret.length].replace('\n', "  ")
        #        print(str(counter) + " " + str(instr) + "       " + code)
        #    else:
        #        print(instr)
        #    counter += 1
        #counter = 0
        #print("Transaction print")
        #for instr in contract.disassembly.instruction_list:
        #    ret = get_sourcecode_and_mapping(instr['address'], contract.disassembly.instruction_list, contract.mappings)
        #    if ret:
        #        code = get_containing_file(contract).data[ret.offset:ret.offset + ret.length].replace('\n', "  ")
        #        print(str(counter) + " " + str(counter) + " " + str(instr) + "       " + code)
        #    else:
        #        print(instr)
        #    counter += 1
        #print()

        # Used to run annotations violation build in traces construction in parallel
        annotationsProcessor = AnnotationProcessor(contract.creation_disassembly.instruction_list,
                                                   contract.disassembly.instruction_list, create_ignore_list, trans_ignore_list, contract)

        # Symbolic execution of construction and transactions
        printd("Constructor and Transaction")

        constr_calldata_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))
        sym_code_extension = SymbolicCodeExtension("calldata", contract.name, constr_calldata_len)

        sym_transactions = SymExecWrapper(contract, self.address, laser_strategy, dynloader, max_depth=self.max_depth,
                                          prepostprocessor=annotationsProcessor, code_extension=sym_code_extension) # Todo Mix the annotation Processors or mix ignore listst
        printd("Construction Violations: " + str(len(reduce(lambda x, y: x + y, annotationsProcessor.create_violations, []))))
        printd("Transaction Violations: " + str(len(reduce(lambda x, y: x + y, annotationsProcessor.trans_violations, []))))

        # Add found violations to the annotations they violated
        # Todo Extract violations from only one symbolic execution
        for ign_idx in range(len(trans_ignore_list)):
            annotation = trans_ignore_list[ign_idx][4]
            mapping = get_sourcecode_and_mapping(trans_ignore_list[ign_idx][2]['address'], contract.disassembly.instruction_list, contract.mappings)
            annotation.set_violations(annotationsProcessor.trans_violations[ign_idx], mapping, contract)

        for ign_idx in range(len(create_ignore_list)):
            annotation = create_ignore_list[ign_idx][4]
            mapping = get_sourcecode_and_mapping(create_ignore_list[ign_idx][2]['address'], contract.creation_disassembly.instruction_list, contract.creation_mappings)
            annotation.set_violations(annotationsProcessor.create_violations[ign_idx], mapping, contract)

        for annotation in self.annotation_map[contract.name]:
            annotation.build_violations(sym_transactions)


        # Build traces from the regular annotation ignoring global states
        # create_traces = get_construction_traces(sym_creation)
        # Todo change traces extraction in a way to use mappings to differentiate between construction and transaction
        create_traces, trans_traces = get_traces(sym_transactions, contract)

        return create_traces, trans_traces

    def build_traces_and_violations(self):
        for contract in self.annotated_contracts:
            const_traces, trans_traces = self.get_traces_and_build_violations(contract)




    def check_annotations(self):

        self.build_annotated_contracts()
        self.build_traces_and_violations()

        # Todo filter violations if the annotation is only broken if it was broken before

        # Todo Set status, perform trace chaining strategy. Update Status

        # Todo Return the annotations with violation information


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

def is_storage_primitive(storage): # Todo If concrete storage gives the value 0 to all unknown lookup values, trace combination has to consider that for the constructor
    if storage:
        for index, content in storage._storage.items():
            if not eq(content, BitVec("storage[" + str(index) + "]", 256)): # Todo See and adapt storage indexing
                return False
    return True

def get_traces(statespace, contract):
    printd("get_traces")
    elim_t_t = 0
    elim_c_t = 0
    trans_traces = []
    constr_traces = []
    state_count = 0
    node_count = 0

    for k in statespace.nodes:
        node_count += 1
        node = statespace.nodes[k]
        for state in node.states:
            state_count += 1
            instruction = state.get_current_instruction()
            # Todo should I ignore certain functions: non public or external functions ???
            if instruction['opcode'] in ["STOP", "RETURN"]:
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):

                    if isinstance(state.current_transaction, ContractCreationTransaction ):
                        istr_list = contract.creation_disassembly.instruction_list
                        mappings = contract.creation_mappings
                    else:
                        istr_list = contract.disassembly.instruction_list
                        mappings = contract.mappings

                    mapping = get_sourcecode_and_mapping(instruction['address'], istr_list, mappings)

                    if mapping:

                        trace = TransactionTrace(state.environment.active_account.storage, state.mstate.constraints, contract)
                        if isinstance(state.current_transaction, ContractCreationTransaction):
                            constr_traces.append(trace)
                        else:
                            trans_traces.append(trace)
                    else:
                        printd("Skipped mapping")
                else:
                    if isinstance(state, ContractCreationTransaction):
                        elim_c_t += 1
                    else:
                        elim_t_t += 1
    printd("Construction traces: " + str(len(constr_traces)) + " eliminated: " + str(elim_c_t))
    printd("Transaction traces: " + str(len(trans_traces)) + " eliminated: " + str(elim_t_t))
    printd("states: " + str(state_count))
    printd("nodes: " + str(node_count))
    return constr_traces, trans_traces

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
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
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

