import logging
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.solidnotary.z3utility import are_z3_satisfiable
from mythril.analysis.symbolic import SymExecWrapper
from mythril.support.loader import DynLoader
from mythril.ether.soliditycontract import SolidityContract
from mythril.disassembler.disassembly import Disassembly
from mythril.solidnotary.calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi
from mythril.solidnotary.coderewriter import write_code, get_code, \
    replace_comments_with_whitespace, apply_rewriting, get_editor_indexed_rewriting
from .codeparser import find_matching_closed_bracket, newlines, get_newlinetype
from mythril.solidnotary.annotation import annotation_kw, init_annotation, increase_rewritten_pos, comment_out_annotations, expand_rew
from z3 import BitVec,eq
from os.path import exists, isdir, dirname, isfile, join
from os import makedirs, chdir, listdir, getcwd
from re import finditer, escape
from mythril.laser.ethereum.svm import GlobalState, Account, Environment, CalldataType
from mythril.laser.ethereum.state import MachineState
from shutil import rmtree, copy
from re import findall, sub
from copy import deepcopy

project_name = "solidnotary"

tmp_dir_name = project_name + "_tmp"

laser_strategy = "dfs"

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

def find_contract_idx_range(contract):
    containing_file = get_containing_file(contract)
    contract_idx = next(finditer(r'contract\s*' + escape(contract.name) + r'\s*{', containing_file.data), None)

    start_head = contract_idx.start()
    end_head = contract_idx.end() - 1
    end_contract = find_matching_closed_bracket(containing_file.data, end_head)
    return start_head, end_head, end_contract




# Todo search for next ; or ...) in the inverse string, exclude content of multiline- and line of linecomments



def get_containing_file(contract):
    contract_name = contract.name
    containing_file = None
    for sol_file in contract.solidity_files:
        contract_idx = next(finditer(r'contract\s*' + escape(contract_name) + r'\s*{', sol_file.data), None)
        if contract_idx:
            containing_file = sol_file
            break
    return containing_file


"""
    Here it might be better to split annotations into the containing constraint an the prefix and sufix
"""


def parse_annotation_info(filedata):
    annotations = []
    for inv in findall(r'//@invariant\<([^\)]+)\>;(\r\n|\r|\n)', filedata):
        match_inv = "//@invariant<" + inv[0] + ">;"
        for pos in find_all(filedata, match_inv + inv[1]):
            line = count_elements(filedata[:pos], newlines) + 1
            col = pos - max(map(lambda x: filedata[:pos].rfind(x), newlines))
            annotations.append((pos, line, col, '//invariant(', inv[0], ")", inv[1]))
    return set(annotations)

def parse_annotation_info(code):
    annotations = []
    for kw in annotation_kw:
        annot_iterator = finditer(r'//@' + escape(kw), code)
        annot_iter = next(annot_iterator, None)
        while annot_iter:
            annotation = init_annotation(code, annot_iter.group(), kw, annot_iter.start(), annot_iter.end())
            annotations.append(annotation)
            annot_iter = next(annot_iterator, None)


def read_write_file(filename):
    with open(filename, 'r') as file:
        filedata = file.read()

    annotations = parse_annotation_info(filedata)

    annotations = sorted(list(annotations), key=lambda x: x[0], reverse=True)
    for annotation in annotations:
        filedata = replace_index(filedata, annotation[3] + annotation[4] + annotation[5] + annotation[6], "assert("
                                 + annotation[4] + ");" + annotation[6], annotation[0])
    # Replace the target string
    # filedata = filedata.replace('@ensure', '@invariant')
    # filedata = filedata.replace('@invariant', '@ensure')

    with open(filename, 'w') as file:
        file.write(filedata)
    return annotations

class SolidNotary:

    def __init__(self, solc_args):
        # Todo Parse Annotations and store them in an additional structure
        # Todo receive a list of files or a file, these are modified for the analysis
        self.solc_args = solc_args

        self.wd = getcwd()
        self.tmp_dir = None
        self.annotation_map = {}
        self.annotated_contracts = []

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

    def provide_resources(self, contracts, address, eth, dynld, max_depth):
        self.contracts = contracts
        self.address = address
        self.eth = eth
        self.dynld = dynld
        self.max_depth = max_depth

    def get_lineno_stop_inst(self):
        pass


    def parse_annotations(self):
        # Todo from which contract to parse?
        for contract in self.contracts:

            code = get_containing_file(contract).data
            contract_range = find_contract_idx_range(contract)
            code = code[contract_range[0]:contract_range[2]]

            for kw in annotation_kw:
                annot_iterator = finditer(r'//@' + escape(kw), code)
                annot_iter = next(annot_iterator, None)
                if annot_iter and contract.name not in self.annotation_map:
                    self.annotation_map[contract.name] = []
                while annot_iter:
                    annotation = init_annotation(code, annot_iter.group(), kw, annot_iter.start(), annot_iter.end())

                    self.annotation_map[contract.name].append(annotation)
                    annot_iter = next(annot_iterator, None)
        print("I need code to place my breakpoints")

    def get_ignore_instructions(self, code, annotations):
        # Todo compute the instructions whos state changes should not have a influence on the other instructions
        # instruction 'address' or 'index' and "A RESET FLAG" to allow for annotations to ignore each other.
        return []

    def build_annotated_contracts(self):
        for contract in self.contracts:
            annotations = self.annotation_map[contract.name]
            sol_file = get_containing_file(contract)
            origin_file_code = sol_file.data

            contract_range = find_contract_idx_range(contract)
            origin_contract_code = origin_file_code[contract_range[0]:(contract_range[2] + 1)]
            contract_prefix = origin_file_code[:contract_range[0]]
            contract_suffix = origin_file_code[(contract_range[2] + 1):]

            contract_prefix_as_rew = expand_rew(origin_contract_code, (contract_prefix, 0))

            rew_contract_code = origin_contract_code
            # Todo Maybe I should first collect all rewritings and eliminate those that are the same, or just read in a file and eliminate implicit blocks

            rewritings = []

            for annotation in annotations:
                rewritings.extend(annotation.rewrite_code(rew_contract_code,
                                                          contract_range))  # Todo only reqrite the code, and remember line where the associated symbolic execution things lie

            for rew_idx in range(len(rewritings)):
                rew_contract_code = apply_rewriting(rew_contract_code, rewritings[rew_idx])
                increase_rewritten_pos(rewritings, rewritings[rew_idx], get_newlinetype(origin_file_code))

            increase_rewritten_pos(rewritings, contract_prefix_as_rew, get_newlinetype(origin_file_code))

            rew_file_code = contract_prefix + rew_contract_code + contract_suffix

            # Todo Properly call and integrate the rewriting, annotations are ordered by position, so updating their location
            # in line should be done for every annotation later
            print("----")
            print(rew_file_code)
            print("----")
            write_code(sol_file.filename, rew_file_code)

            # build a new contract object by the constructor
            # Use that object to build sym_...
            # Call annotation methods with check_functions
            # Todo Build this contracts annotation modified version
            self.annotated_contracts.append(SolidityContract(sol_file.filename, contract.name, solc_args=self.solc_args))

            write_code(sol_file.filename, origin_file_code)

    def get_regular_traces(self, contract):
        contr_to_const = deepcopy(contract)
        contr_to_const.disassembly = Disassembly(contr_to_const.creation_code)
        contr_to_const.code = contr_to_const.creation_code
        dynloader = DynLoader(self.eth) if self.dynld else None
        glbstate = get_constr_glbstate(contr_to_const, self.address)

#        for inst_idx in range(len(contract.disassembly.instruction_list)):
#            instruction = contract.disassembly.instruction_list[inst_idx]
#            mapping = contract.mappings[inst_idx]
#            sc_info = contract.get_source_info(instruction['address'])
#            print(str(instruction['address']) + " " + instruction['opcode'] + " ( " + str(mapping.length) + ", " + str(mapping.lineno)
#                  + ", " + str(mapping.offset) + " )")
#            print(sc_info.code)
#            print()

        constr_annotation_ignore_instructions = self.get_ignore_instructions(contr_to_const.disassembly, self.annotation_map[contr_to_const.name])
        runtime_annotation_ignore_instructions = self.get_ignore_instructions(contract.disassembly, self.annotation_map[contr_to_const.name])


        sym_constructor = SymExecWrapper(contr_to_const, self.address, laser_strategy, dynloader, self.max_depth, glbstate=glbstate)
        print()
        sym_contract = SymExecWrapper(contract, self.address, laser_strategy, dynloader, max_depth=self.max_depth)

        constructor_traces = get_construction_traces(sym_constructor)

        traces = get_transaction_traces(sym_contract)
        return constructor_traces, traces

    def get_annotation_traces(self):
        for contract in self.annotated_contracts:
            for annotation in self.annotation_map[contract.name]:
                for c_v_rewriting in annotation.violation_rew:
                    v_rewriting = get_editor_indexed_rewriting(c_v_rewriting)
                    rew_asm = []
                    for m_idx in range(len(contract.mappings)):
                        mapping = contract.mappings[m_idx]
                        if mapping.lineno == v_rewriting.line:
                            if mapping.offset >= v_rewriting.pos:
                                if mapping.length <= len(v_rewriting.text):
                                    print(str(mapping.lineno) + " " + str(mapping.offset) + " " + str(mapping.length) + " " + contract.disassembly.instruction_list[m_idx]['opcode'])
                    for c_mapping in contract.creation_mappings:
                        if c_mapping.lineno == v_rewriting.line and c_mapping.offset >= v_rewriting.pos and c_mapping.length <= len(v_rewriting.text):
                            print(str(c_mapping.lineno) + " " + str(c_mapping.offset) + " " + str(c_mapping.length))



    def check_annotations(self):

        self.build_annotated_contracts()
        self.get_annotation_traces()
        # Todo for both modes build ignore lists
        # Todo for every contract build both sym-exe
        

        logging.debug("Executing annotations check")

        for contract in self.contracts:

            # self.get_annotation_traces(contract)
            print()


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
        for index, content in storage.items():
            if not eq(content, BitVec("storage_" + str(index), 256)):
                return False
    return True

def get_transaction_traces(statespace):
    print("get_transaction_traces")
    num_elimi_traces= 0
    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode'] == "STOP":
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
                else:
                    num_elimi_traces += 1
    print("Transaction traces: " + str(len(traces)) + " eliminated: " + str(num_elimi_traces))
    return traces

def get_construction_traces(statespace):
    print("get_constructor_traces")
    num_elimi_traces= 0
    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode'] == "RETURN":
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
                else:
                    num_elimi_traces += 1
    print("Construction traces: " + str(len(traces)) + " eliminated: " + str(num_elimi_traces))
    return traces

def get_constr_glbstate(contract, address):

    mstate = MachineState(gas=10000000)

    minimal_const_byte_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))

    # better would be to append symbolic params to the bytecode such that the codecopy instruction that copies the
    # params into memory takes care of placing them onto the memory with the respective size.
    for i in range(int(minimal_const_byte_len / 32)):
        mstate.mem_extend(128 + 32 * i, 32)
        mstate.memory.insert(128 + 32 * i, BitVec('calldata_' + contract.name + '_' + str(i * 32), 256))

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

