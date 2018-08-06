import logging
from mythril.solidnotary.transactiontrace import TransactionTrace
from mythril.solidnotary.z3utility import are_z3_satisfiable
from mythril.analysis.symbolic import SymExecWrapper
from mythril.support.loader import DynLoader
from mythril.ether.soliditycontract import SolidityContract, SourceCodeInfo
from mythril.disassembler.disassembly import Disassembly
from mythril.solidnotary.calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi
from mythril.solidnotary.coderewriter import write_code, get_code, \
    replace_comments_with_whitespace, apply_rewriting
from .codeparser import find_matching_closed_bracket, newlines, get_newlinetype
from .stateprocessing import AnnotationProcessor
import mythril.laser.ethereum.util as helper
from mythril.solidnotary.annotation import annotation_kw, init_annotation, increase_rewritten_pos, comment_out_annotations, expand_rew
from z3 import BitVec,eq
from os.path import exists, isdir, dirname, isfile, join
from os import makedirs, chdir, listdir, getcwd
from re import finditer, escape
from mythril.laser.ethereum.svm import GlobalState, Account, Environment, CalldataType
from mythril.laser.ethereum.state import MachineState
from shutil import rmtree, copy
from re import findall, sub, DOTALL
from copy import deepcopy

project_name = "solidnotary"

tmp_dir_name = project_name + "_tmp"

laser_strategy = "dfs"

class SolidityFunction:

    def __init__(self, f_def):
        attributes = f_def['attributes']

        self.constant = attributes['constant']
        self.implemented = attributes['implemented']
        self.modifiers = attributes['modifiers']
        self.payable =  attributes['payable']
        self.stateMutability = attributes['stateMutability']
        self.visibility = attributes['visibility']
        self.name = attributes['name']
        self.isConstructor = attributes['isConstructor']

        self.terminating_pos = []
        returns = get_all_nested_dicts_with_kv_pairs(f_def, "name", "Return")
        for ret in returns:
            pos_r = ret['src'].split(':')
            self.terminating_pos.append((int(pos_r[0]), int(pos_r[1])))
        self.return_types = []
        if returns:
            ret_param_id = returns[0]['attributes']['functionReturnParameters']

            return_params = get_all_nested_dicts_with_kv_pairs(f_def, 'id', ret_param_id)[0]

            for child in return_params['children']:
                if child['attributes']['type']:
                    self.return_types.append(child['attributes']['type'])

        pos = f_def['src'].split(':')
        if not is_last_stmt_a_return(f_def):
            self.terminating_pos.append((int(pos[0]) + int(pos[1]) - 1, 0))


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

def get_sourcecode_and_mapping(address, instr_list, mappings):
    index = helper.get_instruction_index(instr_list, address)
    return mappings[index]



def get_containing_file(contract):
    contract_name = contract.name
    containing_file = None
    for sol_file in contract.solidity_files:
        contract_idx = next(finditer(r'contract\s*' + escape(contract_name) + r'(.*?){', sol_file.data, flags=DOTALL), None)
        if contract_idx:
            containing_file = sol_file
            break
    return containing_file

def get_last_child(obj):
    if type(obj) == dict:
        return obj['children'][-1]
    raise RuntimeError("No children to retrieve the last one")

def is_last_stmt_a_return(f_def):
    block = None
    for child in f_def['children']:
        if 'name' in child and child['name'] == 'Block':
            block = child
    if not block:
        raise RuntimeError("Function has no block in ast")
    last_child = get_last_child(block)
    return last_child['name'] == 'Return'


def get_containing_kv_pairs(obj, key):
    pairs = []
    if type(obj) == dict:
        if key in obj:
            pairs.extend((key, obj[key]))
        for k,v in obj.items():
            pairs.extend(get_containing_kv_pairs(v, key))
    elif type(obj) == list:
        for elem in obj:
            pairs.extend(get_containing_kv_pairs(elem, key))
    return pairs

"""
    If dictionary with specified key, value pair can contain a dict with the key, value pair this nested dict is 
    returned to. Removing the specified line avoids this
"""
def get_all_nested_dicts_with_kv_pairs(obj, key, value):
    dicts = []
    if type(obj) == dict:
        for k, v in obj.items():
            if k == key and v == value:
                dicts.append(obj)
            dicts.extend(get_all_nested_dicts_with_kv_pairs(v, key, value))
    elif type(obj) == list:
        for elem in obj:
            dicts.extend(get_all_nested_dicts_with_kv_pairs(elem, key, value))
    return dicts

"""
    Parses the ast to find all positions where a contract might terminate with a transactions execution.
"""
def augment_with_functions(contract):
    contract.functions = []
    contract_file = get_containing_file(contract)
    ast = contract_file.ast
    contract_asts = get_all_nested_dicts_with_kv_pairs(ast, "name", "ContractDefinition")
    contract_ast = list(filter(lambda c_ast: c_ast['attributes']['name'] == contract.name, contract_asts))[0]
    f_defs = get_all_nested_dicts_with_kv_pairs(contract_ast, "name", "FunctionDefinition")
    for f_def in f_defs:
        contract.functions.append(SolidityFunction(f_def))


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
    print(contract_code)
    return contract_code
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


            augment_with_functions(contract)
            for function in contract.functions:
                function.terminating_pos = list(map(lambda pos: (pos[0] - contract_range[0], pos[1]), function.terminating_pos))

            for kw in annotation_kw:
                annot_iterator = finditer(r'//@' + escape(kw), code)
                annot_iter = next(annot_iterator, None)
                if annot_iter and contract.name not in self.annotation_map:
                    self.annotation_map[contract.name] = []
                while annot_iter:
                    annotation = init_annotation(contract, code, annot_iter.group(), kw, annot_iter.start(), annot_iter.end())

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
            print("----")
            print(rew_file_code)
            print("----")
            write_code(sol_file.filename, rew_file_code)

            anotation_contract = SolidityContract(sol_file.filename, contract.name, solc_args=self.solc_args)
            self.annotated_contracts.append(anotation_contract)

            for annotation in self.annotation_map[contract.name]:
                annotation.set_annotation_contract(anotation_contract)

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

        create_ignore_list = []
        trans_ignore_list = []

        for annotation in self.annotation_map[contract.name]:
            create_ignore_list.extend(annotation.get_creation_ignore_list())
            trans_ignore_list.extend(annotation.get_trans_ignore_list())

        create_annotationsProcessor = AnnotationProcessor(contr_to_const.disassembly.instruction_list, create_ignore_list)
        trans_annotationsProcessor = AnnotationProcessor(contract.disassembly.instruction_list, trans_ignore_list)

        # Symbolic execution of construction and transactions
        sym_creation = SymExecWrapper(contr_to_const, self.address, laser_strategy, dynloader, self.max_depth,
                                         glbstate=glbstate, prepostprocessor=create_annotationsProcessor)
        sym_transactions = SymExecWrapper(contract, self.address, laser_strategy, dynloader, max_depth=self.max_depth,
                                          prepostprocessor=trans_annotationsProcessor)

        for ign_idx in range(len(trans_ignore_list)):
            annotation = trans_ignore_list[ign_idx][4]
            mapping = get_sourcecode_and_mapping(trans_ignore_list[ign_idx][2]['address'], contract.disassembly.instruction_list, contract.mappings)
            annotation.set_violations(trans_annotationsProcessor.violations[ign_idx], mapping)

        for ign_idx in range(len(create_ignore_list)):
            annotation = create_ignore_list[ign_idx][4]
            mapping = get_sourcecode_and_mapping(create_ignore_list[ign_idx][2]['address'], contract.creation_disassembly.instruction_list, contract.creation_mappings)
            annotation.set_violations(create_annotationsProcessor.violations[ign_idx], mapping)


        # Building of traces
        create_traces = get_construction_traces(sym_creation)
        trans_traces = get_transaction_traces(sym_transactions)

        # Set violations to annotations

        # violations = get_violations(sym_constructor, sym_transactions)
        return create_traces, trans_traces

    def get_annotation_traces(self):
        for contract in self.annotated_contracts:
            const_traces, trans_traces = self.get_regular_traces(contract)




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
    state_count = 0
    node_count = 0

    for k in statespace.nodes:
        node_count += 1
        node = statespace.nodes[k]
        for state in node.states:
            state_count += 1
            instruction = state.get_current_instruction()
            if instruction['opcode'] in ["STOP", "RETURN"]:
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
                else:
                    num_elimi_traces += 1
    print("Transaction traces: " + str(len(traces)) + " eliminated: " + str(num_elimi_traces))
    print("states: " + str(state_count))
    print("nodes: " + str(node_count))
    return traces

def get_construction_traces(statespace):
    print("get_constructor_traces")
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

