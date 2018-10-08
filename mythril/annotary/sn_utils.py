import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.ether.soliditycontract import SourceCodeInfo
from z3 import eq, Extract, BitVec

def get_si_from_state(contract, address, state):

    if isinstance(state.current_transaction, ContractCreationTransaction ):
        instruction_list = contract.creation_disassembly.instruction_list
        mappings = contract.creation_mappings
    else:
        instruction_list = contract.disassembly.instruction_list
        mappings = contract.mappings


    index = helper.get_instruction_index(instruction_list, address)

    if index >= len(mappings):
        return None

    solidity_file = contract.solidity_files[mappings[index].solidity_file_idx]

    filename = solidity_file.filename

    offset = mappings[index].offset
    length = mappings[index].length

    code = solidity_file.data[offset:offset + length]
    lineno = mappings[index].lineno

    return SourceCodeInfo(filename, lineno, code), mappings[index]


def get_source_information(contract, instruction_list, mappings, address):

    index = helper.get_instruction_index(instruction_list, address)

    if index >= len(mappings):
        return None

    solidity_file = contract.solidity_files[mappings[index].solidity_file_idx]

    filename = solidity_file.filename

    offset = mappings[index].offset
    length = mappings[index].length

    code = solidity_file.data[offset:offset + length]
    lineno = mappings[index].lineno

    return SourceCodeInfo(filename, lineno, code)

def get_sourcecode_and_mapping(address, instr_list, mappings):
    index = helper.get_instruction_index(instr_list, address)
    if index is not None and len(mappings) > index:
        return mappings[index]
    else:
        return None


def get_named_instruction(instruction_list, opcode):
    instructions = []

    for instr in instruction_list:
        if instr['opcode'] == opcode:
            instructions.append(instr)

    return instructions


def get_named_instructions_with_mappings(instruction_list, mappings, opcode):
    instructions_and_mappings = []

    for instr_idx in range(len(mappings)):
        if instruction_list[instr_idx]['opcode'] == opcode:
            instructions_and_mappings.append((instruction_list[instr_idx], mappings[instr_idx]))

    return instructions_and_mappings


def flatten(list_to_flatten):
    return [item for sublist in list_to_flatten for item in sublist]


def get_function_by_name(contract, name):
    function_list = []
    for function in contract.functions:
        if function.name == name:
            function_list.append(function)
    return function_list

def get_function_by_hash(contract, hash):
    for function in contract.functions:
        if function.hash == hash:
            return function

def get_function_by_inthash(contract, value):
    return get_function_by_hash(contract, value.hash())

def get_function_from_constraints(contract, constraints):
    # Todo first we could search for constraints that could be a restriction to the function hash
    # Todo a calldata length > 4 constraint could be searched for to
    for function in contract.functions:
        function_constraint = Extract(255,224, BitVec("calldata_" + contract.name+ "[0]", 256)) == int(function.hash, 16)
        for constraint in constraints:
            if eq(constraint, function_constraint):
                return function
    return None

