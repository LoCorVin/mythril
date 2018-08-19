import mythril.laser.ethereum.util as helper
from mythril.ether.soliditycontract import SourceCodeInfo


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



