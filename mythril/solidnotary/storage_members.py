from .ast_parser import get_contract_storage_members
from functools import reduce

type_alias = {"address": "int160", "bool": "int8", "byte": "bytes1", "ufixed": "ufixed128x18", "fixed": "fixed128x18",
              "int": "int256", "uint":"uint256"}


class SolidityMember:

    def __init__(self, m_ast):
        attributes = m_ast['attributes']
        self.constant = attributes['constant']
        self.name = attributes['name']
        self.scope = attributes['scope']
        self.stateVariable = attributes['stateVariable']
        self.storageLocation = attributes['storageLocation']
        self.type = attributes['type']
        self.visibility = attributes['visibility']
        self.src = m_ast['src'].split(':')
        self.src = list(map(lambda x: int(x), self.src))

class StorageSlot:
    # Constraint Slot, irrelevant for ConcretSlot and MappingSlot, important for length constraints on the datatypes
    def may_write_to(self, z3_index, z3_value, storage, constraint_list):
        raise NotImplementedError("Unimplemented Function of Abstract class")

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        raise NotImplementedError("Unimplemented Function of Abstract class")

class ConcretSlot(StorageSlot):

    def __init__(self, slot_counter, bit_counter, bitlength):
        self.slot_counter = slot_counter
        self.bit_counter = bit_counter
        self.bitlength = bitlength

    def may_write_to(self, z3_index, z3_value, storage, constraint_list):
        pass

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class MappingSlot(StorageSlot):

    def __init__(self, slot_counter):
        self.slot_counter = slot_counter

    def may_write_to(self, z3_index, z3_value, storage, constraint_list):
        pass

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class ArraySlot(StorageSlot):

    def __init__(self, slot_counter):
        # Could make a difference between slot and keccak-slot access (length vs. content)
        self.slot_counter = slot_counter

    def may_write_to(self, z3_index, z3_value, storage, constraint_list):
        pass

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class BytesSlot(StorageSlot):

    def __init__(self, slot_counter):
        # Even more different than the ArraySlots as the non-keccak slot can contain content and length if the content is short enough.
        self.slot_counter = slot_counter

    def may_write_to(self, z3_index, z3_value, storage, constraint_list):
        pass

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass


def extract_storage_map(contract, struct_map):
    storage_members = []
    var_defs = get_contract_storage_members(contract.ast)
    for var_def in var_defs:
        storage_members.append(SolidityMember(var_def))
    contract.storage_members = storage_members

    # Todo attention there is a field 'stateVariable' this might me false for some case, also look for "storageLocation"
    # Todo Maybe these have to be filtered out

    storage_map = {}
    slot_counter = 0
    bit_counter = 0
    for member in storage_members:
        m_type = member.type
        m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract.ast, struct_map, m_type, slot_counter, bit_counter)
        storage_map[member.name] = m_info
    return storage_map


def advance_counters(slot_counter, bit_counter):
    if bit_counter != 0:
        slot_counter += 1
        bit_counter = 0
    return slot_counter, bit_counter


def add_counters(slot_counter, bit_counter, needed_bits):
    slot_counter += int((bit_counter + needed_bits) / 256)
    bit_counter = bit_counter + needed_bits % 256
    return slot_counter, bit_counter

def get_primitive_storage_mapping(slot_counter, bit_counter, needed_bits):
    mappings = []
    while needed_bits > 0:
        if bit_counter == 0:
            slot_counter -= 1
            bit_counter = 256
        available_needed = needed_bits if needed_bits < bit_counter else (bit_counter)
        needed_bits -= available_needed
        mappings.append(ConcretSlot(slot_counter, bit_counter - available_needed, available_needed))
    return mappings




def add_multiple_items_to_counters(slot_counter, bit_counter, bits_p_elem, amount_elements):
    if bit_counter == 0 and 256 % bits_p_elem == 0:
        slot_counter += int(amount_elements * bits_p_elem / 256)
        bit_counter = amount_elements * bits_p_elem % 256
    else:
        while amount_elements > 0:
            if 256 - bit_counter < bits_p_elem:
                slot_counter += 1
                bit_counter = 0
                continue
            else:
                bit_counter += bits_p_elem
                amount_elements -= 1
                if bit_counter == 256:
                    slot_counter += 1
                    bit_counter = 0
    return slot_counter, bit_counter


def get_arrays(type_string):
    array_strings = []
    while type_string.endswith("]"):
        array_strings.append(type_string[type_string.rfind("["):])
        type_string = type_string[:type_string.rfind("[")]
    return type_string, array_strings


def extract_primary_dimension(type_string):
    type_string, array_strings = get_arrays(type_string)
    remaining_dim = array_strings[:-1][::-1]
    return type_string + reduce(lambda x, y: x + y, remaining_dim, ""), array_strings[-1]


def get_storage_mapping_for_types(contract, struct_map, m_type, slot_counter=0, bit_counter=0):
    m_info = []
    if type(m_type) == list:
        for sub_type in m_type:
            nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract, struct_map, sub_type, slot_counter, bit_counter)
            m_info.extend(nested_m_info)
        return m_info, slot_counter, bit_counter
    # slot,list or range of sslots, regular expressions on how slots look, z3-Expressions
    if m_type.endswith("]"):
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter) # Array always start at a new slot
        m_type, dimension = extract_primary_dimension(m_type)

        if dimension == "[]":
            # m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, 256))  # slot, bitoffset, bitlength
            m_info.append(ArraySlot(slot_counter))

            return m_info, slot_counter + 1, 0

        dimension = int(dimension[1:-1])

        # Todo special case, if we can compute a static size of something int[100], this can be done faster then 100* calculate need of int

        for _ in range(dimension):
            nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract,struct_map, m_type, slot_counter, bit_counter)
            m_info.extend(nested_m_info)
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter)
        return m_info, slot_counter, bit_counter

    if m_type.startswith('mapping('):
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter)

        # Advancing is good, but for mappings the slot is empty and neither reads nor writes have meaning
        # m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, 256))  # slot, bitoffset, bitlength

        m_info.append(MappingSlot(slot_counter))

        slot_counter += 1
        bit_counter = 0
    if m_type.startswith('struct '):
        struct_abs_name = m_type[len('struct '):]
        try:
            struct_types = struct_map[struct_abs_name]
        except KeyError:
            raise SyntaxError("Unknown struct that cannot be resolved: " + struct_abs_name)
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter)
        # Todo here we should inspect if struct_types have the expected format: list of types
        nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract, struct_map, struct_types, slot_counter, bit_counter)
        m_info.extend(nested_m_info)

    if m_type in type_alias:
        m_type = type_alias[m_type]

    if m_type == "string" or m_type == 'bytes':
        slot_counter, _ = advance_counters(slot_counter,bit_counter)

        m_info.append(BytesSlot(slot_counter))
        # m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, 256))  # slot, bitoffset, bitlength

        slot_counter += 1
    elif True in [m_type.startswith(btype) for btype in ["int", "uint"]]:
        pre, post = m_type[:m_type.find("t")+1], m_type[m_type.find("t")+1:]
        if post == '':
            post = "256"
        post = int(post)
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, post)
        m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, post))
    elif m_type.startswith("bytes"):
        byte_len = m_type[5:]
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, byte_len * 8)
        m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, byte_len * 8))
    elif True in [m_type.startswith(btype) for btype in ["fixed", "ufixed"]]:
        type_part = m_type[m_type.index("fixed") + 5:]
        type_part = type_part[:type_part.index("x")]
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, int(type_part))
        m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, int(type_part)))
    elif m_type.startswith('enum '):
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, 8) # Should be always 8 unless there is some weird enum
        m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, 8))
    elif m_type.startswith("function "):
        bytes_size = 8 # for default case visibility=internal
        if " external " in m_type:
            bytes_size = 24
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, bytes_size * 8)
        m_info.extend(get_primitive_storage_mapping(slot_counter, bit_counter, bytes_size * 8))

    return m_info, slot_counter, bit_counter



