from .ast_parser import get_contract_storage_members
from re import search
from .sn_utils import flatten

type_alias = {"address": "int160", "bool": "int8", "byte": "bytes1", "ufixed": "ufixed128x18", "fixed": "fixed128x18",
              "int": "int256", "uint":"uint256"}

class StorageMap:

    def __init__(self):
        self.slots_identifiers = []


def extract_storage_map(contract, struct_map):
    storage_members = get_contract_storage_members(contract.ast)

    member_tuples = []
    slot_counter = 0
    bit_counter = 0
    for member in storage_members:
        m_type = member['type']
        # Todo m_info is used and safed for the var_name in member['name']
        m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract.ast, struct_map, m_type, slot_counter, bit_counter)


def advance_counters(slot_counter, bit_counter):
    if bit_counter != 0:
        slot_counter += 1
        bit_counter = 0
    return slot_counter, bit_counter


def add_counters(slot_counter, bit_counter, needed_bits):
    slot_counter += (bit_counter + needed_bits) / 256
    bit_counter = bit_counter + needed_bits % 256
    return slot_counter, bit_counter


def add_multiple_items_to_counters(slot_counter, bit_counter, bits_p_elem, amount_elements):
    if bit_counter == 0 and 256 % bits_p_elem == 0:
        slot_counter += amount_elements * bits_p_elem / 256
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
    return type_string + flatten(remaining_dim), int(array_strings[-1][1:-1])


def get_storage_mapping_for_types(contract, struct_map, m_type, slot_counter=0, bit_counter=0):
    m_info = []
    if type(m_type) == list:
        for sub_type in m_type:
            nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract, struct_map, sub_type, slot_counter, bit_counter)
            m_info.extend(nested_m_info)
    # slot,list or range of sslots, regular expressions on how slots look, z3-Expressions
    # Todo the order of [] and [c] is important type[c][] is stored differently from type[][c]
    if m_type.endswith("]"):
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter) # Array always start at a new slot
        m_type, dimension = extract_primary_dimension(m_type)

        if dimension == "[]":
            # Todo Return mapping information
            m_info.append((slot_counter, bit_counter, 256))  # slot, bitoffset, bitlength

            slot_counter, bit_counter = slot_counter + 1, 0
            return m_info, slot_counter + 1, 0

        # Todo special case, if we can compute a static size of something int[100], this can be done faster then 100* calculate need of int

        for _ in range(dimension):
            nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract,struct_map, m_type, slot_counter, bit_counter)
            m_info.extend(nested_m_info)
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter)
        return m_info, slot_counter, bit_counter

    if m_type.startswith('mapping('): # Todo this may not be enough as a struct hides this information behind its new struct name
        slot_counter, bit_counter = advance_counters(slot_counter, bit_counter)

        # Todo Generate keccak information as regex or similar for access [Use current slot counter]
        # Todo Additional info using the keccak offsets for storage slots

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
        nested_m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract,struct_map, struct_types, slot_counter, bit_counter)
        m_info.extend(nested_m_info)

    if m_type in type_alias:
        m_type = type_alias[m_type]

    if m_type == "string" or m_type == 'bytes':
        # Todo Generate keccac information
        slot_counter, _ = advance_counters(slot_counter,bit_counter)
        slot_counter += 1
    elif [m_type.startswith(btype) for btype in ["int", "uint"]]:
        pre, post = m_type[:m_type.find("t")+1], m_type[m_type.find("t")+1:]
        if post == '':
            post = "256"
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, post)
    elif m_type.starswith("bytes"):
        byte_len = m_type[5:]
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, byte_len * 8)
    elif [m_type.startswith(btype) for btype in ["fixed", "ufixed"]]:
        type_part = m_type[m_type.index("fixed") + 5:]
        type_part = type_part[:type_part.index("x")]
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, int(type_part))
    if m_type.startswith('enum '):
        slot_counter, bit_counter = add_counters(slot_counter, bit_counter, 8) # Should be always 8 unless there is some weird enum
    # Todo function types





    return m_info, slot_counter, bit_counter



