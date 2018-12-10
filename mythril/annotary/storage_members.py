from mythril.annotary.ast_parser import get_all_members_for_contract
from mythril.annotary.codeparser import find_matching_closed_bracket
from functools import reduce
from mythril.annotary.z3utility import are_z3_satisfiable
from z3 import eq, BitVecVal, BitVec, Extract, Not, simplify, is_bv
from mythril.laser.ethereum.util import get_concrete_int
from mythril.laser.ethereum.instructions import keccak_map
from re import finditer

from ethereum import utils
from mythril.laser.ethereum import util
from .z3utility import extract_sym_names, get_bv

type_alias = {"address": "int160", "bool": "int8", "byte": "bytes1", "ufixed": "ufixed128x18", "fixed": "fixed128x18",
              "int": "int256", "uint":"uint256"}

'''
    Copied and modified from laser evm, must have the same behaviour
'''
def get_storage_slot(index, storage):
        try:
            index = get_concrete_int(index)
        except AttributeError:
            index = str(index)

        try:
            data = storage[index]
        except KeyError:
            data = BitVec("storage[" + str(index) + "]", 256)

        return data


class SolidityMember:

    def __init__(self, m_ast):
        attributes = m_ast['attributes']
        self.constant = attributes['constant']
        self.name = attributes['name']
        self.declaring_contract = attributes["declaringContract"]
        self.scope = attributes['scope']
        self.stateVariable = attributes['stateVariable']
        self.storageLocation = attributes['storageLocation']
        self.type = attributes['type']
        self.visibility = attributes['visibility']
        self.src = m_ast['src'].split(':')
        self.src = list(map(lambda x: int(x), self.src))

class StorageSlot:
    # Constraint Slot, irrelevant for ConcretSlot and MappingSlot, important for length constraints on the datatypes
    def may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length):
        raise NotImplementedError("Unimplemented Function of Abstract class")


    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        raise NotImplementedError("Unimplemented Function of Abstract class")

class ConcretSlot(StorageSlot):

    def __init__(self, slot_counter, bit_counter, bitlength):
        self.slot_counter = slot_counter
        self.bit_counter = bit_counter
        self.bitlength = bitlength

    def may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length):
        z3_index = simplify(get_bv(z3_index))
        z3_value = simplify(get_bv(z3_value))

        same_slot = False

        add_constraints = []

        # z3-index directly pointing to this slot
        concret_index = BitVecVal(self.slot_counter, 256)

        # Compare expression equivalence
        if eq(concret_index, z3_index):
            same_slot = True

        # If not structurally equivalent, check if there is an assignment that allows them to be equivalent
        if not same_slot and not are_z3_satisfiable(constraint_list + [z3_index == concret_index]):
            return False, None
        add_constraints.append(simplify(z3_index == self.slot_counter))

        index_str = str(z3_index)
        # Rule out keccak symbolic variable as the function prevents someone from arbitrarily controlling the index

        if len(z3_index.children()) < 2 and index_str.startswith("keccak") \
                or "+" in index_str and index_str[:index_str.index("+")].strip() in keccak_map :
            return False, None # Todo Here I might do something more elaborate if I see that it does actually not solve critical writings

        # Problem because writing to an array has a keccak offset, but if the index can be arbitrarely choosen z3 finds
        # a solution for the controllable symbolic variable to match the index to any slot.
        #sym_ind_name = extract_sym_names(z3_index)
        #if any([name for name in sym_ind_name if name.startswith("keccak")]) and any([name for name in sym_ind_name if not name.startswith("keccak")]):
        #    return False, None

        # If the slot is or may be the same and the slot we currently analyze is the same, we found a possible write
        if self.bitlength == 256:
            return True, add_constraints

        # If not, the slot is still written in its entirety but the observed chunk is loaded and overwritten by itself
        to_bit, from_bit = self.bit_counter + self.bitlength - 1, self.bit_counter
        # to_bit, from_bit = BitVecVal(self.bit_counter + self.bitlength - 1, 256), BitVecVal(self.bit_counter, 256)
        chunk_writing = Extract(to_bit, from_bit, z3_value)

        chunk_content = Extract(to_bit, from_bit,
                                get_bv(get_storage_slot(BitVecVal(self.slot_counter, 256), storage)))

        # if the current content of the observed chunk and the respective chunk of the written value can be different
        # like by a different variable assignment, then we found it
        if are_z3_satisfiable(constraint_list + [Not(chunk_content == chunk_writing)]):
            # It is actually not important to use the constraint that the values are different, overwriting with the same
            # value is still writing. On the other hand it avoids references to storage that later have to be solved with
            # intertransactional analysis although the violation can be triggered in one transaction
            # add_constraints.append(simplify(Not(chunk_content == chunk_writing)))
            return True, add_constraints

        # For the 256-bit chunks the last step should not be necessary, but a compiler could generate some code that
        # overwrites a slot content with itself. This function would have a false positive in that case.

        return False, None


    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class MappingSlot(StorageSlot):

    def __init__(self, slot_counter):
        self.slot_counter = slot_counter

    def may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length):
        # write keccak(...) check if it contains the slot keccak needs the
        z3_index = simplify(z3_index)
        z3_index_str = str(z3_index).replace("\n", "")
        if "keccak(Concat(" in z3_index_str:
            for match in finditer(r'keccak\(Concat\(', z3_index_str ):
                match_str = z3_index_str[match.start():]
                match_str = match_str[len("keccak(Concat("):find_matching_closed_bracket(match_str, len("keccak(Concat"))]
                if not "keccak(" in match_str:
                    if str(match_str).endswith(",_" + str(self.slot_counter)):
                        return True, [] # Found store with unresolved keccak-references

        if z3_index_str in keccak_map:
            unresolved_index = keccak_map[str(z3_index).replace("\n" , "")]
            unresolved_index = str(unresolved_index).replace("\n", "")
            if "Concat(" in unresolved_index:
                for match in finditer(r'Concat\(', unresolved_index):
                    match_str = unresolved_index[match.start():]
                    match_str = match_str[
                                len("Concat("):find_matching_closed_bracket(match_str, len("Concat"))]
                    if not "Concat(" in match_str:
                        if str(match_str).endswith(", " + str(self.slot_counter)):
                            return True, [] # Found store with solved
        return False, []

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class ArraySlot(StorageSlot):

    def __init__(self, slot_counter):
        # Could make a difference between slot and keccak-slot access (length vs. content)
        self.slot_counter = slot_counter
        self.bitlength = 256

    def may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length):
        if consider_length:
            may_write_to, added_constraints = ConcretSlot.may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length)
            if may_write_to:
                return may_write_to, added_constraints

        slot_hash = utils.sha3(utils.bytearray_to_bytestr(util.concrete_int_to_bytes(self.slot_counter)))
        slot_hash = str(BitVecVal(util.concrete_int_from_bytes(slot_hash, 0), 256))


        z3_index_str = str(z3_index).replace("\n", "")
        if z3_index_str.startswith(slot_hash):
            if z3_index_str.endswith(slot_hash) or z3_index_str[len(slot_hash):].startswith(" +"):
                return True, []
        if z3_index_str in keccak_map:
            unresolved_index = keccak_map[str(z3_index).replace("\n" , "")]
            unresolved_index = str(unresolved_index).replace("\n", "")
            if unresolved_index.startswith(str(self.slot_counter)):
                if unresolved_index.endswith(str(self.slot_counter)) or unresolved_index[len(str(self.slot_counter)):].startswith(" +"):
                    return True, []
        return False, []

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass

class BytesSlot(StorageSlot):

    def __init__(self, slot_counter):
        # Even more different than the ArraySlots as the non-keccak slot can contain content and length if the content is short enough.
        self.slot_counter = slot_counter
        self.bitlength = 256

    def may_write_to(self, z3_index, z3_value, storage, constraint_list, consider_length):
        # The representative field also includes content, for this reason it is always considers
        may_write_to, added_constraints = ArraySlot.may_write_to(self, z3_index, z3_value, storage, constraint_list, True)
        return may_write_to, added_constraints

    def may_read_from(self, z3_index, z3_value, storage, constraint_list):
        pass


def extract_storage_map(contract, struct_map):
    storage_members = []
    var_defs = get_all_members_for_contract(contract)
    for var_def in var_defs:
        storage_members.append(SolidityMember(var_def))
    contract.storage_members = storage_members
    storage_map = {}
    slot_counter = 0
    bit_counter = 0
    for member in storage_members:
        m_type = member.type
        m_info, slot_counter, bit_counter = get_storage_mapping_for_types(contract.ast, struct_map, m_type, slot_counter, bit_counter)
        storage_map[member.declaring_contract + "." + member.name] = m_info
        for slot in m_info:
            slot.member = member
    return storage_map


def advance_counters(slot_counter, bit_counter):
    if bit_counter >= 255:
        slot_counter += 1
        bit_counter = 0
    return slot_counter, bit_counter


def add_counters(slot_counter, bit_counter, needed_bits):
    slot_counter += int((bit_counter + needed_bits) / 256)
    bit_counter = bit_counter + needed_bits % 256
    return slot_counter, bit_counter

def get_primitive_storage_mapping(slot_counter, bit_counter, needed_bits):
    mappings = []

    if needed_bits > 256 - bit_counter:
        slot_counter, bit_counter = slot_counter + 1, 0 #advance_counters(slot_counter, bit_counter)

    while needed_bits > 0:

        available_needed = needed_bits if needed_bits <= 256 - bit_counter else (256 - bit_counter)
        needed_bits -= available_needed
        mappings.append(ConcretSlot(slot_counter, bit_counter, available_needed))

    if len(mappings) > 0:
        slot_counter, bit_counter = advance_counters(mappings[-1].slot_counter, mappings[-1].bit_counter + mappings[-1].bitlength)


    return mappings, slot_counter, bit_counter




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
                if bit_counter >= 255:
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
        return m_info, slot_counter, bit_counter
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
        return m_info, slot_counter, bit_counter

    if m_type.startswith("contract"):
        m_type = 'address'
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
        mappings, slot_counter, bit_counter = get_primitive_storage_mapping(slot_counter, bit_counter, post)
        m_info.extend(mappings)
    elif m_type.startswith("bytes"):
        byte_len = m_type[5:]


        mappings, slot_counter, bit_counter = get_primitive_storage_mapping(slot_counter, bit_counter, byte_len * 8)
        m_info.extend(mappings)
    elif True in [m_type.startswith(btype) for btype in ["fixed", "ufixed"]]:
        type_part = m_type[m_type.index("fixed") + 5:]
        type_part = type_part[:type_part.index("x")]


        mappings, slot_counter, bit_counter = get_primitive_storage_mapping(slot_counter, bit_counter, int(type_part))
        m_info.extend(mappings)
    elif m_type.startswith('enum '):
        mappings, slot_counter, bit_counter = get_primitive_storage_mapping(slot_counter, bit_counter, 8)
        m_info.extend(mappings)
    elif m_type.startswith("function "):
        bytes_size = 8 # for default case visibility=internal
        if " external " in m_type:
            bytes_size = 24
        mappings, slot_counter, bit_counter = get_primitive_storage_mapping(slot_counter, bit_counter, bytes_size * 8)
        m_info.extend(mappings)
    else:
        raise SyntaxError("Not treated type")

    return m_info, slot_counter, bit_counter



