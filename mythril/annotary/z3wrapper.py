from mythril.annotary.z3utility import extract_sym_names, filter_for_t_variable_data
from z3 import substitute, BitVec, simplify
from mythril.annotary.sn_utils import flatten

optimized = True


class Constraint:
    """
    Layer around Z3 bitvector expressions with meta information to depict path and transaction constraints. The
    metainformation helps to later perform expression substitution when chaining transactions.
    """

    def __init__(self, constraint):
        self.constraint = constraint
        # symbolic names of used storage references.
        self.slot_names = []
        # symbolic names of transaction variables
        self.tran_names = []
        self.extract_names()

    def simplify(self):
        """
        Simplifies the contained Z3 constraints and extracts the symbolic names.
        """
        self.constraint = simplify(self.constraint)
        self.extract_names()

    def extract_names(self):
        """
        Extracts symbolic variables from the z3 constraints and splits them into slot references and transaction
        dependent variables.
        """
        sym_names = extract_sym_names(self.constraint)
        self.slot_names = list(filter(lambda name: name.startswith("storage"), sym_names))  # For substitution
        self.tran_names = filter_for_t_variable_data(sym_names)  # For depth increment

    def substitute(self, subs_map):
        """
        Performs expression substitution on the constraint terms with the given substitution list.
        :param subs_map: A list of substitution tuples containing (var_to_substitute, expression_to_inser,
        tuple_of_tran_slot_names).
        """
        # Only the substitutions are used for which vars are contained in the constraint.
        if optimized:
            filtered_sub_map = [subs for subs in subs_map if subs[0] in self.tran_names or subs[0] in self.slot_names]
        else:
            filtered_sub_map = subs_map
        # Only call Z3 substitution if necessary
        if filtered_sub_map:
            self.constraint = substitute(self.constraint, [(BitVec(subs[0], 256), subs[1]) for subs in filtered_sub_map])
            # Updating the in the constraint contained storage slot and tran name references
            filtered_names = [sub[0] for sub in filtered_sub_map]
            self.tran_names = [name for name in self.tran_names if name not in filtered_names]
            self.slot_names = [name for name in self.slot_names if name not in filtered_names]
            self.tran_names.extend(flatten([sub[2][0] for sub in filtered_sub_map]))
            self.slot_names.extend(flatten([sub[2][1] for sub in filtered_sub_map]))


class Slot:
    """
    Layer around Z3 bitvector expressions with meta information to depict the content of a storage slot. The
    metainformation helps to later perform expression substitution when chaining transactions.
    """

    def __init__(self, name, slot):
        self.name = name
        self.slot = slot
        sym_names = extract_sym_names(self.slot)
        # symbolic names of used storage references.
        self.slot_names = list(filter(lambda sym_name: sym_name.startswith("storage"), sym_names))
        # symbolic names of transaction variables
        self.tran_names = filter_for_t_variable_data(sym_names)

    def extract_names(self):
        """
        Extracts symbolic variables from the z3 constraints and splits them into slot references and transaction
        dependent variables.
        """
        sym_names = extract_sym_names(self.slot)
        self.slot_names = list(filter(lambda name: name.startswith("storage"), sym_names))  # For substitution
        self.tran_names = filter_for_t_variable_data(sym_names)  # For depth increment

    def simplify(self):
        """
        Simplifies the Z3 storage slot content and extracts the symbolic names.
        """
        self.slot = simplify(self.slot)
        self.extract_names()

    def substitute(self, subs_map):
        """
        Performs expression substitution on the slot value with the given substitution list.
        :param subs_map: A list of substitution tuples containing (var_to_substitute, expression_to_inser,
        tuple_of_tran_slot_names).
        """
        # Only the substitutions are used for which vars are contained in the slot value.
        if optimized:
            filtered_sub_map = [subs for subs in subs_map if subs[0] in self.tran_names or subs[0] in self.slot_names]
        else:
            filtered_sub_map = subs_map
        # Only call Z3 substitution if necessary
        if filtered_sub_map:
            self.slot = substitute(self.slot, [(BitVec(subs[0], 256), subs[1]) for subs in filtered_sub_map])
            # Updating the in the constraint contained storage slot and tran name references
            filtered_names = [sub[0] for sub in filtered_sub_map]
            self.tran_names = [name for name in self.tran_names if name not in filtered_names]
            self.slot_names = [name for name in self.slot_names if name not in filtered_names]
            self.tran_names.extend(flatten([sub[2][0] for sub in filtered_sub_map]))
            self.slot_names.extend(flatten([sub[2][1] for sub in filtered_sub_map]))

