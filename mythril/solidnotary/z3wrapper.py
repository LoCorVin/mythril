from mythril.solidnotary.z3utility import extract_sym_names, filter_for_t_variable_data
from z3 import substitute, BitVec, simplify
from .sn_utils import flatten

optimized = True

class Constraint:

    def __init__(self, constraint):
        self.constraint = constraint
        self.extract_names()

    def simplify(self):
        self.constraint = simplify(self.constraint)
        self.extract_names()

    def extract_names(self):
        self.sym_names = extract_sym_names(self.constraint)
        self.slot_names = list(filter(lambda name: name.startswith("storage"), self.sym_names))  # For substitution
        self.sym_names = filter_for_t_variable_data(self.sym_names)  # For depth increment

        #    def add_transaction_idx(self): # This can be done in one substitution for storage slots and depth increment
        #        pass

    def substitute(self, subs_map):
        if optimized:
            filtered_sub_map = [subs for subs in subs_map if subs[0] in self.sym_names or subs[0] in self.slot_names]
        else:
            filtered_sub_map = subs_map
        if filtered_sub_map:  # call substitute only if something is to substitute
            self.constraint = substitute(self.constraint, [(BitVec(subs[0], 256), subs[1]) for subs in filtered_sub_map])
            # Updating names
            filtered_names = [sub[0] for sub in filtered_sub_map]
            self.sym_names = [name for name in self.sym_names if name not in filtered_names]
            self.slot_names = [name for name in self.slot_names if name not in filtered_names]
            self.sym_names.extend(flatten([sub[2][0] for sub in filtered_sub_map]))
            self.slot_names.extend(flatten([sub[2][1] for sub in filtered_sub_map]))

class Slot:

    def __init__(self, name, slot):
        self.name = name
        self.slot = slot

        self.sym_names = extract_sym_names(self.slot)

        self.slot_names = list(filter(lambda name: name.startswith("storage"), self.sym_names)) # For substitution
        self.sym_names = filter_for_t_variable_data(self.sym_names) # For depth increment

    def simplify(self):
        self.slot = simplify(self.slot)

#    def add_transaction_idx(self): # This can be done in one substitution for storage slots and depth increment
#        pass

    def substitute(self, subs_map):
        if optimized:
            filtered_sub_map = [subs for subs in subs_map if subs[0] in self.sym_names or subs[0] in self.slot_names]
        else:
            filtered_sub_map = subs_map
        if filtered_sub_map: # call substitute only if something is to substitute
            self.slot = substitute(self.slot, [(BitVec(subs[0], 256), subs[1]) for subs in filtered_sub_map ])
            # Updating names
            filtered_names = [sub[0] for sub in filtered_sub_map]
            self.sym_names = [name for name in self.sym_names if name not in filtered_names]
            self.slot_names = [name for name in self.slot_names if name not in filtered_names]
            self.sym_names.extend(flatten([sub[2][0] for sub in filtered_sub_map]))
            self.slot_names.extend(flatten([sub[2][1] for sub in filtered_sub_map]))

