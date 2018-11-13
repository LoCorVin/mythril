from z3 import *
from mythril.annotary.z3utility import get_function_from_constraints, simplify_constraints_individually, sanitize_expr
from copy import deepcopy
from mythril.annotary.sn_utils import flatten
from mythril.annotary.debugc import printd
from mythril.laser.ethereum.transaction import ContractCreationTransaction
import re
from mythril.annotary.z3utility import are_satisfiable, simplify_constraints, simplify_z3_constraints, \
    extract_sym_names, filter_for_t_variable_data
from mythril.annotary.z3wrapper import Slot, Constraint

simp_and_sat = False


def deep_bitvec_substitute(obj, subs_map):
    if (not hasattr(obj, 'children') or len(obj.children()) == 0) and type(obj) == BitVecRef and hasattr(obj, 'decl') :
            return [str(obj.decl())]
    else:
        sym_vars = []
        for c in obj.children():
            if (not hasattr(obj, 'children') or len(obj.children()) == 0) and type(c) == BitVecRef and hasattr(obj, 'decl'):
                pass
            else:
                sym_vars.extend(deep_bitvec_substitute(c, subs_map))
        return sym_vars

# Todo constructor mit den intentet initvalues versorgen




class TransactionTrace:

    def __init__(self, state, contract=None, lvl=1):
        # self.storage = {k: simplify(v) for k,v in storage }
        constraints = state.mstate.constraints
        storage = state.environment.active_account.storage
        self.constraints = simplify_constraints_individually(constraints)
        if contract:
            self.functions = [get_function_from_constraints(contract, state.mstate.constraints, isinstance(state.current_transaction, ContractCreationTransaction))]

        # eliminate all constraints that only contain names not in the set of names from storage
        self.constraints = simplify_z3_constraints(self.constraints) # Todo simplification of the sum of constraints



        # Or hook transformation in here
        self.storage = {s_name: Slot(s_name, simplify(sanitize_expr(z3_vars))) for (s_name, z3_vars) in storage._storage.items()}
        self.constraints = [Constraint(constraint) for constraint in self.constraints]

        self.tran_constraints = deepcopy(self.constraints)
        self.lvl = lvl
        self.sym_names = flatten(self.extract_sym_names_from_storage())

        # Constraints on storage keys to are necessary
        self.tran_constraints = [tra_const for tra_const in self.tran_constraints if tra_const.slot_names]
        #self.tran_constraints = list(filter(lambda c: any([name in (self.sym_names + ["storage_" + str(s_key) for
        #    s_key, _ in self.storage.items()]) for name in extract_sym_names(c)]), self.tran_constraints))

        # Transformation
        #self.storage = {s_name: Slot(s_name, z3_vars) for (s_name, z3_vars) in self.storage.items()}
        #self.tran_constraints = [Constraint(constraint) for constraint in self.tran_constraints]

        self.sym_names.extend(flatten(self.extract_sym_names_from_constraints()))
        if lvl == 1:
            self.set_transaction_idx()


    """   
        Returns the list of referenced storage slots in storage slot content and constraints, these have to be 
        solved/substituted with other expressions to find an executable chain.
    """
    def get_ref_storage_names(self):
        if hasattr(self, "ref_slots"):
            return self.ref_slots
        # Todo recompute on combination
        self.ref_slots = [[], []]
        for constraints in self.tran_constraints:
            self.ref_slots[1].extend(constraints.slot_names)
        for slot_idx, slot in self.storage.items():
            if not eq(slot.slot, BitVec("storage[" + str(slot_idx) + "]", 256)):
                self.ref_slots[0].extend(slot.slot_names)
        return self.ref_slots


    """
        Returns a mapping, that mapps the contained written storage names to the storage names of slots mapped in the 
        contained expression:
        
        e.g. 1: UDIV(storage[0], UADD(storage[0], storage[1]))  ->    "storage[0]" : ["storage[0]", "storage[1]"]
    """
    def get_storage_subs_map(self):
        if hasattr(self, "subs_map"):
            return self.subs_map
        # Todo recompute on combination
        self.subs_map = {}
        for slot_idx, slot in self.storage.items():
            if not eq(slot.slot, BitVec("storage[" + str(slot_idx) + "]", 256)):
                self.subs_map["storage[" + str(slot_idx) + "]"] = slot.slot_names
        return self.subs_map

    def update_ref_storage_names(self):
        del self.ref_slots
        self.get_ref_storage_names()

    def update_storage_subs_map(self):
        del self.subs_map
        self.get_storage_subs_map()


    def __str__(self):
        return str(self.as_dict())

    def as_dict(self):

        return {'lvl': self.lvl, 'storage': str({s_name: slot.slot for s_name, slot in self.storage}),
                'tran_constraints': str([const.constraint for const in self.tran_constraints])}

    def pp_trace(self):
        printd()
        printd("Trace lvl: {}".format(self.lvl))
        printd("Storage: {}".format({k: str(v.slot).replace("\n", " ") for k, v in self.storage.items()}))
        printd("Tran_constraints: {}".format(list(map(lambda x: str(x.constraint).replace("\n", " "), self.tran_constraints))))
        printd()

    def add_transaction_idx(self, offset):# Delete if no error shows

        new_names = []
        for name in self.sym_names:
            matched_name = re.search(r't([0-9]+)(_.*)', name)
            num = int(matched_name.group(1)) + offset
            new_names.append("t" + str(num) + matched_name.group(2))
        repl_tup = list(zip(self.sym_names, new_names))

        self.substitute_bv_names(repl_tup)

        self.sym_names = new_names

    def get_transaction_depth_repl_tuples(self, offset):
        new_names = []
        for name in self.sym_names:
            matched_name = re.search(r't([0-9]+)(_.*)', name)
            num = int(matched_name.group(1)) + offset
            new_names.append("t" + str(num) + matched_name.group(2))
        repl_tup = list(zip(self.sym_names, new_names))

        # self.substitute_bv_names(repl_tup)

        self.sym_names = new_names
        return repl_tup

    def set_transaction_idx(self):
        repl_tup = []
        new_sym_names = []
        for name in self.sym_names:
            repl_tup.append((name, "t1_" + name))
            new_sym_names.append("t1_" + name)
        self.sym_names = new_sym_names
        self.substitute_bv_names(repl_tup)

    # Todo merge this (transaction depth add) subs with the other(storage slot) subs

    def substitute_bv_names(self, subs_tuple):
        subs_tuples = list(map(lambda name_t: (name_t[0], BitVec(name_t[1], 256), ([name_t[1]], [])), subs_tuple))
        for s_num, _ in self.storage.items():
            self.storage[s_num].substitute(subs_tuples)
        for c_idx in range(len(self.tran_constraints)):
            self.tran_constraints[c_idx].substitute(subs_tuples)

    def extract_sym_names_from_storage(self):
        return [slot.sym_names for _, slot in self.storage.items()]
        sym_names = []
        sum = 0
        for k,v in self.storage.items():
            vs_sym_names = extract_sym_names(v)
            sym_names.extend(vs_sym_names)
            if vs_sym_names:
                sum += 1
        printd("Extracted sym storage: " + str(sum) + " " + str( float(len(self.storage) - sum) / len(self.storage)))
        return filter_for_t_variable_data(sym_names)

    def extract_sym_names_from_constraints(self):
        return [const.sym_names for const in self.constraints]
        sym_names = []
        sum = 0
        for v_idx in range(len(self.tran_constraints)):
            vs_sym_names = extract_sym_names(self.tran_constraints[v_idx])
            sym_names.extend(vs_sym_names)
            if vs_sym_names:
                sum += 1
        printd("Extracted sym constraints: " + str(sum) + " " + str( float(len(self.storage) - sum) / len(self.storage)))
        return filter_for_t_variable_data(sym_names) # Todo Check whether here it is the right choice too, to filter ...

    """
          Either do only deep checking here and use the proper trace or storage_slot reduction in the apply function. Or do
          both here.
      """

    def deep_equals(trace_lvl1, trace_lvl2):
        return set(trace_lvl1) == set(trace_lvl2) # Todo Impelement an ACTUAL deep comparison

    def simplify_storage(self):
        for k,v in self.storage.items():
            # Todo explore the arguments of this storage simplification in z3 to find ways to further simplify and to
            # sort this expressions for equality comparison
            self.storage[k].simplify()

    """
        Applies the new trace tt on a possibly even changed trace self.
    """
    def apply_trace(self, tt):
        if tt is None:
            return self
        new_trace = deepcopy(tt)
        subs_map = list(map(lambda x: (x[0], BitVec(x[1], 256), ([x[1]], [])), new_trace.get_transaction_depth_repl_tuples(self.lvl)))

        subs_map.extend(list(map(lambda x: ("storage[" + str(x[0]) + "]", x[1].slot, (x[1].sym_names, x[1].slot_names)), self.storage.items()))) # Build this map only once

        for k,v in new_trace.storage.items():
            new_trace.storage[k].substitute(subs_map)  # Todo substitute only if necessary

        # Copies all storage entries that are not changed in the newer trace
        for k in self.storage.keys():
            if k not in new_trace.storage:
                new_trace.storage[k] = deepcopy(self.storage[k])

        for c_idx in range(len(new_trace.tran_constraints)):
            new_trace.tran_constraints[c_idx].substitute(subs_map) # Todo only substitute if necessary
        new_trace.lvl += self.lvl
        new_trace.sym_names.extend(deepcopy(self.sym_names))
        # self can be omitted (e.g. when related storage locations were overwritten)
        new_trace.functions = self.functions + tt.functions
        if simp_and_sat:
            new_trace.simplify_storage()
            new_trace.tran_constraints = simplify_constraints(new_trace.tran_constraints)
            # Simplify constraints in there sum to eliminate subconstraints
            if are_satisfiable(new_trace.tran_constraints):
                return new_trace
            else:
                return None
        else:
            return new_trace

    def apply_traces_parallel(self, traces):
        combined_traces = []
        for trace in traces:
            combined_traces.append(self.apply_trace(trace))
        return list(filter(lambda t: not t is None, combined_traces))

    def apply_exact_trace_levels(self, traces, depth):
        # Todo maybe some faster trace build not building one level at a time to e.g.
        # Todo reach level 17 but build 2, then 4, then 8 and then 16 then 17
        trace_lvl_n = [self]
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in trace_lvl_n:
                trace_lvl_np1.extend(trace.apply_traces_parallel(traces))
            if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_n): # Fixpoint detected, function needs to ignore lists, dicts and objects.
                return trace_lvl_n
            trace_lvl_n = trace_lvl_np1
        return trace_lvl_n

    def apply_up_to_trace_levels(self, traces, depth):
        traces_up_to = [[self]] # elements are trace_levels
        for i in range(depth):
            trace_lvl_np1 = []
            for trace in traces_up_to[-1]:
                trace_lvl_np1.extend(trace.apply_traces_parallel(traces))
            for trace_lvl_i in traces_up_to:
                # the following might be faster to check when using a content representing hash
                if TransactionTrace.deep_equals(trace_lvl_np1, trace_lvl_i): # cycle in the traces of trace chains detected: levels
                    # while repeat themselves, function needs to ignore lists, dicts and objects.
                    return traces_up_to
            traces_up_to.append(trace_lvl_np1)
        return traces_up_to

    # Todo Maybe implement a function that checks whether two traces are combinable before creating objekts, adv. in
    # case they are not the object creation doe not have to be done. Investigate whether a suicide trace completely
    # stopes the contract from being executable. In that case a suicided transaction also is not combinable with
    # successive transactions.

    # Todo write a function that allows to specify a function/invocable to explore the tracechain space in DFS manner


