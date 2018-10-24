from mythril.annotary.annotation import Status
from collections import deque
from mythril.annotary.debugc import printd
from z3 import BitVecVal, BitVec, substitute
from mythril.annotary.z3utility import are_z3_satisfiable

class AnnotationFinishedException(Exception):
    pass

def get_annotation_of_violation(annotations, violation):
    for annotation in annotations:
        if violation in annotation.violations:
            return annotation

def contains_storage_reference(trace):
    found_storage_reference=False
    for t_constraint in trace.tran_constraints:
        if any(map(lambda n: n.startswith("storage["), t_constraint.slot_names)):
            return True
    return False

    # This should not be relevant after considering that any arbitrary value can stand in the storage slot if the
    # constraints have no mor references to them
    #for slot_idx, slot in trace.storage.items():
    #    if any(map(lambda n: n.startswith("storage[") and n != str(slot.slot), slot.slot_names)):
    #        found_storage_reference = True
    #        break
    #return found_storage_reference

def zeroize_constraints(constraints):
    for constraint in constraints:
        constraint.constraint = substitute(constraint.constraint, [(BitVec(slot_name, 256), BitVecVal(0, 256)) for slot_name in constraint.slot_names])
        constraint.sym_names = [sym_name for sym_name in constraint.sym_names if sym_name in constraint.slot_names]
        constraint.slot_names = []


def zeroize_storage_vars(trace):
    zeroize_constraints(trace.constraints)
    zeroize_constraints(trace.tran_constraints)
    for slot_idx, slot in trace.storage.items():
        trace.storage[slot_idx].slot = substitute(slot.slot, [(BitVec(slot_name, 256), BitVecVal(0, 256)) for slot_name in slot.slot_names])
        slot.sym_names = [sym_name for sym_name in slot.sym_names if sym_name in slot.slot_names]
        slot.slot_names = []


class ChainStrategy:

    def __init__(self, const_traces, trans_traces, annotations):
        self.const_traces = const_traces
        self.trans_traces = trans_traces
        self.annotations = deque(annotations) # Worklist containint the annotations -> violations -> trace -> constraints&storage


        for annotation in annotations:
            annotation.status = Status.UNCHECKED
            for violation in annotation.violations:
                violation.status = Status.UNCHECKED
                trace = violation.trace
                if not contains_storage_reference(trace):
                    violation.status = Status.VSINGLE
                    annotation.status = Status.VSINGLE
            if annotation.status == Status.VSINGLE:
                annotation.violations = [violation for violation in annotation.violations if violation.status == Status.VSINGLE]
                self.annotations.remove(annotation) # removing finished annotation from the self.annotations worklist

        # Faster more efficient combination by using only name mappings
        #const_traces = list(map(lambda trace: (trace.get_ref_storage_names(), trace.get_storage_subs_map()), self.const_traces))
        #trans_traces = list(map(lambda trace: (trace.get_ref_storage_names(), trace.get_storage_subs_map()), self.trans_traces))



    def check_violations(self, violations):
        """returns a status from Annotation status: HOLDS, UNCHECKED, VSINGLE, VDEPTH, VCHAIN and a transactionchain
        with one violation prepend violation prepend
        """
        raise NotImplementedError("Unimplemented chain strategy interface")

class ForwardChainStrategy(ChainStrategy):
    """Builds chains until it can append a violation. When depth is reached, VDEPTH is returned, if at some point the
    appending was successful VCHAIN is returned together with the first encountered violation.
    """

    def __init__(self, const_traces, trans_traces, annotations):
        super(ForwardChainStrategy, self).__init__(const_traces, trans_traces, annotations)

            

    def check_violations(self, violations):
        pass

class BackwardChainStrategy(ChainStrategy):
    """
        Reversly builds the chains from the violation by appending transaction, if appending a constructor trace
        worked, and no symbolic variable refers to the storage, the violation was verified.
    """

    def __init__(self, const_traces, trans_traces, annotations, depth=8):
        super(BackwardChainStrategy, self).__init__(const_traces, trans_traces, annotations)
        self.depth = depth

    def check_violations(self):
        traces = self.const_traces + self.trans_traces

        while self.annotations:
            annotation = self.annotations.popleft()
            annotation.violations = deque(annotation.violations)
            try:
                while annotation.violations:
                    violation = annotation.violations.popleft()
                    vts = deque([violation.trace])
                    for i in range(self.depth):
                        new_vs = []
                        while vts:
                            v = vts.popleft()
                            for t in traces:
                                is_const = False
                                vt_new = t.apply_trace(v)
                                if t in self.const_traces:
                                    is_const = True
                                    zeroize_storage_vars(t)
                                if not contains_storage_reference(vt_new):
                                    if are_z3_satisfiable([constraint.constraint for constraint in vt_new.tran_constraints]):
                                        if is_const:
                                            printd("ConstOriginChain")
                                        else:
                                            printd("IndiChain")
                                        violation.trace = vt_new
                                        violation.status = Status.VCHAIN
                                        annotation.status = Status.VCHAIN
                                        annotation.violations = [violation]
                                        raise AnnotationFinishedException()
                                else:
                                    new_vs.append(vt_new)
                        if not new_vs:
                            annotation.violations = []
                            annotation.status = Status.HOLDS
                            raise AnnotationFinishedException()
                        else:
                            vts = deque(new_vs)
                    if vts:
                        violation.status = Status.VDEPTH
                        violation.trace = vts
                        annotation.status = Status.VDEPTH
            except AnnotationFinishedException as v:
                pass
