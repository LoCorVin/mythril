from .annotation import Status
from collections import deque
from copy import copy
from .z3utility import are_z3_satisfiable

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
                self.annotations.remove(annotation) # removing finished annotation from the self.annotations worklist

        # Faster more efficient combination by using only name mappings
        #const_traces = list(map(lambda trace: (trace.get_ref_storage_names(), trace.get_storage_subs_map()), self.const_traces))
        #trans_traces = list(map(lambda trace: (trace.get_ref_storage_names(), trace.get_storage_subs_map()), self.trans_traces))

        traces = self.const_traces + self.trans_traces

        while self.annotations:
            annotation = self.annotations.popleft()
            annotation.violations = deque(annotation.violations)
            while annotation.violations:
                violation = annotation.violations.popleft()
                vts = [violation.trace]
                for i in range(4):
                    new_vs = []
                    while vts:
                        v = vts.popleft()
                        for t in traces:
                            vt_new = t.apply_trace(v)
                            if t in self.const_traces:
                                # Todo set variables to 0
                            if not contains_storage_reference(vt_new):
                                if not are_z3_satisfiable(vt_new.tran_constraints):
                                    # Todo set state and remove violations and annotations from lists
                            else:
                                new_vs.append(new_vs)
                    vts = deque(new_vs)

        print()

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

    def __init__(self, const_traces, trans_traces, annotations):
        super(BackwardChainStrategy, self).__init__(const_traces, trans_traces, annotations)

    def check_violations(self, violations):
        pass
