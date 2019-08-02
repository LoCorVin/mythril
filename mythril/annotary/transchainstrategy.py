from mythril.annotary.annotation import Status
from collections import deque
from mythril.annotary.debugc import printd
from z3 import BitVecVal, BitVec, substitute
from mythril.annotary.z3utility import are_z3_satisfiable


class AnnotationFinishedException(Exception):
    """
    Used to jump out of the algorithm when all violations of an annotation have been finished to process.
    """
    pass


class ViolationFinishedException(Exception):
    """
    Used to jump out of the algorithm when a violation was processed sufficiently.
    """
    pass


def get_annotation_of_violation(annotations, violation):
    """
    Returns the annotation this violation violates.
    :param annotations: List of annotations.
    :param violation: The violation that violates the searched annotation.
    :return: The violated annotation.
    """
    for annotation in annotations:
        if violation in annotation.violations:
            return annotation


def contains_storage_reference(trace):
    """
    Searches the traces constraint list for references to the storage that holds contract state. Checking the
    constraints is sufficient as they depict the reachability of the trace(chain).
    :param trace: containing the constraints that are searched.
    :return: if the trace constraints contain variables referencing storage.
    """
    for t_constraint in trace.tran_constraints:
        if any(map(lambda n: n.startswith("storage["), t_constraint.slot_names)):
            return True
    return False


def zeroize_constraints(constraints):
    """
    Replaces all symbolic variables referencing storage in the constraints list by the value 0.
    :param constraints: to be substituted in.
    """
    for constraint in constraints:
        constraint.constraint = substitute(constraint.constraint, [(BitVec(slot_name, 256), BitVecVal(0, 256)) for slot_name in constraint.slot_names])
        constraint.tran_names = [sym_name for sym_name in constraint.tran_names if sym_name in constraint.slot_names]
        constraint.slot_names = []


def zeroize_storage_vars(trace):
    """
    Replaces all symbolic variables referencing storage in the constraints and transaction constraints list
    by the value 0.
    :param trace: to be substituted in.
    """
    zeroize_constraints(trace.constraints)
    zeroize_constraints(trace.tran_constraints)
    for slot_idx, slot in trace.storage.items():
        trace.storage[slot_idx].slot = substitute(slot.slot, [(BitVec(slot_name, 256), BitVecVal(0, 256)) for slot_name in slot.slot_names])
        slot.tran_names = [sym_name for sym_name in slot.tran_names if sym_name in slot.slot_names]
        slot.slot_names = []


class ChainStrategy:
    """
    This class is a generalized interface for strategies that chain traces in front of found violations to
    check whether or not the violation is intertransactionally reachable.
    """

    def __init__(self, const_traces, trans_traces, annotations, config):
        """
        Initializes the strategy.
        :param const_traces: Traces extracted from the execution of the construction bytecode.
        :param trans_traces: Traces extracted from the execution of the runtime bytecode.
        :param annotations: Found in the contract and equipped with the potential violation found
        during symbolic execution.
        :param config: Configuration for the chaining strategy such as different optimizations.
        """
        self.config = config
        self.const_traces = const_traces
        self.trans_traces = trans_traces
        # Worklist containing the annotations -> violations -> trace -> constraints&storage
        self.annotations = deque(annotations)

        for annotation in annotations:
            annotation.status = Status.HSINGLE
            for violation in annotation.violations:
                # The initial confidence level is VDEPTH
                annotation.status = Status.VDEPTH
                violation.status = Status.VDEPTH
                trace = violation.trace
                if not contains_storage_reference(trace):
                    # If the constraints don't reference state, a violation with high severity and confidence was found
                    violation.status = Status.VSINGLE
                    annotation.status = Status.VSINGLE

    def check_violations(self, violations):
        """returns a status from Annotation status: HOLDS, UNCHECKED, VSINGLE, VDEPTH, VCHAIN and a transactionchain
        with one violation prepend violation prepend
        """
        raise NotImplementedError("Unimplemented chain strategy interface")


class ForwardChainStrategy(ChainStrategy):
    """Builds chains until it can append a violation. When depth is reached, VDEPTH is returned, if at some point the
    appending was successful VCHAIN is returned together with the first encountered violation.
    """

    def __init__(self, const_traces, trans_traces, annotations, config):
        super(ForwardChainStrategy, self).__init__(const_traces, trans_traces, annotations, config)

    def check_violations(self, violations):
        pass


def refines_constraints(storage, constraints):
    """
    Determines whether with the storage as basis for the substitution map there is a substitution that can be performed
    on the constraints, therefore refining them.
    :param storage: The storage basis for the substitution map
    :param constraints: The constraint list containing the expressions to be substituted.
    :return: True if the substitution would change the constraint list.
    """
    storage_names = ["storage[" + str(key) + "]" for key, _ in storage.items()]
    for name in storage_names:
        for constraint in constraints:
            if name in constraint.slot_names:
                return True
    return False


class BackwardChainStrategy(ChainStrategy):
    """
        Reversly builds the chains from the violation by appending transaction, if appending a constructor trace
        worked, and no symbolic variable refers to the storage, the violation was verified.
    """

    def __init__(self, const_traces, trans_traces, annotations, config):
        super(BackwardChainStrategy, self).__init__(const_traces, trans_traces, annotations, config)

    def check_violations(self):
        traces = self.const_traces + self.trans_traces

        while self.annotations:
            annotation = self.annotations.popleft()
            violations = deque(annotation.violations)
            printd(annotation.annotation_str)
            try:
                # Checks one violation at a time.
                while violations:
                    # True when a chain starting at a construction trace was found
                    constructor_chain = None
                    violation = violations.popleft()
                    # skips already verified violations
                    if violation.status == Status.VSINGLE:
                        continue
                    vts = deque([violation.trace])
                    try:
                        # Goes only until a preconfigured maximal transaction chain
                        for i in range(self.config.max_transaction_depth):
                            new_vs = []
                            while vts:
                                v = vts.popleft()
                                # Violation is finished when a chain or single transaction with non state referencing
                                # constraints was found
                                if violation.status in [Status.VSINGLE or Status.VCHAIN]:
                                    raise ViolationFinishedException
                                for t in traces:
                                    is_const = t in self.const_traces
                                    # Does not consider constructor traces, if such a trace was already found.
                                    if constructor_chain and is_const:
                                        continue
                                        # Only applies a trace to the current violation trace if it changes the
                                        # constraints
                                    if refines_constraints(t.storage, v.tran_constraints):
                                        vt_new = t.apply_trace(v)
                                        if not vt_new: # If resulting trace contains not satisfiable constraints, the trace is skipped
                                            continue
                                        if is_const:
                                            # If the constructor is reached the evm read the def value 0 from storage
                                            zeroize_storage_vars(vt_new)
                                            # Satisfiability check already done when combining traces, only repeat
                                            # here because zeroizing might renderhe constraints unsatisfiable
                                            if not are_z3_satisfiable([constraint.constraint for constraint in
                                                                       vt_new.tran_constraints]):
                                                continue
                                        # No storage references implies that violating trace can be applied to any
                                        # storage state of the contract and be satifiable
                                        if not contains_storage_reference(vt_new):
                                            if self.config.search_for_indipendent_chain and is_const:
                                                # If a independent chain should be searched after a construction chain
                                                # was found the former is cached
                                                constructor_chain = (vt_new, Status.VCHAIN)
                                            else:
                                                # Found the violating chain
                                                violation.trace = vt_new
                                                violation.status = Status.VCHAIN
                                                raise ViolationFinishedException()
                                        else:
                                            # Add non construction chains to the worklist for the next depth
                                            if not is_const:
                                                new_vs.append(vt_new)
                            if not new_vs:
                                # if the space of trace chains was exhausted the algorithm returns with the found
                                # construction trace or the statement that the annotations holds
                                if constructor_chain:
                                    violation.trace = constructor_chain[0]
                                    violation.status = constructor_chain[1]
                                else:
                                    violation.trace = None
                                    violation.status = Status.HOLDS
                                raise ViolationFinishedException()
                            else:
                                vts = deque(new_vs)
                        # When the maximal exploration depth was reached the found constructor chain or the statement
                        # that the violation could not be confirmed is returned
                        if vts:
                            if constructor_chain:
                                violation.trace = constructor_chain[0]
                                violation.status = constructor_chain[1]
                            else:
                                violation.status = Status.VDEPTH
                                violation.trace = vts[0]
                    except ViolationFinishedException as v:
                        pass
            except AnnotationFinishedException as a:
                pass
            status = Status.HSINGLE
            # Sets the anntotation confidence level according to the most sever found violation
            for violation in annotation.violations:
                if status.value < violation.status.value:
                    status = violation.status
            annotation.status = status
