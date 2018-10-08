class ChainStrategy:

    def __init__(self, const_traces, trans_traces):
        self.const_traces = const_traces
        self.trans_traces = trans_traces

    def check_violations(self, violations):
        """returns a status from Annotation status: HOLDS, UNCHECKED, VSINGLE, VDEPTH, VCHAIN and a transactionchain
        with one violation prepend violation prepend
        """
        raise NotImplementedError("Unimplemented chain strategy interface")

class ForwardChainStrategy(ChainStrategy):
    """Builds chains until it can append a violation. When depth is reached, VDEPTH is returned, if at some point the
    appending was successful VCHAIN is returned together with the first encountered violation.
    """

    def __init__(self, const_traces, trans_traces):
        super(ChainStrategy, self).__init__(const_traces, trans_traces)

    def check_violations(self, violations):
        pass

class BackwardChainStrategy(ChainStrategy):
    """
        Reversly builds the chains from the violation by appending transaction, if appending a constructor trace
        worked, and no symbolic variable refers to the storage, the violation was verified.
    """

    def __init__(self, const_traces, trans_traces):
        super(ChainStrategy, self).__init__(const_traces, trans_traces)

    def check_violations(self, violations):
        pass
