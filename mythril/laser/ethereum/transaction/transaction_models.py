import logging
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import GlobalState, Environment, WorldState
from z3 import BitVec
import array


class TransactionEndSignal(Exception):
    """ Exception raised when a transaction is finalized"""
    def __init__(self, global_state):
        self.global_state = global_state


class TransactionStartSignal(Exception):
    """ Exception raised when a new transaction is started"""
    def __init__(self, transaction, op_code):
        self.transaction = transaction
        self.op_code = op_code


class MessageCallTransaction:
    """ Transaction object models an transaction"""
    def __init__(self,
                 world_state,
                 callee_account,
                 caller,
                 call_data=(),
                 gas_price=BitVec("gasprice", 256),
                 call_value=BitVec("callvalue", 256),
                 origin=BitVec("origin", 256),
                 call_data_type=BitVec("call_data_type", 256),
                 code=None
                 ):
        assert isinstance(world_state, WorldState)
        self.world_state = world_state
        self.callee_account = callee_account
        self.caller = caller
        self.call_data = call_data
        self.gas_price = gas_price
        self.call_value = call_value
        self.origin = origin
        self.call_data_type = call_data_type
        self.code = code
        self.return_data = None

    def initial_global_state(self):
        # Initialize the execution environment
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            code=self.code or self.callee_account.code,
            calldata_type=self.call_data_type,
        )

        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = 'fallback'

        return global_state

    def end(self, global_state, return_data=None):
        self.return_data = return_data
        raise TransactionEndSignal(global_state)


class ContractCreationTransaction:
    """ Transaction object models an transaction"""
    def __init__(self,
                 world_state,
                 caller,
                 callee_account=None,
                 code=None,
                 call_data=(),
                 gas_price=BitVec("gasprice", 256),
                 call_value=BitVec("callvalue", 256),
                 origin=BitVec("origin", 256),
                 call_data_type=BitVec("call_data_type", 256),
                 contract_name="unknown"
                 ):
        assert isinstance(world_state, WorldState)

        self.world_state = world_state
        # TODO: set correct balance for new account
        self.callee_account = callee_account if callee_account else world_state.create_account(0, concrete_storage=True, contract_name=contract_name)

        self.caller = caller
        self.call_data = call_data
        self.gas_price = gas_price
        self.call_value = call_value

        self.origin = origin
        self.call_data_type = call_data_type
        self.code = code
        self.return_data = None

    def initial_global_state(self):
        # Initialize the execution environment
        environment = Environment(
            self.callee_account,
            self.caller,
            self.call_data,
            self.gas_price,
            self.call_value,
            self.origin,
            self.code,
            calldata_type=self.call_data_type,
        )
        if hasattr(self, "code_extension"):
            environment.code_extension = self.code_extension


        global_state = GlobalState(self.world_state, environment, None)
        global_state.environment.active_function_name = 'constructor'

        return global_state

    def end(self, global_state, return_data=None):

        if not all([isinstance(element, int) for element in return_data]):
            self.return_data = None
            raise TransactionEndSignal(global_state)

        contract_code = bytes.hex(array.array('B', return_data).tostring())

        global_state.environment.active_account.code = Disassembly(contract_code)
        self.return_data = global_state.environment.active_account.address

        raise TransactionEndSignal(global_state)
