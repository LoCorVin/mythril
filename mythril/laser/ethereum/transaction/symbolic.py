from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction, ContractCreationTransaction
from z3 import BitVec
from mythril.laser.ethereum.state import GlobalState, Environment, CalldataType, Account, WorldState
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import Storage
from mythril.laser.ethereum.cfg import Node, Edge, JumpType
from copy import deepcopy


def execute_message_call(laser_evm, callee_address):
    """ Executes a message call transaction from all open states """
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    open_world_state = open_states[0]
    open_world_state.accounts = deepcopy(open_world_state.accounts)
    open_world_state[callee_address].storage = Storage()

    transaction = MessageCallTransaction(
        open_world_state,
        open_world_state[callee_address],
        BitVec("caller", 256),
        [],
        BitVec("gasprice", 256),
        BitVec("callvalue", 256),
        BitVec("origin", 256),
        CalldataType.SYMBOLIC,
    )
    _setup_global_state_for_execution(laser_evm, transaction)

    laser_evm.exec()


def execute_contract_creation(laser_evm, contract_initialization_code, contract_name, code_extension=None, callvalue=BitVec("callvalue", 256)):
    """ Executes a contract creation transaction from all open states"""
    open_states = laser_evm.open_states[:]
    del laser_evm.open_states[:]

    new_account = laser_evm.world_state.create_account(0, concrete_storage=True, dynamic_loader=None, contract_name=contract_name)

    for open_world_state in open_states:
        transaction = ContractCreationTransaction(
            open_world_state,
            BitVec("caller", 256),
            new_account,
            Disassembly(contract_initialization_code),
            [],
            BitVec("gasprice", 256),
            callvalue,
            BitVec("origin", 256),
            CalldataType.SYMBOLIC
        )
        if code_extension:
            transaction.code_extension = code_extension

        _setup_global_state_for_execution(laser_evm, transaction)
    laser_evm.exec(True)

    return new_account


def _setup_global_state_for_execution(laser_evm, transaction):
    """ Sets up global state and cfg for a transactions execution"""
    global_state = transaction.initial_global_state()
    global_state.transaction_stack.append((transaction, None))

    new_node = Node(global_state.environment.active_account.contract_name)

    laser_evm.nodes[new_node.uid] = new_node
    if transaction.world_state.node:
        laser_evm.edges.append(Edge(transaction.world_state.node.uid, new_node.uid, edge_type=JumpType.Transaction,
                               condition=None))
    global_state.node = new_node
    new_node.states.append(global_state)
    laser_evm.work_list.append(global_state)
