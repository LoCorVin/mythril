from z3 import BitVec, BitVecVal
import logging
from mythril.laser.ethereum.state import WorldState
from mythril.annotary.debugc import printd
from mythril.laser.ethereum.transaction import TransactionStartSignal, TransactionEndSignal, \
    ContractCreationTransaction, CreateNewContractSignal
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from datetime import datetime, timedelta
from copy import copy, deepcopy
from functools import reduce
from mythril.laser.ethereum.transaction import execute_contract_creation, execute_message_call

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1

class StateIdAssigner:

    def __init__(self):
        self.states = []
        self.state_id = 0

    def set_new_state(self, state):
        state.id = self.state_id
        self.states.append(state)
        self.state_id += 1



class SVMError(Exception):
    pass


class SymbolicCodeExtension:

    def __init__(self, symbolic_name, contract_name, extension_byte_size, predefined_map={}):
        self.symbolic_name = symbolic_name
        self.contract_name = contract_name
        self.extension_byte_size = extension_byte_size
        self.predifined_map = predefined_map

    def __len__(self):
        return self.extension_byte_size

    def __getitem__(self, item):
        if item in self.predifined_map:
            return self.predifined_map[item]
        return BitVec(self.symbolic_name + "_" + self.contract_name + "[" + str(item) + "]", 256)
'''
Main symbolic execution engine.
'''


class LaserEVM:
    """
    Laser EVM class
    """

    def __init__(self, accounts, dynamic_loader=None, max_depth=float('inf'), execution_timeout=60, create_timeout=10,
                 strategy=DepthFirstSearchStrategy, prepostprocessor=None):
        world_state = WorldState()
        world_state.accounts = accounts
        # this sets the initial world state
        self.world_state = world_state
        self.open_states = [world_state]

        self.nodes = {}
        self.edges = []
        self.coverage = {}

        self.total_states = 0
        self.dynamic_loader = dynamic_loader

        self.work_list = []
        self.strategy = strategy(self.work_list, max_depth)
        self.max_depth = max_depth

        self.execution_timeout = execution_timeout
        self.create_timeout = create_timeout

        self.time = None

        self.pre_hooks = {}
        self.post_hooks = {}

        if prepostprocessor:
            self.prepostprocessor = prepostprocessor
        else:
            self.prepostprocessor = None

        self.state_id_assigner = StateIdAssigner()

        logging.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    @property
    def accounts(self):
        return self.world_state.accounts

    def sym_exec(self, main_address=None, creation_code=None, contract_name=None, code_extension=None):
        logging.debug("Starting LASER execution")
        self.time = datetime.now()

        if main_address:
            logging.info("Starting message call transaction to {}".format(main_address))
            execute_message_call(self, main_address)
        elif creation_code:
            logging.info("Starting contract creation transaction")
            created_account = execute_contract_creation(self, creation_code, contract_name=contract_name, code_extension=code_extension)
            logging.info("Finished contract creation, found {} open states".format(len(self.open_states)))
            if len(self.open_states) == 0:
                print("No contract was created during the execution of contract creation "
                      "Try to increase the resources for creation exection (max-depth or create_timeout)")
            printd("Finished outer creation")

            # Reset code coverage
            self.coverage = {}

            self.time = datetime.now()
            logging.info("Starting message call transaction")
            execute_message_call(self, created_account.address)

            #self.time = datetime.now()
            #execute_message_call(self, created_account.address)

        logging.info("Finished symbolic execution")
        logging.info("%d nodes, %d edges, %d total states", len(self.nodes), len(self.edges), self.total_states)
        for code, coverage in self.coverage.items():
            cov = reduce(lambda sum_, val: sum_ + 1 if val else sum_, coverage[1]) / float(coverage[0]) * 100
            logging.info("Achieved {} coverage for code: {}".format(cov, code))

    def exec(self, create=False):
        for global_state in self.strategy:
            if self.execution_timeout and not create:
                if self.time + timedelta(seconds=self.execution_timeout) <= datetime.now():
                    print("Timeout Transaction reached, stopping")
                    return
            elif self.create_timeout and create:
                if self.time + timedelta(seconds=self.create_timeout) <= datetime.now():
                    print("Timeout Transaction reached, stopping")
                    return

            try:
                new_states, op_code = self.execute_state(global_state)
            except NotImplementedError:
                logging.info("Encountered unimplemented instruction")
                continue


            self.work_list += new_states

            # Todo consider whether adding this to have a traversable state execution tree is woth it


            if not hasattr(global_state, "id"):
                self.state_id_assigner.set_new_state(global_state)
            if not hasattr(global_state, "next"):
                global_state.next = []
            for new_state in new_states:
                new_state.previous = global_state.id
                self.state_id_assigner.set_new_state(new_state)
                global_state.next.append(new_state.id)
            # Todo End here

            if self.prepostprocessor:
                new_states = self.prepostprocessor.filter(global_state, new_states)


            self.total_states += len(new_states)
            self.manage_cfg(op_code, new_states)

    def execute_state(self, global_state):
        instructions = global_state.environment.code.instruction_list
        try:
            op_code = instructions[global_state.mstate.pc]['opcode']
        except IndexError:
            self.open_states.append(global_state.world_state)
            return [], None

        self._execute_pre_hook(op_code, global_state)
        try:
            self._measure_coverage(global_state)

            if self.prepostprocessor:
                global_state = self.prepostprocessor.preprocess(global_state)
                op_code = global_state.get_current_instruction()['opcode']

            new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(global_state)

            if self.prepostprocessor:
                new_global_states = self.prepostprocessor.postprocess(global_state, new_global_states)

        except CreateNewContractSignal as c:
            laser_evm = LaserEVM(self.accounts, self.dynamic_loader, self.max_depth, self.execution_timeout, self.create_timeout,
                 strategy=DepthFirstSearchStrategy, prepostprocessor=self.prepostprocessor)

            laser_evm.open_states = [self.world_state]
            printd("Start subconstruction")
            code_extension = SymbolicCodeExtension("calldata", "Subcontract", c.extension_byte_size, c.predefined_map)
            created_account = execute_contract_creation(laser_evm, c.bytecode, contract_name="Subcontract",
                        code_extension=code_extension, callvalue=c.callvalue)

            if laser_evm.open_states:
                created_account = laser_evm.open_states[0].accounts[created_account.address]

            paused_state = c.paused_state
            paused_state.accounts[created_account.address] = created_account

            # Computing address from hex str returned to z3 BitVec representation
            address_as_int = 0
            new_address = created_account.address.replace("0x", "")
            i = 0
            while i < len(new_address):
                address_as_int *= 256
                address_as_int += int(new_address[i:i + 2], 16)
                i += 2


            paused_state.mstate.stack.append(BitVecVal(address_as_int, 256))
            paused_state.mstate.pc += 1 # Because the post code of instruction wrapper was not executed after Signal
            new_global_states = [paused_state]

            if self.prepostprocessor:
                new_global_states = self.prepostprocessor.postprocess(global_state, new_global_states)
            printd("End subcontruction")

        except TransactionStartSignal as e:
            printd("Transaction start")
            # Setup new global state
            new_global_state = e.transaction.initial_global_state()


            new_global_state.transaction_stack = copy(global_state.transaction_stack) + [(e.transaction, global_state)]
            new_global_state.node = global_state.node
            new_global_state.mstate.constraints = global_state.mstate.constraints

            return [new_global_state], op_code

        except TransactionEndSignal as e:
            printd("Transaction end")
            transaction, return_global_state = e.global_state.transaction_stack.pop()

            if return_global_state is None:
                if not isinstance(transaction, ContractCreationTransaction) or transaction.return_data:
                    e.global_state.world_state.node = global_state.node
                    self.open_states.append(e.global_state.world_state)
                new_global_states = []
            else: 
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [e.global_state])

                # Resume execution of the transaction initializing instruction
                op_code = return_global_state.environment.code.instruction_list[return_global_state.mstate.pc]['opcode']

                # Set execution result in the return_state
                return_global_state.last_return_data = transaction.return_data
                return_global_state.world_state = copy(global_state.world_state)
                return_global_state.environment.active_account = \
                    global_state.accounts[return_global_state.environment.active_account.address]
		
                #if self.prepostprocessor:
                #    global_state = self.prepostprocessor.preprocess(global_state)
                #    op_code = global_state.get_current_instruction()['opcode']

                # Execute the post instruction handler
                new_global_states = Instruction(op_code, self.dynamic_loader).evaluate(return_global_state, True)

                #if self.prepostprocessor:
                #    new_global_states = self.prepostprocessor.postprocess(global_state, new_global_states)

                # In order to get a nice call graph we need to set the nodes here
                for state in new_global_states:
                    state.node = global_state.node

        self._execute_post_hook(op_code, new_global_states) # Todo Maybe also filter here

        return new_global_states, op_code

    def _measure_coverage(self, global_state):
        code = global_state.environment.code.bytecode
        number_of_instructions = len(global_state.environment.code.instruction_list)
        instruction_index = global_state.mstate.pc

        if code not in self.coverage.keys():
            self.coverage[code] = [number_of_instructions, [False]*number_of_instructions]

        self.coverage[code][1][instruction_index] = True

    def manage_cfg(self, opcode, new_states):
        if opcode == "JUMP":
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state)
        elif opcode == "JUMPI":
            for state in new_states:
                self._new_node_state(state, JumpType.CONDITIONAL, state.mstate.constraints[-1])
        elif opcode in ("CALL", 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state, JumpType.CALL)
                # Keep track of added contracts so the graph can be generated properly
                if state.environment.active_account.contract_name not in self.world_state.accounts.keys():
                    self.world_state.accounts[
                        state.environment.active_account.address] = state.environment.active_account
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(self, state, edge_type=JumpType.UNCONDITIONAL, condition=None):
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        new_node.constraints = state.mstate.constraints
        self.nodes[new_node.uid] = new_node
        self.edges.append(Edge(old_node.uid, new_node.uid, edge_type=edge_type, condition=condition))

        if edge_type == JumpType.RETURN:
            new_node.flags |= NodeFlags.CALL_RETURN
        elif edge_type == JumpType.CALL:
            try:
                if 'retval' in str(state.mstate.stack[-1]):
                    new_node.flags |= NodeFlags.CALL_RETURN
                else:
                    new_node.flags |= NodeFlags.FUNC_ENTRY
            except IndexError:
                new_node.flags |= NodeFlags.FUNC_ENTRY
        if not state.environment.code:
            print()
        address = state.environment.code.instruction_list[state.mstate.pc - 1]['address']
        
        environment = state.environment
        disassembly = environment.code
        if address in state.environment.code.addr_to_func:
            # Enter a new function

            environment.active_function_name = disassembly.addr_to_func[address]
            new_node.flags |= NodeFlags.FUNC_ENTRY

            logging.info(
                "- Entering function " + environment.active_account.contract_name + ":" + new_node.function_name)
        elif address == 0:
            environment.active_function_name = "fallback"

        new_node.function_name = environment.active_function_name

    def _execute_pre_hook(self, op_code, global_state):
        if op_code not in self.pre_hooks.keys():
            return
        for hook in self.pre_hooks[op_code]:
            hook(global_state)

    def _execute_post_hook(self, op_code, global_states):
        if op_code not in self.post_hooks.keys():
            return

        for hook in self.post_hooks[op_code]:
            for global_state in global_states:
                hook(global_state)

    def hook(self, op_code):
        def hook_decorator(function):
            if op_code not in self.pre_hooks.keys():
                self.pre_hooks[op_code] = []
            self.pre_hooks[op_code].append(function)
            return function

        return hook_decorator

    def post_hook(self, op_code):
        def hook_decorator(function):
            if op_code not in self.post_hooks.keys():
                self.post_hooks[op_code] = []
            self.post_hooks[op_code].append(function)
            return function

        return hook_decorator
