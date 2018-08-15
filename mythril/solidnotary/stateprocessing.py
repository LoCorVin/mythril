from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from mythril.laser.ethereum.svm import SVMError
from copy import deepcopy
from enum import Enum
from z3 import simplify
from .z3utility import are_z3_satisfiable


# Instruction ignore type
class IType(Enum):
    ENTRY = 0
    EXIT = 1
    VIOLATION = 2

class PrePostProcessor:

    """
        Two functions 'preprocess' and 'postprocess' that are to be hooked in before and after processing an
        instruction in the symbolic execution engine. They bot return the type of parameter they get with the
        aim to overwrite them or modify them.

        Check configuration is there to check the enclosing svm's configuration to see whether or not it can
        use the implemented preprocessor.

    """

    def preprocess(self, global_state):
        raise NotImplementedError("PrePostProcessing interface")

    def postprocess(self, global_state, new_global_states):
        raise NotImplementedError("PrePostProcessing interface")

    def check_configuration(self, svm):
        raise NotImplementedError("PrePostProcessing interface")

    def filter(self, new_states):
        raise NotImplementedError("PrePostProcessing interface")

class AnnotationProcessor(PrePostProcessor):
    # This still has one disadvantage, the actual instruction sets that are used by different analysis if using the resulting
    # symbolic execution. Traces can also be build from the annotation modified symbolic execution. But running the
    # mythril analysis modules on the modified contract might give different results due to the processing of nodes and not states
    # actual but previous insturction that might me on the ignore list.

    def __init__(self, instructions, ignore_list):
        self.instructions = instructions
        self.ignore_list = ignore_list
        self.violations = []
        for ignr_tpl in self.ignore_list:
            self.violations.append([])
        self.state_ctr = 0
        self.restored_ids = []

    def check_configuration(self, svm):
        if svm.strategy != DepthFirstSearchStrategy:
            raise SVMError("Annotation instruction preprocessor can be only used with DFS strategy")


    def filter(self, new_states):
        ret_states = []
        for state in new_states:
            if not hasattr(state, "ignore"):
                ret_states.append(state)
        return ret_states

    def is_this_or_previouse_ignore_type(self, global_state, itype=IType.ENTRY):
        instructions = global_state.environment.code.instruction_list
        instr = instructions[global_state.mstate.pc]

        ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[itype.value] == instr]
        if not ignore_tuples and instructions[global_state.mstate.pc - 1]['opcode'] == 'JUMPDEST':
            # print("Handle pre jumpdest")
            jumpdest_istr = instructions[global_state.mstate.pc - 1]
            ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[itype.value] == jumpdest_istr]
        return ignore_tuples is not None and len(ignore_tuples) > 0

    def get_ignore_tuple(self, global_state, itype=IType.ENTRY):
        instructions = global_state.environment.code.instruction_list
        instr = instructions[global_state.mstate.pc]

        ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[itype.value] == instr]
        if not ignore_tuples and instructions[global_state.mstate.pc - 1]['opcode'] == 'JUMPDEST':
            jumpdest_istr = instructions[global_state.mstate.pc - 1]
            ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[itype.value] == jumpdest_istr]
        if not ignore_tuples:
            return None
        return ignore_tuples[0]

    def preprocess(self, global_state):
        instructions = global_state.environment.code.instruction_list
        instr = instructions[global_state.mstate.pc]
        if instr['address'] == 71:
            print()

        if hasattr(global_state, "duplicate"):
            print("Pick up duplicate")
        print(instr)
        if self.is_this_or_previouse_ignore_type(global_state, IType.ENTRY):
            if hasattr(global_state, 'saved_state'): # Skip
                print("Skip")
                ign_exit_istr = self.get_ignore_tuple(global_state, IType.ENTRY)[IType.EXIT.value]
                istr_idx = instructions.index(ign_exit_istr)
                global_state.mstate.pc = istr_idx + 1
            else: # Save
                # Todo Here we do now only MARK the state to be ignored
                print("Save")
                helper_state_ref = global_state
                global_state = deepcopy(helper_state_ref)
                global_state.saved_state = helper_state_ref
                global_state.id = self.state_ctr
                self.state_ctr += 1

        if self.is_this_or_previouse_ignore_type(global_state, IType.VIOLATION): # violation
            print("violation")
            for idx in range(len(global_state.mstate.constraints)):
                global_state.mstate.constraints[idx] = simplify(global_state.mstate.constraints[idx])
            if are_z3_satisfiable(global_state.mstate.constraints):
                violating_state = deepcopy(global_state)
                del violating_state.saved_state # Todo Why do we delete this here? I think we need the mark to ignore it in graph building
                self.violations[self.ignore_list.index(self.get_ignore_tuple(global_state, IType.VIOLATION))].append(violating_state)

        return global_state

    def postprocess(self, global_state, new_global_states):
        returnable_new_states = []

        if hasattr(global_state, 'ignore'):
            print("carry")
            for new_state in new_global_states:
                new_state.ignore = global_state.ignore

        # Had to be added, because treatment of a single instruction does not carry over added attributes
        if hasattr(global_state, 'saved_state'): # Carry
            for new_state in new_global_states:
                new_state.saved_state = global_state.saved_state
                new_state.id = global_state.id



        for new_state in new_global_states:
            if hasattr(new_state, "duplicate"):
                del new_state.duplicate
        #else:
            #print("Nothing to carry")

        for state_idx in range(len(new_global_states)):
            new_state = new_global_states[state_idx]
            instr = self.instructions[global_state.mstate.pc]

            if self.is_this_or_previouse_ignore_type(new_state, IType.ENTRY):
                print("Duplicate new")
                skip_state = new_state # Not using deepcopy here anymore, leeds to missing states in node in statespace
                new_global_states[state_idx] = None

                while self.is_this_or_previouse_ignore_type(skip_state, IType.ENTRY):

                    # Leave a new state to start the execution of the part to be ignored by the rest
                    ign_state = deepcopy(skip_state)
                    ign_state.ignore = "ignore"
                    returnable_new_states.append(ign_state)
                    print("Leave ignore state to process")

                    # set skip state to the next instruction that may again be a regular one
                    ign_exit_istr = self.get_ignore_tuple(skip_state, IType.ENTRY)[IType.EXIT.value]
                    istr_idx = self.instructions.index(ign_exit_istr)
                    skip_state.mstate.pc = istr_idx + 1
                # After skip state finally reached an instruction that is not another entry it is marked as dublicate
                skip_state.duplicate = "duplicate"
                returnable_new_states.append(skip_state)


            # Is exit instruction
            if self.is_this_or_previouse_ignore_type(global_state, IType.EXIT) and not hasattr(global_state, "duplicate"):
                print("Drop at exit")
                return returnable_new_states # Todo Drop only the ignored once at exit?
#                if hasattr(new_state, 'saved_state'):
#                    new_global_states[state_idx] = None
#                else:
#                    raise RuntimeError("No saved global state at encounter of exit instruction. This should not happen")

        returnable_new_states.extend(list(filter(lambda state: state is not None, new_global_states)))

        return returnable_new_states


