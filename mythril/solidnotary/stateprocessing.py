from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from mythril.laser.ethereum.svm import SVMError
from copy import deepcopy

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
        return list(filter(lambda state: not hasattr(state, "saved_state"), new_states))

    def preprocess(self, global_state):
        instructions = global_state.environment.code.instruction_list
        instr = instructions[global_state.mstate.pc]
        if instr['opcode'] in ["STOP", "RETURN"]:
            print(instr)
        ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[0] == instr]
        if not ignore_tuples and instructions[global_state.mstate.pc - 1]['opcode'] == 'JUMPDEST':
            print("Handle pre jumpdest")
            jumpdest_istr = instructions[global_state.mstate.pc - 1]
            ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[0] == jumpdest_istr]
        if ignore_tuples:
            if hasattr(global_state, 'saved_state'): # Skip
                print("Skip")
                ign_exit_istr = ignore_tuples[0][1]
                istr_idx = instructions.index(ign_exit_istr)
                global_state.mstate.pc = istr_idx + 1
            else: # Save
                print("Save")
                helper_state_ref = global_state
                global_state = deepcopy(helper_state_ref)
                global_state.saved_state = helper_state_ref
                global_state.id = self.state_ctr
                self.state_ctr += 1

        ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[2] == instr]
        if ignore_tuples: # violation
            self.violations[self.ignore_list.index(ignore_tuples[0])].append(deepcopy(global_state))

        return global_state

    def postprocess(self, global_state, new_global_states):
        # Had to be added, because treatment of a single instruction does not carry over added attributes
        if hasattr(global_state, 'saved_state'): # Carry
            print("carry")
            for new_state in new_global_states:
                new_state.saved_state = global_state.saved_state
                new_state.id = global_state.id
        else:
            print("Nothing to carry")

        for state_idx in range(len(new_global_states)):
            new_state = new_global_states[state_idx]
            instr = self.instructions[global_state.mstate.pc]
            ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[1] == instr]
            if not ignore_tuples and self.instructions[new_state.mstate.pc - 1]['opcode'] == 'JUMPDEST':
                jumpdest_istr = self.instructions[new_state.mstate.pc - 1] # exit if jumpdest is exit
                ignore_tuples = [ign_tuple for ign_tuple in self.ignore_list if ign_tuple[1] == jumpdest_istr]
            if ignore_tuples:
                if hasattr(new_state, 'saved_state'):
                    if new_state.id in self.restored_ids: # Dont recover if already done
                        print("Dont recover")
                        new_global_states[state_idx] = None
                    else: # Recover saved state on exit
                        print("Recover")
                        new_global_states[state_idx] = new_state.saved_state
                        new_global_states[state_idx].mstate.pc = new_state.mstate.pc
                        self.restored_ids.append(new_state.id)
                else:
                    raise RuntimeError("No saved global state at encounter of exit instruction. This should not happen")

            new_global_states = list(filter(lambda state: state is not None, new_global_states))

        return new_global_states


