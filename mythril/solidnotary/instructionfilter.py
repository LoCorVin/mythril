class InstructionFilter:

    def __init__(self):
        self.saved_glb_state = None
        self.restored = True # Set to false when entering a new

        self.enter_inst = []
        self.exit_inst = []

        self.annotation_final_state = [] # Maybe fill them in here

    def add_annotation(self, enter_exit_tuple):
        self.enter_inst.append(enter_exit_tuple[0])
        self.exit_inst.append(enter_exit_tuple[1])

    def pre_filter(self, glb_state):
        # instruction = glb_state.get_current_instruction()
        # if glb_state.mstate.pc
        return glb_state

    def post_filter(self, glb_state):
        return glb_state
