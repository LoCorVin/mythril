from re import search
from enum import Enum
from re import match
from .codeparser import find_matching_closed_bracket, get_pos_line_col
from .coderewriter import expand_rew, after_implicit_block, get_exp_block_brack_pos, get_editor_indexed_rewriting



ANNOTATION_START = "@"
ANNOTATION_START_REPLACEMENT = "//@"
annotation_kw = ["check", "invariant", "construction", "ethersink", "ethersource"]


def comment_out_annotations(filename):
    with open(filename, 'r') as file:
        filedata = file.read()
    for kw in annotation_kw:
        filedata = filedata.replace(ANNOTATION_START + kw, ANNOTATION_START_REPLACEMENT + kw)

    with open(filename, 'w') as file:
        file.write(filedata)

def recomment_annotations(filename):
    with open(filename, 'r') as file:
        filedata = file.read()

    for kw in annotation_kw:
        filedata = filedata.replace(ANNOTATION_START_REPLACEMENT + kw, ANNOTATION_START + kw)

    with open(filename, 'w') as file:
        file.write(filedata)

def get_origin_pos_line_col(text):
    return get_pos_line_col(text.replace(ANNOTATION_START_REPLACEMENT, ANNOTATION_START))

def get_annotation_content(code, content_start):
    match_annotation_start = match(r'\s*\(', code[content_start:])
    if not match_annotation_start:
        raise SyntaxError("Annotation needs to be properly defined within (...)")
    m_string = match_annotation_start.group()
    closed_idx = find_matching_closed_bracket(code, content_start + len(m_string) - 1)
    return code[(content_start + len(m_string)):closed_idx], len(m_string)


def init_annotation(code, head, kw, start, end):
    if kw == "check":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return CheckAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin_pos_line_col(code[:start]))
    elif kw == "invariant":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return InvariantAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin_pos_line_col(code[:start]))
    elif kw == "construction":
        pass

    elif kw == "ethersink":
        pass

    elif kw == "ethersource":
        pass

def increase_rewritten_pos(ano_rewritings, rewriting, nwl_type="\n"):
    for ano_rewriting in ano_rewritings:
        nr_nwl = rewriting.text.count(nwl_type)
        if ano_rewriting != rewriting and ano_rewriting.pos >= rewriting.pos:
            ano_rewriting.line += nr_nwl
            ano_rewriting.pos += len( rewriting.text)
            if not ano_rewriting.text.endswith(nwl_type) and ano_rewriting.line == rewriting.line:
                if nwl_type in ano_rewriting.text:
                    ano_rewriting.pos += ano_rewriting.text[::-1].index(nwl_type[::-1])
                else:
                    ano_rewriting.pos += len(ano_rewriting.text)


class Status(Enum):
    HOLDS = 1
    UNCHECKED = 2
    VSINGLE = 3
    VDEPTH = 4
    VCHAIN = 5

class Annotation:

    def __init__(self, annotation_str, status=Status.UNCHECKED):
        self.status = status
        self.annotation_str = annotation_str
        self.violations = [] # Filled when executing scheck_single_transactions

        self.viol_rews = [] # List of rewritings that contain code to be traceless in the symbolic execution
        self.viol_rew_instrs = [] # list of instructions lists that are associated to the rewriting in the same position
        self.viol_inst = [] # Single instruction that triggers the violation through 'ASSERT_FAIL'
        self.exit_inst = [] # Single instruction that marks end of the violation rewriting, currently a 'JUMPDEST'

        self.anotation_contract = None

    def rewrite_code(self, code): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def set_anotation_contract(self, anotation_contract):
        self.anotation_contract = anotation_contract
        self.build_instruction_lists()

    def build_instruction_lists(self):

        for v_rewriting in self.viol_rews:
            rewriting = get_editor_indexed_rewriting(v_rewriting)
            rew_asm = []
            viol_instr, exit_instr = None, None
            for m_idx in range(len(self.anotation_contract.mappings)):
                mapping = self.anotation_contract.mappings[m_idx]
                if mapping.lineno == rewriting.line and mapping.offset >= rewriting.pos and mapping.length <= len(rewriting.text):
                    instr = self.anotation_contract.disassembly.instruction_list[m_idx]
                    rew_asm.append(instr)
                    print(instr['opcode'])
                    if instr['opcode'] == 'JUMPDEST':
                        exit_instr = instr
                    elif instr['opcode'] == 'ASSERT_FAIL':
                        viol_instr = instr

            for m_idx in range(len(self.anotation_contract.creation_mappings)):
                mapping = self.anotation_contract.creation_mappings[m_idx]
                if mapping.lineno == rewriting.line and mapping.offset >= rewriting.pos and mapping.length <= len(rewriting.text):
                    instr = self.anotation_contract.disassembly.instruction_list[m_idx]
                    rew_asm.append(instr)
                    print(instr['opcode'])
                    if instr['opcode'] == 'JUMPDEST':
                        exit_instr = instr
                    elif instr['opcode'] == 'ASSERT_FAIL':
                        viol_instr = instr

            self.viol_rew_instrs.append(rew_asm)

            self.viol_inst.append(viol_instr)
            self.exit_inst.append(exit_instr)



    def get_rewritten_loc(self):
        if hasattr(self, "rewritten_loc"):
            return self.rewritten_loc
        return []

    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

#    def __init__(self, annstring, lineno, fileoffset):
#        self.annstring = annstring
#
#        annotation = search(r'@(?P<aname>[^\{\}]*)(\{(?P<acontent>.*)\})?', annstring)
#        if not annotation:
#            raise SyntaxError("{} is not a correct annotation".format(annstring))
#
#        self.aname = annotation['aname']
#        self.acontent = annotation['acontent']
#        self.lineno = lineno
#        self.length = len(annstring)
#        self.fileoffset = fileoffset

class CheckAnnotation(Annotation):

    def __init__(self, annotation_str, loc, origin_loc):
        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc # Has to be calculated before
        self.rewritings = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        assert_rew = expand_rew(code, ("assert(" + self.content + ");", self.loc[0]))
        if after_implicit_block(code, self.loc[0]):
            start, end = get_exp_block_brack_pos(code, self.loc[0])
            self.rewritings.append(expand_rew(code, ("{", start)))
            self.rewritings.append(assert_rew)
            self.rewritings.append(expand_rew(code, ("}", end)))
        else:
            self.rewritings.append(assert_rew)

        self.viol_rews.append(assert_rew)
        return self.rewritings

    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

class InvariantAnnotation(Annotation):
    def __init__(self, annotation_str, loc, origin_loc):
        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc

        self.rewritings = []

        self.violation_rew = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        return []

    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

