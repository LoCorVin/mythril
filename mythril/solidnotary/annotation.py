from enum import Enum
from re import match
from functools import reduce
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


def init_annotation(contract, code, head, kw, start, end):
    if kw == "check":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return CheckAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin_pos_line_col(code[:start]))
    elif kw == "invariant":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return InvariantAnnotation(contract, code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin_pos_line_col(code[:start]))
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
                    ano_rewriting.col += rewriting.text[::-1].index(nwl_type[::-1])
                else:
                    ano_rewriting.col += len(rewriting.text)

def is_mapping_inside_rew(mapping, rewriting):
    return is_mapping_inside_range(mapping, rewriting.pos, rewriting.pos + len(rewriting.text))

def is_mapping_inside_range(mapping, start_pos, end_pos):
    # mapping.lineno == rewriting.line and
    return mapping.offset >= start_pos and mapping.offset < end_pos and mapping.length + mapping.offset <= end_pos


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

        # Todo These may not be necessary for the rest of the execution as enter, exit and violating instr. define enough
        self.viol_rew_instrs = [] # list of instructions lists that are associated to the rewriting in the same position

        self.viol_inst = [] # Single instruction that triggers the violation through 'ASSERT_FAIL'
        self.exit_inst = [] # Single instruction that marks end of the violation rewriting, currently a 'JUMPDEST'
        self.enter_inst = [] # First instruction associated to the rewriting in the same position to save state an be ignored

        self.viol_rts = [] #

        self.anotation_contract = None

    def rewrite_code(self, code): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def set_annotation_contract(self, annotation_contract):
        self.annotation_contract = annotation_contract
        self.build_instruction_lists()

    def build_instruction_lists(self):

        for v_rewriting in self.viol_rews:
            rewriting_rt = "" # Set when first associated instruction is found in constructor or transaction code
            rewriting = get_editor_indexed_rewriting(v_rewriting)
            rew_asm = []
            viol_instr, exit_instr, enter_instr = None, None, None
            if rewriting_rt != 'c':
                for m_idx in range(len(self.annotation_contract.mappings)):
                    mapping = self.annotation_contract.mappings[m_idx]

                    if is_mapping_inside_rew(mapping, rewriting):
                        instr = self.annotation_contract.disassembly.instruction_list[m_idx]
                        rew_asm.append(instr)
                        if not enter_instr:
                            enter_instr = instr
                            instr['is'] = "Enter"
                            rewriting_rt = 't'

                        if instr['opcode'] == 'ASSERT_FAIL':
                            instr['line'] = mapping.lineno
                            viol_instr = instr
                            instr['is'] = "Violation"

                        if 'is' not in instr:
                            instr['is'] = 'Ignore'

            if rewriting_rt != 't':
                for m_idx in range(len(self.annotation_contract.creation_mappings)):
                    mapping = self.annotation_contract.creation_mappings[m_idx]

                    if is_mapping_inside_rew(mapping, rewriting):
                        instr = self.annotation_contract.creation_disassembly.instruction_list[m_idx]
                        rew_asm.append(instr)
                        if not enter_instr:
                            enter_instr = instr
                            instr['is'] = "Enter"
                            rewriting_rt = 'c'

                        if instr['opcode'] == 'ASSERT_FAIL':
                            instr['line'] = mapping.lineno
                            viol_instr = instr
                            instr['is'] = "Violation"

                        if 'is' not in instr:
                            instr['is'] = 'Ignore'

            if rew_asm:
                exit_instr = reduce(lambda x, y: y if y['address'] > x['address'] else x, rew_asm)
                exit_instr['is'] = 'Exit'

            self.viol_rew_instrs.append(rew_asm)

            self.viol_inst.append(viol_instr)
            self.exit_inst.append(exit_instr)
            self.enter_inst.append(enter_instr)

            self.viol_rts.append(rewriting_rt)
        print()

    def set_violations(self, violations, src_mapping): # Ads new violations to this annotation and sets the status, can be called multiple times
        self.violations.extend([(violation, src_mapping) for violation in violations])
        self.status = Status.VSINGLE if self.violations else Status.HOLDS

    def get_creation_ignore_list(self):
        return [(val0, val1, val2, val3, self) for val0, val1, val2, val3, val4 in list(zip(self.enter_inst, self.exit_inst, self.viol_inst, self.viol_rew_instrs, self.viol_rts)) if val4 == 'c']

    def get_trans_ignore_list(self):
        return [(val0, val1, val2, val3, self) for val0, val1, val2, val3, val4 in list(zip(self.enter_inst, self.exit_inst, self.viol_inst, self.viol_rew_instrs, self.viol_rts)) if val4 == 't']

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

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

class InvariantAnnotation(Annotation):
    def __init__(self, contract, annotation_str, loc, origin_loc):
        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc

        self.rewritings = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        if not hasattr(contract, 'functions'):
            raise RuntimeError("Contract not augmented with functions parsed from ast")
        self.functions = contract.functions

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        assertion_text = "assert(" + self.content + ");"
        for function in self.functions:
            for term_pos in function.terminating_pos:

                assertion_rew = expand_rew(code, (assertion_text, term_pos[0]))
                if after_implicit_block(code, term_pos[0]):
                    start, end = get_exp_block_brack_pos(code, term_pos[0])

                    self.rewritings.append(expand_rew(code, ("{", start)))
                    self.rewritings.append(expand_rew(code, ("}", end)))

                if term_pos[1] > 0:
                    ret_end = term_pos[0] + term_pos[1]
                    if not code[:ret_end].strip().endswith(';'):
                        inc_pos = code[ret_end:].index(";") + 1
                        ret_end += inc_pos
                    return_content = code[term_pos[0]:ret_end]
                    if return_content.startswith("return"):
                        return_content = return_content[len("return"):].strip()
                    if return_content.endswith(';'):
                        return_content = return_content[:len(return_content) - 1].strip()
                    if return_content:
                        ret_var = "("
                        for ret_idx in range(len(function.return_types)):
                            ret_var += "sol_retvar_" + str(term_pos[0]) + "_" + str(ret_idx) + ","
                        ret_var = ret_var[:len(ret_var)-1] + ")"

                        self.rewritings.append(expand_rew(code, ("var " + ret_var + "="+return_content+";", term_pos[0])))
                        self.rewritings.append(assertion_rew)
                        self.rewritings.append(expand_rew(code, ("return " + ret_var + "; /*", term_pos[0])))
                        self.rewritings.append(expand_rew(code, ("*/", ret_end)))
                    else:
                        self.rewritings.append(assertion_rew)
                else:
                    self.rewritings.append(assertion_rew)
                self.viol_rews.append(assertion_rew)

        return self.rewritings





    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

