from re import search
from enum import Enum
from re import match
from .codeparser import find_matching_closed_bracket, get_pos_line_col



ANNOTATION_START = "@"
ANNOTATION_START_REPLACEMENT = "//@"
annotation_kw = ["check", "invariant", "construction", "ethersink", "ethersource"]


def get_origin__pos_line_col(text):
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
        return CheckAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin__pos_line_col(code[:start]))
    elif kw == "invariant":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return InvariantAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), get_origin__pos_line_col(code[:start]))
    elif kw == "construction":
        pass

    elif kw == "ethersink":
        pass

    elif kw == "ethersource":
        pass


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

    def rewrite_code(self, code): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        raise NotImplementedError("Abstract function of Annotation abstraction")

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

    code_const_pair = ("block.")

    def __init__(self, annotation_str, loc, origin_loc):
        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        return code

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

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        return code

    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

