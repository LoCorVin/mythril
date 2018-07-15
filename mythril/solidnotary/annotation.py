from re import search
from enum import Enum

class Status(Enum):
    HOLDS = 1
    UNCHECKED = 2
    VSINGLE = 3
    VDEPTH = 4
    VCHAIN = 5

class Annotation:

    def __init__(self, info, status=Status.UNCHECKED):
        self.status = status
        self.info = info
        self.violations = [] # Filled when executing scheck_single_transactions

    def parse_annotation(self, annotation_string, linenr): # returns two strings, the parsed annotation and the replacementstring
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_rewriting_string(self): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
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
    def __init__(self, info, status=Status.UNCHECKED):
        self.status = status
        self.info = info
        self.violations = [] # Filled when executing scheck_single_transactions

    def parse_annotation(self, annotation_string, linenr): # returns two strings, the parsed annotation and the replacementstring
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_rewriting_string(self): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def build_violations(self, sym_myth):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

class InvariantAnnotation(Annotation):
    pass

