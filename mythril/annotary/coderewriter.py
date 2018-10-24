from re import finditer, escape, DOTALL
from re import sub
from mythril.annotary.codeparser import find_matching_closed_bracket, get_newlinetype



class Rewriting:

    def __init__(self, text, pos, line, col):
        self.text = text
        self.pos = pos
        self.line = line
        self.col = col

    def __eq__(self, other):
        if isinstance(other, Rewriting):
            return self.text == other.text and self.pos == other.pos and self.line == other.line and self.col == other.col
        return NotImplemented


def apply_rewriting(code, rewriting):
    return code[:rewriting.pos] + rewriting.text + code[rewriting.pos:]



def get_line_count(text):
    return text.count(get_newlinetype(text))

def expand_rew(code, rew_tuple):
    pos = rew_tuple[1]
    nr_nwls = code[:pos].count(get_newlinetype(code))
    if get_newlinetype(code) in code[:pos]:
        col = code[:pos][::-1].index(get_newlinetype(code)[::1])
    else:
        col = pos
    return Rewriting(rew_tuple[0], pos, nr_nwls, col)

def get_editor_indexed_rewriting(rewriting):
    return Rewriting(rewriting.text, rewriting.pos, rewriting.line + 1, rewriting.col)

def get_code(filename):
    with open(filename, 'r', encoding="utf-8") as file:
        return file.read()

def write_code(filename, code):
    with open(filename, 'w', encoding="utf-8") as file:
        file.write(code)

def get_lines(filename):
    lines = []
    with open(filename, encoding="utf-8") as file:
        lines= file.readlines()
    return lines

def substr_first(string, subs1, subs2):
    if subs1 in string and subs2 in string:
        return subs1 if string.index(subs1) < string.index(subs2) else subs2
    elif subs1 in string:
        return subs1
    elif subs2 in string:
        return subs2
    return None

#def current_line_contains(string, sub):
#    if sub not in string:
#        return False
#    newline_idx = len(string)
#    for newline in newlines:
#        if newline in string:
#            newline_idx = min(newline_idx, string.index(newline))
#    if newline_idx == len(string):
#        return True
#    return string.index(sub) <= newline_idx



def remove_solidity_comments(code):
    code = sub(escape('/*') + r'(.*?)\*/', r"", code, flags=DOTALL)
    code = sub(escape('//') + r'(.*?)\r\n', r"\r\n", code, flags=DOTALL)
    code = sub(escape('//') + r'(.*?)\n', r"\n", code, flags=DOTALL)
    code = sub(escape('//') + r'(.*?)\r', r"\r", code, flags=DOTALL)
    return code

def replace_regex_with_whitespace(regex, code):
    matches = finditer(regex, code, flags=DOTALL)
    match = next(matches, None)
    while match:
        to_rpl = match.group()
        rpl = " " * len(to_rpl)
        nwls = finditer(r'\r\n|\n|\r', to_rpl)
        nwl = next(nwls, None)
        while nwl:
            rpl = rpl[:nwl.start()] + nwl.group() + rpl[nwl.end():]
            nwl = next(nwls, None)
        code = code[:match.start()] + rpl + code[match.end():]
        match = next(matches, None)
    return code


def replace_comments_with_whitespace(code):
    code = replace_regex_with_whitespace(escape('/*') + r'(.*?)' + escape('*/'), code)
    code = replace_regex_with_whitespace(escape('//') + '(.*?)(\r\n|\n|\r)', code)
    return code



def after_implicit_block(origin_code, idx):
    code = origin_code[:idx][::-1]
    # although this is used after eliminating the original comments, commented out annotations could in theory hold this kws
    impb_idx = next(finditer(r'(esle|fi|elihw)', code), None)
    no_impb_idx = next(finditer(r';|}|{', code), None)

    if not impb_idx:
        return False

    impb_idx_pos = impb_idx.start()
    if no_impb_idx and no_impb_idx.start() < impb_idx_pos:
        return False
    if impb_idx.group() != 'esle':
        real_pos = len(origin_code) - impb_idx_pos - (len(origin_code) - idx)
        brack_pos = next(finditer(r'\s*\(', origin_code[real_pos:]), None)
        tmp = origin_code[real_pos:]
        tmp2 = origin_code[:real_pos]
        if not brack_pos:
            raise SyntaxError(impb_idx.group()[::-1] + " needs following (...)")
        real_pos = real_pos + brack_pos.end() - 1
        real_pos = find_matching_closed_bracket(origin_code, real_pos)
        impb_idx_pos = len(origin_code) - real_pos

        # if one that needs () get end of ()


    return True

def get_exp_block_brack_pos(origin_code, idx):
    origin_code = replace_comments_with_whitespace(origin_code)
    code = origin_code[:idx][::-1]
    start, stop = None, None
    # although this is used after eliminating the original comments, commented out annotations could in theory hold this kws
    impb_idx = next(finditer(r'(esle|fi|rof|elihw)', code), None)

    if impb_idx.group() == 'esle':
        start = len(code) - impb_idx.start()
    else:
        code = origin_code[(idx - impb_idx.start()):]
        brack_pos = next(finditer(r'\s*\(', code), None)
        brack_pos = find_matching_closed_bracket(origin_code, brack_pos.end() - 1 + idx - impb_idx.start())
        start = brack_pos + 1

    iter_idx = start
    while iter_idx < len(origin_code):
        if origin_code[iter_idx] in ["(", "[", "{"]:
            iter_idx = find_matching_closed_bracket(origin_code, iter_idx)
        if origin_code[iter_idx] in ["}", ";"]:
            end = iter_idx + 1
            break
        iter_idx += 1

    return start, end
