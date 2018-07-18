from .annotation import annotation_kw, ANNOTATION_START, ANNOTATION_START_REPLACEMENT
from re import finditer, escape, DOTALL
from re import findall, sub


newlines = ["\r\n", "\r", "\n"]



def get_code(filename):
    with open(filename, 'r') as file:
        return file.read()

def write_code(filename, code):
    with open(filename, 'w') as file:
        file.write(code)

def get_lines(filename):
    lines = []
    with open(filename) as file:
        lines= file.readlines()
    return lines


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



def substr_first(string, subs1, subs2):
    if subs1 in string and subs2 in string:
        return subs1 if string.index(subs1) < string.index(subs2) else subs2
    elif subs1 in string:
        return subs1
    elif subs2 in string:
        return subs2
    return None

def current_line_contains(string, sub):
    if sub not in string:
        return False
    newline_idx = len(string)
    for newline in newlines:
        if newline in string:
            newline_idx = min(newline_idx, string.index(newline))
    if newline_idx == len(string):
        return True
    return string.index(sub) <= newline_idx

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



def after_implicit_block(code, idx):
    code = code[:idx][::-1]

    impb_idx = next(finditer(r'(esle|fi|elihw)', code), None)
    no_impb_idx = next(finditer(r';|}|{', code), None)

    if not impb_idx:
        return False

    if no_impb_idx and no_impb_idx.start() < no_impb_idx.start():
        return False
    return True

with open("comment_test.sol", 'r') as file:
    code = file.read()
print(replace_comments_with_whitespace(code))
