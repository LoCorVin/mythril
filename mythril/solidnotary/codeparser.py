from re import findall

opening_brackets = ["(", "{", "[", "<"]
closing_brackets = [")", "}", "]", ">"]

newlines_reg = r'(\r\n|\r|\n)'
newlines = ['\r\n', '\r', '\n']

#def parse_contract(contract):


    # Todo return a list of tuples with function name, bracket positions and ranges

#def in_function(code):
#    pass

def count_lines(text):
    if text == "":
        return 0
    return 1 + len(findall(newlines_reg, text))

def get_pos_line_col(text):
    return len(text), len(findall(newlines_reg, text)), min(map(lambda nwl: text[::-1].index(nwl) if nwl in text else len(text), newlines))

def find_matching_closed_bracket(filedata, bracket_idx):
    nwl = get_newlinetype(filedata)
    bracket = filedata[bracket_idx]
    opening_bracket = filedata[bracket_idx] in opening_brackets

    if opening_bracket:
        to_search = filedata[bracket_idx:]
    else:
        to_search = filedata[:(bracket_idx + 1)][::-1]
    matching_bracket = closing_brackets[opening_brackets.index(bracket)] if opening_bracket \
        else closing_brackets[opening_brackets.index(bracket)]
    idx = 0
    counter = 0
    while True:
        if opening_bracket and to_search[idx:].startswith("//"):
            idx = idx + to_search[idx:].index(nwl) + len(nwl)
        if not opening_bracket and to_search[idx].startswith(nwl[::-1]):
            inc_idx = 0
            current_inv_line = to_search[(idx + len(nwl)):]
            if nwl[::-1] in current_inv_line:
                current_inv_line = current_inv_line[:current_inv_line.index(nwl[::-1])]
            if "//" in current_inv_line:
                inc_idx += len(nwl) + current_inv_line.index(nwl[::-1]) + len("//")
            idx += inc_idx
        if to_search[idx] == bracket:
            counter += 1
        elif to_search[idx] == matching_bracket:
            counter -= 1
        if counter <= 0:
            break
        idx += 1

    return bracket_idx + (idx if opening_bracket else -idx)

def get_newlinetype(text):
    nwl = "\n"
    for newline in newlines:
        if newline in text:
            nwl = newline
            break
    return nwl

def current_line_contains(string, sub):
    nwl = get_newlinetype(string)
    string = string[(string.rfind(nwl) + len(nwl)):]
    return sub in string

def is_commented_out(code, pos):
    return current_line_contains(code[:pos], "//")
