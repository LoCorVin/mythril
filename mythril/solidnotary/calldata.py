from re import findall,search, escape, finditer
from mythril.exceptions import CompilerError
from subprocess import Popen, PIPE
from .codeparser import find_matching_closed_bracket
import json
import sys

class CalldataMap:

    def __init__(self, abi, solc_v):
        pass

    def __init__(self, solidity_file, solc_v):
        pass

def get_minimal_byte_enc_len(abi_obj):
    if type(abi_obj) == list:
        return sum([head_byte_length_min(t) for t in abi_obj]) + sum([tail_byte_length_min(t) for t in abi_obj])
    if type(abi_obj) == str:
        stype = abi_obj
    else:
        stype = abi_obj['type']
    if stype == 'tuple':
        return get_minimal_byte_enc_len(abi_obj['components'])
    try:
        match = search(r'(?P<pre>.*)\[(?P<post>[0-9]+)\]', stype)
        pre = match['pre']
        post = match['post']
        return int(post) * get_minimal_byte_enc_len(pre)
    except (KeyError, TypeError) as e:
        pass
    if stype.endswith("[]"):
        return 32

    if stype == "string":
        return 32
    elif stype == "bytes":
        return 32 # 2 was the smallest observed value, remix did not allow specification of zero size bytes
    elif [stype.startswith(prefix_type) for prefix_type in ["int", "uint", "address", "bool", "fixed", "ufixed", "bytes"]]:
        return 32

def head_byte_length_min(abi_obj):
    if is_dynamic(abi_obj):
        return 32
    else:
        return get_minimal_byte_enc_len(abi_obj)


def tail_byte_length_min(abi_obj):
    if is_dynamic(abi_obj):
        return get_minimal_byte_enc_len(abi_obj)
    else:
        return 0

def get_minimal_wsize(abi_obj):
    stype = abi_obj['type']
    if type(stype) == list:
        return sum(list(map(lambda a: get_minimal_wsize(a), stype)))
    if stype in ["bytes", "string"] or stype.endswith("[]"):
        return True
    if stype == 'tuple':
        return True in [is_dynamic(elem) for elem in abi_obj['components']]
    try:
        match = search(r'(?P<pre>.*)(?P<post>\[[0-9]+\])', stype)
        pre = match['pre']
        # post = match['post']
        return is_dynamic(pre)
    except (KeyError | TypeError):
        pass
    return False


def get_minimal_constructor_param_encoding_len(abi):
    for spec in abi:
        try:
            if spec['type'] == 'constructor':
                con_inputs = spec['inputs']
                return get_minimal_byte_enc_len(con_inputs)
        except KeyError:
            print("ABI does not contain inputs for constructor")
    return -1

def get_calldata_name_map(abi):
    calldata_mappings = {}
    for spec in abi:
        try:
            if spec['type'] == 'function' or spec['type'] == 'constructor':
                signature = ''
                if spec['type'] == 'function':
                    signature = spec['name']
                signature += "("
                for input in spec['inputs']:
                    signature += input['type'] + ","
                if signature.endswith(","):
                    signature = signature[:len(signature) - 1]
                signature += ")"
                calldata_mappings[signature] = get_params_name_map(spec['inputs']) # not just name but also signature
        except KeyError:
            print("ABI does not contain inputs for " + spec['type'] + "" if 'name' not in spec else (": " + spec['name']))
    return calldata_mappings

def get_minimal_constr_param_byte_length(filename, contract_name=None):
    abi_decoded = get_solc_abi_json(filename)
    return get_minimal_constructor_param_encoding_len(abi_decoded)

def is_dynamic(abi_obj):
    if type(abi_obj) == list:
        return True in list(map(lambda a: is_dynamic(a), abi_obj))
    if type(abi_obj) == str:
        stype = abi_obj
    else:
        stype = abi_obj['type']
    if stype in ["bytes", "string"] or stype.endswith("[]"):
        return True
    if stype == 'tuple':
        return True in [is_dynamic(elem) for elem in abi_obj['components']]
    try:
        match = search(r'(?P<pre>.*)(?P<post>\[[0-9]+\])', stype)
        pre = match['pre']
        # post = match['post']
        return is_dynamic(pre)
    except (KeyError, TypeError) as e:
        pass
    return False

def get_solc_abi_json(file, solc_binary="solc", solc_args=None):

    cmd = [solc_binary, "--abi", '--allow-paths', "."]

    if solc_args:
        cmd.extend(solc_args.split(" "))

    cmd.append(file)

    try:
        p = Popen(cmd, stdout=PIPE, stderr=PIPE)

        stdout, stderr = p.communicate()
        ret = p.returncode

        if ret != 0:
            raise CompilerError("Solc experienced a fatal error (code %d).\n\n%s" % (ret, stderr.decode('UTF-8')))
    except FileNotFoundError:
        raise CompilerError("Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable.")

    out = stdout.decode("UTF-8")

    if not len(out):
        raise CompilerError("Compilation failed.")

    out = out[out.index("["):]

    print(out)

    return json.loads(out)

def flatten(to_flatten):
    return [item for sublist in to_flatten for item in sublist]

def get_params_name_map(abi_obj):
    if type(abi_obj) == list:
        param_map = flatten([head_params_name_map(t) for t in abi_obj])
        param_map.extend(flatten([tail_params_name_map(t) for t in abi_obj]))
        return param_map
    if type(abi_obj) == str:
        stype = abi_obj
    else:
        stype = abi_obj['type']
        # add names
    if stype == 'tuple':
        return get_params_name_map(abi_obj['components'])
    try:
        match = search(r'(?P<pre>.*)\[(?P<post>[0-9]+)\]', stype)
        pre = match['pre']
        post = match['post']
        param_namings = get_params_name_map(pre)
        return [(elem[0] + "[" + idx +"]", elem[1]) for idx, elem in enumerate(int(post)*param_namings)]
    except (KeyError, TypeError) as e:
        pass
    if stype.endswith("[]"):
        return [(abi_obj['name'] + "_length", 32)]

    if stype == "string": # adapt
        return [(abi_obj['name'] + "_length", 32)]
    elif stype == "bytes": # adapt
        return [(abi_obj['name'] + "_length", 32)]
    elif [stype.startswith(prefix_type) for prefix_type in ["int", "uint", "address", "bool", "fixed", "ufixed", "bytes"]]: # bytes or byte ??
        return [(abi_obj['name'], 32)]

def head_params_name_map(abi_obj):
    if is_dynamic(abi_obj):
        return [(abi_obj['name'] + "_offset", 32)]
    else:
        return get_params_name_map(abi_obj)


def tail_params_name_map(abi_obj):
    if is_dynamic(abi_obj):
        return get_params_name_map(abi_obj)
    else:
        return []

"""
    Simple mapping from byte-size idx in calldata to variable names. Constraints have to be considered for access but 
    might not be enough. regex that searches for calldata[ ... param_offset] could do the trick. 
"""
def calldata_to_param_map(contract_name, calldata_string, calldata_mapping):
    results = findall(r'calldata_' + escape(contract_name) +r'(?P<idx>\[[0-9]+\])', calldata_string)
    idx = int(results['idx'])

    for map_slice in calldata_mapping:
        name = map_slice[0]
        size = map_slice[1]
        if idx <= size:
            return name, idx
    return None



"""
    Constraints are used to identify the right function.
"""
def map_symbolic_vars_to_names(sym_var, contract, calldata_mapping, is_constructor):
    mem_string = "mem["
    call_string = "calldata_" + contract.name + "["
    storage_string = "storage["
    open_bracket = sym_var.index("[")
    closing_bracket = find_matching_closed_bracket(sym_var, open_bracket)
    content = sym_var[(open_bracket + 1):closing_bracket]
    try:
        int(content)
        return calldata_to_param_map(contract.name, sym_var, calldata_mapping)
    except ValueError:
        pass

    if sym_var.startswith(mem_string) and is_constructor:
        const_offset = int(content[:content.index("+")])
        if const_offset < 128:
            # Todo If the function has a hash, this hash is in the first 4 bytes of the calldata, meaning that
            # Todo we have to take that into account as well
            raise RuntimeError("Loading calldata from memory starts at byte 128: " + str(content))
        const_offset -= 128
    found_calldata = finditer(escape(call_string), content)
    possible_offset = next(found_calldata, None)
    while possible_offset:
        start = possible_offset.start()
        end = find_matching_closed_bracket(content, possible_offset.end() - 1)
        if not content[:start].trim().endswith("*") and not content[:end].trim().startswith("*"):
            offset = content[start:(end + 1)]
        possible_offset = next(found_calldata, None)

    return



def abi_json_to_abi(abi_json):
    return json.loads(abi_json)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        print("Size:")
        print(get_minimal_constr_param_byte_length(sys.argv[1]))
    else:
        print("Error: No file specified")
