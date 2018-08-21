
def get_last_child(obj):
    if type(obj) == dict:
        return obj['children'][-1]
    raise RuntimeError("No children to retrieve the last one")

def is_last_stmt_a_return(f_def):
    block = None
    for child in f_def['children']:
        if 'name' in child and child['name'] == 'Block':
            block = child
    if not block:
        raise RuntimeError("Function has no block in ast")
    last_child = get_last_child(block)
    return last_child['name'] == 'Return'


def get_dict_containing_k(obj, key):
    pairs = []
    if type(obj) == dict:
        if key in obj:
            pairs.extend((key, obj[key]))
        for k, v in obj.items():
            pairs.extend(get_dict_containing_k(v, key))
    elif type(obj) == list:
        for elem in obj:
            pairs.extend(get_dict_containing_k(elem, key))
    return pairs

"""
    If dictionary with specified key, value pair can contain a dict with the key, value pair this nested dict is 
    returned to. Removing the specified line avoids this
"""
def get_all_nested_dicts_with_kv_pairs(obj, key, value):
    dicts = []
    if type(obj) == dict:
        for k, v in obj.items():
            if k == key and v == value:
                dicts.append(obj)
            dicts.extend(get_all_nested_dicts_with_kv_pairs(v, key, value))
    elif type(obj) == list:
        for elem in obj:
            dicts.extend(get_all_nested_dicts_with_kv_pairs(elem, key, value))
    return dicts

def get_contract_ast(ast, contract_name):
    contract_asts = get_all_nested_dicts_with_kv_pairs(ast, "name", "ContractDefinition")
    try:
        return list(filter(lambda c_ast: c_ast['attributes']['name'] == contract_name, contract_asts))[0]
    except KeyError:
        return None

def get_function_asts(contract_ast):
    return get_all_nested_dicts_with_kv_pairs(contract_ast, "name", "FunctionDefinition")

def get_function_term_positions(f_ast):
    terminating_pos = []
    returns = get_all_nested_dicts_with_kv_pairs(f_ast, "name", "Return")
    for ret in returns:
        pos_r = ret['src'].split(':')
        terminating_pos.append((int(pos_r[0]), int(pos_r[1])))
    return_types = []
    if returns:
        # Finds return stmt and the id of the element holding the type information
        ret_param_id = returns[0]['attributes']['functionReturnParameters']
        # finds the subelement holding the information on the return param types
        return_params = get_all_nested_dicts_with_kv_pairs(f_ast, 'id', ret_param_id)[0]
        for child in return_params['children']:
            if child['attributes']['type']:
                return_types.append(child['attributes']['type'])

    # Uses src attribute to find position in file
    pos = f_ast['src'].split(':')
    if not is_last_stmt_a_return(f_ast):
        terminating_pos.append((int(pos[0]) + int(pos[1]) - 1, 0))
    return return_types, terminating_pos

def get_function_param_tuples(f_ast):
    parameter_list = get_all_nested_dicts_with_kv_pairs(f_ast['children'], 'name', 'ParameterList')[0]
    params = ""
    param_tpls = []
    for param in parameter_list['children']:
        param_tpls.append((param['attributes']['name'], param['attributes']['type']))
        params += param['attributes']['type'] + ","
    return param_tpls

def get_contract_storage_members(contract_ast):
    return get_all_nested_dicts_with_kv_pairs(contract_ast, 'stateVariable', True)