
def get_last_child(obj):
    if type(obj) == dict:
        if len(obj['children']):
            return obj['children'][-1]
        else:
            return None
    raise RuntimeError("No children to retrieve the last one")

def is_last_stmt_a_return(f_def):
    block = None
    for child in f_def['children']:
        if 'name' in child and child['name'] == 'Block':
            block = child
    if not block:
        raise RuntimeError("Function has no block in ast")
    last_child = get_last_child(block)
    return last_child and last_child['name'] == 'Return'


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

def get_all_functions_for_contract(contract):
    contract_asts = []
    for file in contract.solidity_files:
        contract_asts.extend(get_all_nested_dicts_with_kv_pairs(file.ast, "name", "ContractDefinition"))
    main_contract_ast = contract.ast if hasattr(contract, "ast") else None
    if not main_contract_ast:
        for contract_ast in contract_asts:
            if contract_ast['attributes']['name'] == contract.name:
                main_contract_ast = contract_ast
    contract.implemented_functions = get_function_asts(main_contract_ast)
    functions = []
    functions.extend(contract.implemented_functions)
    if not hasattr(main_contract_ast['attributes'], 'linearizedBaseContracts') \
        and len(main_contract_ast['attributes']['linearizedBaseContracts']) <= 1:
        return contract.implemented_functions
    linearizedBaseContracts = main_contract_ast['attributes']['linearizedBaseContracts'][1:]
    for contract_id in linearizedBaseContracts:
        for contract_ast in contract_asts:
            if contract_ast['id'] == contract_id:
                next_base_contract = contract_ast
                break
        base_functions = get_function_asts(next_base_contract)
        functions.extend(base_functions)
    return functions

def get_all_members_for_contract(contract):
    contract_asts = []
    for file in contract.solidity_files:
        contract_asts.extend(get_all_nested_dicts_with_kv_pairs(file.ast, "name", "ContractDefinition"))
    main_contract_ast = contract.ast if hasattr(contract, "ast") else None
    if not main_contract_ast:
        for contract_ast in contract_asts:
            if contract_ast['attributes']['name'] == contract.name:
                main_contract_ast = contract_ast
    members = augment_with_contract_name(get_contract_members(get_contract_members(main_contract_ast)),
                                         main_contract_ast['attributes']['name'])
    if not hasattr(main_contract_ast['attributes'], 'linearizedBaseContracts') \
        and len(main_contract_ast['attributes']['linearizedBaseContracts']) <= 1:
        return contract.members
    linearizedBaseContracts = main_contract_ast['attributes']['linearizedBaseContracts'][1:]
    for contract_id in linearizedBaseContracts:
        for contract_ast in contract_asts:
            if contract_ast['id'] == contract_id:
                next_base_contract = contract_ast
                break
        base_members = augment_with_contract_name(get_contract_members(next_base_contract), next_base_contract['attributes']['name'])
        members[:0] = base_members # Prepend members
    return members

def augment_with_contract_name(m_asts, contract_name):
    for m_ast in m_asts:
        m_ast["attributes"]['declaringContract'] = contract_name
    return m_asts


def get_contract_ast(ast, contract_name):
    contract_asts = get_all_nested_dicts_with_kv_pairs(ast, "name", "ContractDefinition")
    try:
        return list(filter(lambda c_ast: c_ast['attributes']['name'] == contract_name, contract_asts))[0]
    except KeyError:
        return None

def get_function_asts(contract_ast):
    return get_all_nested_dicts_with_kv_pairs(contract_ast, "name", "FunctionDefinition")


def get_function_term_positions(f_ast):
    # Todo ignore functions that definitely do not change anything for @invariant
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

def get_contract_members(contract_ast):
    var_defs = get_all_nested_dicts_with_kv_pairs(contract_ast, 'name', 'VariableDeclaration')
    return list(filter(lambda vdef: vdef['attributes']['stateVariable'],var_defs))

def get_struct_map(files):
    structs = {}
    for file in files:
        for struct in get_all_nested_dicts_with_kv_pairs(file.ast, 'name', 'StructDefinition'):
            struct_abs_name = struct['attributes']['canonicalName']
            if struct_abs_name not in structs:
                structs[struct_abs_name] = [variable['attributes']['type'] for variable in get_all_nested_dicts_with_kv_pairs(struct, 'name', 'VariableDeclaration')]
    return structs


