from z3 import Solver, sat, eq, simplify, is_bool, is_true, is_false, Extract, BitVec, BitVecVal
from copy import deepcopy

"""
    Returns whether or the specified symbolic string stands for a data value that can be different from transaction to 
    transaction without the need of an intermediate call to the contract (e.g. a transaction params, blocknumber, ...)
"""


def is_t_variable(var):
    var = str(var)
    if (var.startswith("caller")
        or var.startswith("gasprice")
        or var.startswith("callvalue")
        or var.startswith("origin")
        or var.startswith("calldata_")
        or var.startswith("calldatasize_")
        or var.startswith("balance_at")
        or var.startswith("KECCAC_mem_")
        or var.startswith("keccac_")
        or var.startswith("gasprice")
        or var.startswith("extcodesize")
        or var.startswith("returndatasize")
        # or var.startswith(var, "blockhash_block_") should not change between transactions
        or var.startswith("coinbase")
        or var.startswith("timestamp")
        or var.startswith("block_number")
        or var.startswith("block_difficulty")
        or var.startswith("block_gaslimit")
        or var.startswith("mem_")
        or var.startswith("msize")
        or var.startswith("gas")
        or var.startswith("retval_")
        or var.startswith("keccac_")):
        return True
    else:
        return False

def simplify_if_necessary(exp):
    if type(exp) in [int, str, float, complex, bool]:
        return exp
    return simplify(exp)

def sanitize_expr(exp):
    if type(exp) in [int]:
        return BitVecVal(exp, 256)
    return exp


def filter_for_t_variable_data(sym_vars):
    return list(filter(lambda x: is_t_variable(x), sym_vars))

def are_satisfiable(constraints):
    return are_z3_satisfiable([const.constraint for const in constraints])

def are_z3_satisfiable(z3_constraints):
    s = Solver()
    for c in z3_constraints:
        s.add(c)
    return s.check() == sat

def simplify_constraints_individually(constraints):
    simp_const = []
    for const in constraints:
        simp_const.append(simplify(const))
    return simp_const

def simplify_storage(storage):
    return {k:(simplify(v) if not isinstance(v, int) else v) for k, v in storage.items()}


def simplify_z3_constraints(constraints): # Todo simplification of the sum of constraints
    simp_const = constraints
    # simp_const = simplify_constraints_individually(constraints)
    simp_const = list(filter(lambda c: not is_bool(c) or not is_true(c), simp_const))
    falses = list(filter(lambda c: is_bool(c) and is_false(c), simp_const))
    if len(falses) > 0:
        return [deepcopy(falses[0])]

    return simp_const

def simplify_constraints(constraints): # Todo simplification of the sum of constraints
    simp_const = []
    for const in constraints:
        const.simplify()
    simp_const = list(filter(lambda c: not is_bool(c.constraint) or not is_true(c.constraint), constraints))
    falses = list(filter(lambda c: is_bool(c.constraint) and is_false(c.constraint), simp_const))
    if len(falses) > 0:
        return [deepcopy(falses[0])]

    return simp_const


def extract_sym_names(obj):
    if (not hasattr(obj, 'children') or len(obj.children()) == 0) and hasattr(obj, 'decl') :
            return [str(obj.decl())]
    else:
        sym_vars = []
        for c in obj.children():
            sym_vars.extend(extract_sym_names(c))
        return sym_vars

'''
    If None is returned the function that is searched is the default function or the constructor
'''
def get_function_from_constraints(contract, constraints, is_constructor=False):
    default_func = None
    for func in contract.functions:
        if func.isConstructor and is_constructor:
            return func
        for constraint in constraints:
            if len(func.hash) > 0:
                function_constraint = Extract(255, 224,
                                              BitVec('calldata_' + contract.name + "[0]", 256)) == int(func.hash,
                                                                                                       16)
                if eq(simplify(function_constraint), constraint):
                    return func
        if not func.isConstructor:
            if func.signature == "()":
                default_func = func
    return default_func

def get_function_from_constraints(contract, constraints, is_constructor=False):
    default_func = None
    for func in contract.functions:
        if func.isConstructor and is_constructor:
            return func
        for constraint in constraints:
            if len(func.hash) > 0:
                function_constraint = Extract(255, 224,
                                              BitVec('calldata_' + contract.name + "[0]", 256)) == int(func.hash,
                                                                                                       16)
                if eq(simplify(function_constraint), constraint):
                    return func
        if not func.isConstructor:
            if func.signature == "()":
                default_func = func
    return default_func


def extract_possible_hashes(state, contract_name):
    hashes = []
    for constraint in state.mstate.constraints:
        simp_constraint = simplify(constraint)
        str_constraint = str(simp_constraint).replace(" ", "")
        str_constraint = str_constraint.replace("\n", "")
        start = "Extract(255,224,calldata_" + contract_name + "[0])=="
        end = ""
        if str_constraint.startswith(start) and str_constraint.endswith(end):
            try:
                hash_as_int = int(str_constraint[len(start):-len(end)])
                hash = hex(hash_as_int).replace("0x", "")
                hash = "0"*(8-len(hash)) + hash
                hashes.append(hash)
            except ValueError:
                continue

    return hashes

