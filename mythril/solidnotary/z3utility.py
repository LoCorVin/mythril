from z3 import Solver, sat, simplify, is_bool, is_true, is_false
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


def filter_for_t_variable_data(sym_vars):
    return list(filter(lambda x: is_t_variable(x), sym_vars))

def are_satisfiable(constraints):
    return are_z3_satisfiable([const.constraint for const in constraints])

def are_z3_satisfiable(z3_constraints):
    s = Solver()
    for c in z3_constraints:
        s.add(c)
    return s.check() == sat

def simplify_z3_constraints(constraints): # Todo simplification of the sum of constraints
    simp_const = []
    for const in constraints:
        simp_const.append(simplify(const))
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