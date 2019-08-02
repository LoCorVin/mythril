from z3 import Solver, sat, eq, simplify, is_bool, is_true, is_false, Extract, BitVec, BitVecVal, is_bv
from copy import deepcopy


def is_t_variable(var):
    """
    Checks whether or not var is a value different from transaction to transaction.
    :param var: the symbolic variable that is checked against transaction dependence.
    :return: if the symbolic variable var is transaction dependent. They are not substituted.
    """
    var = str(var)
    if (var.startswith("caller")
            or var.startswith("gasprice")
            or var.startswith("callvalue")
            or var.startswith("origin")
            or var.startswith("calldata_")
            or var.startswith("calldatasize_")
            or var.startswith("balance_at")
            or var.startswith("keccak_mem_")
            or var.startswith("keccak_")
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
            or var.startswith("retval_")):
        return True
    else:
        return False


def get_bv(exp):
    """
    Ensures that the returned value is a binary vector by transforming the expression if necessary.
    :param exp: expression to transform into a binary vector
    :return: a binary vector
    """
    if is_bv(exp):
        return exp
    if type(exp) == int:
        return BitVecVal(exp, 256)
    raise ValueError("Bitvector or int needed")


def simplify_if_necessary(exp):
    """
    Executes the Z3 simplification algorithm if the expression is not a primitive value.
    :param exp: Expression to be simplified
    :return: The result of a expression simplification algorithm onto exp
    """
    if type(exp) in [int, str, float, complex, bool]:
        return exp
    return simplify(exp)


def sanitize_expr(exp):
    """
    Converts ints to bit vector expressions.
    :param exp:
    :return:
    """
    if type(exp) in [int]:
        return BitVecVal(exp, 256)
    return exp


def filter_for_t_variable_data(sym_vars):
    """
    Filters a list of symbolic variables for those that are transaction specific and do not reference the program state.
    :param sym_vars: list of symbolic variables
    :return: list of transaction specific symbolic variables
    """
    return list(filter(lambda x: is_t_variable(x), sym_vars))


def are_satisfiable(constraints):
    """
    Strips meta data from the constraints to only check the internal Z3 constraints over bit vectors for satisfiability.
    :param constraints: Annotary's constraints holding meta-data and Z3 constraints.
    :return: Whether or not they are satisfiable.
    """
    return are_z3_satisfiable([const.constraint for const in constraints])


def are_z3_satisfiable(z3_constraints):
    """
    Checks the satisfiability of Z3 constraints.
    :param z3_constraints: to be checked
    :return: if satisfiable
    """
    s = Solver()
    for c in z3_constraints:
        s.add(c)
    return s.check() == sat


def simplify_constraints_individually(constraints):
    """
    Returns False if contained in the constraints, simplifies the set of constraints individually.
    :param constraints: To be simplified.
    :return:
    """
    simp_const = []
    # Handle constraints based on trivial contained constraints
    if False in constraints:
        constraints = []
    else:
        constraints = [const for const in constraints if type(const) != bool]
    for const in constraints:
        simp_const.append(simplify(const))
    return simp_const


def simplify_storage(storage):
    """
    Simplifies the values stored in the storage slots.
    :param storage: the representation of a contract storage.
    :return: a storage representation with potentially simpler expressions.
    """
    return {k: (simplify(v) if not isinstance(v, int) else v) for k, v in storage.items()}


def simplify_z3_constraints(constraints):
    """
    Simplifies the constraint list, only by expressions that can be determined to evaluate to a a specific boolean value
    :param constraints:
    :return:
    """
    simp_const = constraints
    # Currently not running the individual simplification algorithm on every simplification call for
    # simp_const = simplify_constraints_individually(constraints)
    simp_const = list(filter(lambda c: not is_bool(c) or not is_true(c), simp_const))
    falses = list(filter(lambda c: is_bool(c) and is_false(c), simp_const))
    if len(falses) > 0:
        return [deepcopy(falses[0])]

    return simp_const


def simplify_constraints(constraints):
    """
    Simplifies the list of constraints, as well as the constraints individually.
    :param constraints: in Annotary representation, z3 constraints and metadata.
    :return: the simplified constraints.
    """
    for const in constraints:
        const.simplify()
    # Todo simplification of the sum of constraints
    simp_const = list(filter(lambda c: not is_bool(c.constraint) or not is_true(c.constraint), constraints))
    falses = list(filter(lambda c: is_bool(c.constraint) and is_false(c.constraint), simp_const))
    if len(falses) > 0:
        return [deepcopy(falses[0])]
    return simp_const


def extract_sym_names(obj):
    """
    Extracts the symbolic variables used in the Z3 object
    :param obj: a z3 expression or object.
    :return:
    """
    if (not hasattr(obj, 'children') or len(obj.children()) == 0) and hasattr(obj, 'decl'):
        return [str(obj.decl())]
    else:
        sym_vars = []
        for c in obj.children():
            sym_vars.extend(extract_sym_names(c))
        return sym_vars


def get_function_from_constraints(contract, constraints, is_constructor=False):
    """
    Makes assumptions on the currently executed contract function, based on the constraint list. THe function identifier
    passed in the call data is checked in the contract bytecode to jump to the function implementation. A check for it
    is therefore contained in the constraint list.
    :param contract: the contract that was symbolically executed.
    :param constraints: the constraints of symbolic execution.
    :param is_constructor: whether the constructor is executed.
    :return: The currently executed contract function.
    """
    default_func = None
    for func in contract.functions:
        # Returns the constructor function when found, if it is known to be currently executed
        if func.isConstructor and is_constructor:
            return func
        for constraint in constraints:
            # Compares function hashes and == constraints.
            if len(func.hash) > 0:
                function_constraint = Extract(255, 224,
                                              BitVec('calldata_' + contract.name + "[0]", 256)) == int(func.hash,
                                                                                                       16)
                if eq(simplify(function_constraint), constraint):
                    return func
        if not func.isConstructor:
            # Return the default function if one exists an no other function was identified
            if func.signature == "()":
                default_func = func
    return default_func


def extract_possible_hashes(state, contract_name):
    """
    Extracts possible hashes representing function identifiers from the state constraints.
    :param state: in a function
    :param contract_name: the contract name of the executed contract
    :return: all possible function identifier hashes.
    """
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
                f_hash = hex(hash_as_int).replace("0x", "")
                f_hash = "0"*(8-len(f_hash)) + f_hash
                hashes.append(f_hash)
            except ValueError:
                continue
    return hashes

