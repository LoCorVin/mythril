import logging
from mythril.solidnotary.transactiontrace import TransactionTrace, extract_sym_names
from mythril.solidnotary.z3utility import are_z3_satisfiable
from laser.ethereum.svm import Environment, GlobalState, CalldataType
from mythril.solidnotary.z3utility import are_satisfiable
from z3 import BitVec, BitVecRef, simplify, is_false, is_bool, is_true, Solver, sat, eq
from os.path import exists
from os import makedirs, chdir
from copy import deepcopy


class SolidNotary:

    def __init__(self, wd):
        # Todo Parse Annotations and store them in an additional structure
        # Todo receive a list of files or a file, these are modified for the analysis
        self.wd = wd
        self.tmp_dir = None

    def create_tmp_dir(self):
        for i in range(10):
            if not exists("tmp" + str(i)):
                makedirs("tmp" + str(i))
                self.tmp_dir = "tmp" + str(i)
                break

    def delete_tmp_dir(self):
        pass

    def notarize(self):
        # Todo Instantiate an instance of Mythril, analyze and print the result
        # Todo Find how they are storing results
        pass

def is_storage_primitive(storage):
    if storage:
        for index, content in storage.items():
            if not eq(content, BitVec("storage_" + str(index), 256)):
                return False
    return True

def get_transaction_traces(statespace):
    print("get_transaction_traces")
    num_elimi_traces= 0
    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode'] == "STOP":
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
                else:
                    num_elimi_traces += 1
    print("Eminiated constructor traces: " + str(num_elimi_traces))
    return traces

def get_construction_traces(statespace):
    print("get_constructor_traces")
    num_elimi_traces= 0
    traces = []

    for k in statespace.nodes:
        node = statespace.nodes[k]
        for state in node.states:
            instruction = state.get_current_instruction()
            if instruction['opcode'] == "RETURN":
                storage = state.environment.active_account.storage
                if storage and not is_storage_primitive(storage) and are_z3_satisfiable(state.mstate.constraints):
                    traces.append(TransactionTrace(state.environment.active_account.storage, state.mstate.constraints))
                else:
                    num_elimi_traces += 1
    print("Eminiated constructor traces: " + str(num_elimi_traces))
    return traces

def get_t_indexed_environment(active_account, index):

        # Initialize the execution environment

        environment = Environment(
            active_account,
            BitVec("caller_"+str(index), 256),
            [],
            BitVec("gasprice_"+str(index), 256),
            BitVec("callvalue_"+str(index), 256),
            BitVec("origin_"+str(index), 256),
            calldata_type=CalldataType.SYMBOLIC,
        )

        return environment

#def get_t_indexed_globstate(active_account, index):
#    environment = get_t_indexed_environment(active_account, index)
#    # Todo is this just some set of preset accounts? How should we deal with it
#    return GlobalState(self.accounts, environment)

