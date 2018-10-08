
import logging
from mythril.annotary.calldata import get_minimal_constructor_param_encoding_len, abi_json_to_abi
from mythril.laser.ethereum.svm import GlobalState, Account, Environment, MachineState, CalldataType
from z3 import BitVec
from mythril.analysis.symbolic import SymExecWrapper
from mythril.support.loader import DynLoader
from copy import deepcopy
from mythril.disassembler.disassembly import Disassembly
from time import process_time

from .annotary import get_transaction_traces, get_construction_traces


def get_constr_glbstate(contract, address):

    mstate = MachineState(gas=10000000)

    minimal_const_byte_len = get_minimal_constructor_param_encoding_len(abi_json_to_abi(contract.abi))

    # better would be to append symbolic params to the bytecode such that the codecopy instruction that copies the
    # params into memory takes care of placing them onto the memory with the respective size.
    for i in range(int(minimal_const_byte_len / 32)):
        mstate.mem_extend(128 + 32 * i, 32)
        mstate.memory.insert(128 + 32 * i, BitVec('calldata_' + contract.name + '_' + str(i * 32), 256))

    # Todo Replace pure placement of enough symbolic 32 Byte-words with placement of symbolic variables that contain
    # the name of the solidity variables

    accounts = {address: Account(address, contract.disassembly, contract_name=contract.name)}

    environment = Environment(
        accounts[address],
        BitVec("caller", 256),
        [],
        BitVec("gasprice", 256),
        BitVec("callvalue", 256),
        BitVec("origin", 256),
        calldata_type=CalldataType.SYMBOLIC,
    )

    # Todo find source for account info, maybe the std statespace?

    return GlobalState(accounts, environment, mstate)


def check_annotations(contracts, address, eth, dynld, max_depth=12):

    logging.debug("Executing annotations check")

    for contract in contracts:

        contr_to_const = deepcopy(contract)
        contr_to_const.disassembly = Disassembly(contr_to_const.creation_code)
        contr_to_const.code = contr_to_const.creation_code
        dynloader = DynLoader(eth) if dynld else None
        glbstate = get_constr_glbstate(contr_to_const, address)

        sym_constructor = SymExecWrapper(contr_to_const, address, dynloader, max_depth, glbstate)
        sym_contract = SymExecWrapper(contract, address, dynloader, max_depth=max_depth)

        constructor_trace = get_construction_traces(
            sym_constructor)  # Todo the traces here should not contain references to storages anymore
        for t in constructor_trace:
            t.pp_trace()

        traces = get_transaction_traces(sym_contract)
        print("Start")
        a = process_time()
        print("const: " + str(len(constructor_trace)) + " trans: " + str(len(traces)))
        trace_chains = []
        for trace in constructor_trace:
            comp_trace_lvls = trace.apply_up_to_trace_levels(traces, 1)
            if not trace_chains:
                trace_chains = comp_trace_lvls
            else:
                for index in range(len(trace_chains)):
                    trace_chains[index].extend(comp_trace_lvls[index])
            print()
        for lvl in trace_chains:
            print("Traces: " + str(len(lvl)))

        #for tt in trace_chains[-1]:
        #    tt.pp_trace()
        #    for trace_lvl in comp_trace_lvls:
        #        print(len(trace_lvl))
        #        print(sum(map(lambda t: len(t.tran_constraints), trace_lvl))/len(trace_lvl))
        #        for t in trace_lvl:
        #            print("constraints: " + str(len(t.tran_constraints)))
        #            t.pp_trace()
        print(process_time() - a)

