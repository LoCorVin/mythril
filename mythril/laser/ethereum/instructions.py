import binascii
import logging
from copy import copy, deepcopy
from z3 import BitVecRef

import ethereum.opcodes as opcodes
from ethereum import utils
from z3 import BitVec, Extract, UDiv, simplify, Concat, ULT, UGT, BitVecNumRef, Not, \
    is_false, is_expr, ExprRef, URem, SRem
from z3 import BitVecVal, If, BoolRef

import mythril.laser.ethereum.util as helper
from mythril.laser.ethereum import util
from mythril.laser.ethereum.call import get_call_parameters
from mythril.laser.ethereum.state import GlobalState, MachineState, Environment, CalldataType
import mythril.laser.ethereum.natives as natives
from mythril.laser.ethereum.transaction import MessageCallTransaction, TransactionEndSignal, TransactionStartSignal, \
    ContractCreationTransaction, CreateNewContractSignal
from mythril.laser.ethereum.state import Storage

keccak_map = {}

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1


class StackUnderflowException(Exception):
    pass


class StopSignal(Exception):
    pass


def instruction(func):
    """ Wrapper that handles copy and original return """

    def wrapper(self, global_state):
        global_state_copy = copy(global_state)
        new_global_states = func(self, global_state_copy)
        for state in new_global_states:
            state.mstate.pc += 1
        return new_global_states
    return wrapper


class Instruction:
    """
    Instruction class is used to mutate a state according to the current instruction
    """

    def __init__(self, op_code, dynamic_loader):
        self.dynamic_loader = dynamic_loader
        self.op_code = op_code

    def evaluate(self, global_state, post=False):
        """ Performs the mutation for this instruction """
        # Generalize some ops
        logging.debug("Evaluating {}".format(self.op_code))
        op = self.op_code.lower()
        if self.op_code.startswith("PUSH"):
            op = "push"
        elif self.op_code.startswith("DUP"):
            op = "dup"
        elif self.op_code.startswith("SWAP"):
            op = "swap"
        elif self.op_code.startswith("LOG"):
            op = "log"

        instruction_mutator = getattr(self, op + '_', None) if not post else getattr(self, op + '_' + 'post', None)

        if instruction_mutator is None:
            raise NotImplementedError

        return instruction_mutator(global_state)

    @instruction
    def jumpdest_(self, global_state):
        return [global_state]

    @instruction
    def push_(self, global_state):
        value = BitVecVal(int(global_state.get_current_instruction()['argument'][2:], 16), 256)
        global_state.mstate.stack.append(value)
        return [global_state]

    @instruction
    def dup_(self, global_state):
        value = int(global_state.get_current_instruction()['opcode'][3:], 10)
        global_state.mstate.stack.append(global_state.mstate.stack[-value])
        return [global_state]

    @instruction
    def swap_(self, global_state):
        depth = int(self.op_code[4:])
        try:
            stack = global_state.mstate.stack
            stack[-depth - 1], stack[-1] = stack[-1], stack[-depth - 1]
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def pop_(self, global_state):
        try:
            global_state.mstate.stack.pop()
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def and_(self, global_state):
        try:
            stack = global_state.mstate.stack
            op1, op2 = stack.pop(), stack.pop()
            if type(op1) == BoolRef:
                op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))
            if type(op2) == BoolRef:
                op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

            stack.append(op1 & op2)
        except IndexError:
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def or_(self, global_state):
        stack = global_state.mstate.stack
        try:
            op1, op2 = stack.pop(), stack.pop()

            if type(op1) == BoolRef:
                op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

            if type(op2) == BoolRef:
                op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

            stack.append(op1 | op2)
        except IndexError:  # Stack underflow
            raise StackUnderflowException()
        return [global_state]

    @instruction
    def xor_(self, global_state):
        mstate = global_state.mstate
        mstate.stack.append(mstate.stack.pop() ^ mstate.stack.pop())
        return [global_state]

    @instruction
    def not_(self, global_state: GlobalState):
        mstate = global_state.mstate
        mstate.stack.append(TT256M1 - mstate.stack.pop())
        return [global_state]

    @instruction
    def byte_(self, global_state):
        mstate = global_state.mstate
        op0, op1 = mstate.stack.pop(), mstate.stack.pop()
        if not isinstance(op1, ExprRef):
            op1 = BitVecVal(op1, 256)
        try:
            index = util.get_concrete_int(op0)
            offset = (31 - index) * 8
            result = Concat(BitVecVal(0, 248), Extract(offset + 7, offset, op1))
        except AttributeError:
            logging.debug("BYTE: Unsupported symbolic byte offset")
            result = BitVec(str(simplify(op1)) + "[" + str(simplify(op0)) + "]", 256)

        mstate.stack.append(simplify(result))
        return [global_state]

    # Arithmetic
    @instruction
    def add_(self, global_state):
        op1, op2 = helper.pop_bitvec(global_state.mstate), helper.pop_bitvec(global_state.mstate)
        op1_str, op2_str = str(op1).replace("\n", ""), str(op2).replace("\n", "")
        # Augmentation to backtrace hash computations
        if op1_str in keccak_map or op2_str in keccak_map:
            op1_original, op2_original = op1, op2
            #if op1_str in keccak_map:
            #    op1_original = keccak_map[op1_str]
            #if op2_str in keccak_map:
            #    op2_original = keccak_map[op2_str]
            keccak_map[str(simplify(op1+op2)).replace("\n", "")] = op1_original + op2_original
        global_state.mstate.stack.append(op1 + op2)
        return [global_state]

    @instruction
    def sub_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) - helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def mul_(self, global_state):
        global_state.mstate.stack.append(
            (helper.pop_bitvec(global_state.mstate) * helper.pop_bitvec(global_state.mstate)))
        return [global_state]

    @instruction
    def div_(self, global_state):
        op0, op1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        if op1 == 0:
            global_state.mstate.stack.append(BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(UDiv(op0, op1))
        return [global_state]

    @instruction
    def sdiv_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        if s1 == 0:
            global_state.mstate.stack.append(BitVecVal(0, 256))
        else:
            global_state.mstate.stack.append(s0 / s1)
        return [global_state]

    @instruction
    def mod_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(0 if s1 == 0 else URem(s0, s1))
        return [global_state]

    @instruction
    def smod_(self, global_state):
        s0, s1 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate)
        global_state.mstate.stack.append(0 if s1 == 0 else SRem(s0, s1))
        return [global_state]

    @instruction
    def addmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append(URem(URem(s0, s2) + URem(s1, s2), s2))
        return [global_state]

    @instruction
    def mulmod_(self, global_state):
        s0, s1, s2 = util.pop_bitvec(global_state.mstate), util.pop_bitvec(global_state.mstate), util.pop_bitvec(
            global_state.mstate)
        global_state.mstate.stack.append(URem(URem(s0, s2) * URem(s1, s2), s2))
        return [global_state]

    @instruction
    def exp_(self, global_state):
        state = global_state.mstate
        # we only implement 2 ** x
        base, exponent = util.pop_bitvec(state), util.pop_bitvec(state)

        if (type(base) != BitVecNumRef) or (type(exponent) != BitVecNumRef):
            state.stack.append(BitVec("(" + str(simplify(base)) + ")^(" + str(simplify(exponent)) + ")", 256))
        elif base.as_long() == 2:
            if exponent.as_long() == 0:
                state.stack.append(BitVecVal(1, 256))
            else:
                state.stack.append(base << (exponent - 1))
        else:
            state.stack.append(BitVecVal(base.as_long() ** exponent.as_long(), 256))
        return [global_state]

    @instruction
    def signextend_(self, global_state):
        state = global_state.mstate
        s0, s1 = state.stack.pop(), state.stack.pop()

        try:
            s0 = util.get_concrete_int(s0)
            s1 = util.get_concrete_int(s1)

            if s0 <= 31:
                testbit = s0 * 8 + 7
                if s1 & (1 << testbit):
                    state.stack.append(s1 | (TT256 - (1 << testbit)))
                else:
                    state.stack.append(s1 & ((1 << testbit) - 1))
            else:
                state.stack.append(s1)
            # TODO: broad exception handler
        except:
            return []

        return [global_state]

    # Comparisons
    @instruction
    def lt_(self, global_state):
        state = global_state.mstate
        exp = ULT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @instruction
    def gt_(self, global_state):
        state = global_state.mstate
        exp = UGT(util.pop_bitvec(state), util.pop_bitvec(state))
        state.stack.append(exp)
        return [global_state]

    @instruction
    def slt_(self, global_state):
        state = global_state.mstate
        exp = util.pop_bitvec(state) < util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @instruction
    def sgt_(self, global_state):
        state = global_state.mstate

        exp = util.pop_bitvec(state) > util.pop_bitvec(state)
        state.stack.append(exp)
        return [global_state]

    @instruction
    def eq_(self, global_state):
        state = global_state.mstate

        op1 = state.stack.pop()
        op2 = state.stack.pop()


        if type(op1) == BoolRef:
            op1 = If(op1, BitVecVal(1, 256), BitVecVal(0, 256))

        if type(op2) == BoolRef:
            op2 = If(op2, BitVecVal(1, 256), BitVecVal(0, 256))

        exp = op1 == op2

        state.stack.append(exp)
        return [global_state]

    @instruction
    def iszero_(self, global_state):
        state = global_state.mstate

        val = state.stack.pop()
        exp = val == False if type(val) == BoolRef else val == 0
        state.stack.append(exp)

        return [global_state]

    # Call data
    @instruction
    def callvalue_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.callvalue)

        return [global_state]

    @instruction
    def calldataload_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0 = state.stack.pop()

        try:
            offset = util.get_concrete_int(simplify(op0))
            b = environment.calldata[offset]
        except AttributeError:
            logging.debug("CALLDATALOAD: Unsupported symbolic index")
            state.stack.append(BitVec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
            return [global_state]
        except IndexError:
            logging.debug("Calldata not set, using symbolic variable instead")
            state.stack.append(BitVec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
            return [global_state]

        if type(b) == int:
            val = b''

            try:
                for i in range(offset, offset + 32):
                    val += environment.calldata[i].to_bytes(1, byteorder='big')

                logging.debug("Final value: " + str(int.from_bytes(val, byteorder='big')))
                state.stack.append(BitVecVal(int.from_bytes(val, byteorder='big'), 256))
            # FIXME: broad exception catch
            except:
                state.stack.append(BitVec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))
        else:
            # symbolic variable
            state.stack.append(BitVec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(simplify(op0)) + "]", 256))

        return [global_state]

    @instruction
    def calldatasize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        if environment.calldata_type == CalldataType.SYMBOLIC:
            state.stack.append(BitVec("calldatasize_" + environment.active_account.contract_name, 256))
        else:
            state.stack.append(BitVecVal(len(environment.calldata), 256))
        return [global_state]

    @instruction
    def calldatacopy_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0, op1, op2 = state.stack.pop(), state.stack.pop(), state.stack.pop()

        try:
            mstart = util.get_concrete_int(op0)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic memory offset in CALLDATACOPY")
            return [global_state]

        dstart_sym = False
        try:
            dstart = util.get_concrete_int(op1)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic calldata offset in CALLDATACOPY")
            dstart = simplify(op1)
            dstart_sym = True

        size_sym = False
        try:
            size = util.get_concrete_int(op2)
            # FIXME: broad exception catch
        except:
            logging.debug("Unsupported symbolic size in CALLDATACOPY")
            size = simplify(op2)
            size_sym = True

        if dstart_sym or size_sym:
            state.mem_extend(mstart, 1)
            state.memory[mstart] = BitVec(
                "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                    size) + "]", 256)
            return [global_state]

        if size > 0:
            try:
                state.mem_extend(mstart, size)
            # FIXME: broad exception catch
            except:
                logging.debug("Memory allocation error: mstart = " + str(mstart) + ", size = " + str(size))
                state.mem_extend(mstart, 1)
                state.memory[mstart] = BitVec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                        size) + "]", 256)
                return [global_state]

            try:
                i_data = environment.calldata[dstart]

                for i in range(mstart, mstart + size):
                    state.memory[i] = environment.calldata[i_data]
                    i_data += 1
            except:
                logging.debug("Exception copying calldata to memory")

                state.memory[mstart] = BitVec(
                    "calldata_" + str(environment.active_account.contract_name) + "[" + str(dstart) + ": + " + str(
                        size) + "]", 256)
        return [global_state]

    # Environment
    @instruction
    def address_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.address)
        return [global_state]

    @instruction
    def balance_(self, global_state):
        state = global_state.mstate
        address = state.stack.pop()
        try:
            address_hex = util.get_concrete_int(simplify(address))
            active_address = int(global_state.environment.active_account.address, 16)
            if address_hex == active_address:
                state.stack.append(global_state.environment.active_account.balance)
                return [global_state]
        except:
            pass
        state.stack.append(BitVec("balance_at[" + str(address) + "]", 256))
        return [global_state]

    @instruction
    def origin_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.origin)
        return [global_state]

    @instruction
    def caller_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        state.stack.append(environment.sender)
        return [global_state]

    @instruction
    def codesize_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        disassembly = environment.code
        if hasattr(environment, "code_extension"):
            state.stack.append(len(disassembly.bytecode) // 2 + len(environment.code_extension))
        else:
            state.stack.append(len(disassembly.bytecode) // 2)
        return [global_state]

    @instruction
    def sha3_(self, global_state):
        state = global_state.mstate
        environment = global_state.environment
        op0, op1 = state.stack.pop(), state.stack.pop()

        try:
            index, length = util.get_concrete_int(op0), util.get_concrete_int(op1)
        # FIXME: broad exception catch
        except:
            # Can't access symbolic memory offsets
            if is_expr(op0):
                op0 = simplify(op0)
            state.stack.append(BitVec("keccak_mem[" + str(op0) + "]", 256))
            return [global_state]

        try:
            data = b''

            for i in range(index, index + length):
                data += util.get_concrete_int(state.memory[i]).to_bytes(1, byteorder='big')
                i += 1
            # FIXME: broad exception catch
        except:
            data = b''
            last = 0
            result = None
            i = index
            while i < index + length:
                if type(state.memory[i]) == BitVecRef:
                    if i - last > 0:
                        if result == None:
                            result = BitVecVal(util.concrete_int_from_bytes(data, 0), len(data)*8)
                        else:
                            result = Concat(result, BitVecVal(util.concrete_int_from_bytes(data, 0), len(data)*8)) # Todo decide on concat order

                        result = Concat(result, state.memory[i])
                    else:
                        result = state.memory[i]
                    data = b''
                    i += 32 # Todo not shure whether or not to change this variably
                    last = i
                else:
                    data += util.get_concrete_int(state.memory[i]).to_bytes(1, byteorder='big')
                    i += 1
            if len(data) > 0:
                if result == None:
                    result = BitVecVal(util.concrete_int_from_bytes(data, 0), len(data)*8)
                else:
                    result = Concat(result, BitVecVal(util.concrete_int_from_bytes(data, 0), len(data)*8))

            svar = str(simplify(result))


            svar = svar.replace(" ", "_")

            state.stack.append(BitVec("keccak(" + svar+ ")", 256))
            return [global_state]

        keccak = utils.sha3(utils.bytearray_to_bytestr(data))
        logging.debug("Computed SHA3 Hash: " + str(binascii.hexlify(keccak)))
        keccak_result = BitVecVal(util.concrete_int_from_bytes(keccak, 0), 256)

        keccak_map[str(keccak_result)] = None
        i = 0
        while i < length:
            bitvec = BitVecVal(util.concrete_int_from_bytes(data, i), (len(data) - i)*8 if len(data) - i < 32 else 256 )
            bitvec_key = str(bitvec).replace("\n", "")
            if bitvec_key in keccak_map:
                bitvec = keccak_map[bitvec_key]
            if keccak_map[str(keccak_result)] is None:
                keccak_map[str(keccak_result)] = bitvec
            else:
                keccak_map[str(keccak_result)] = Concat(keccak_map[str(keccak_result)], bitvec)
            i += 32

        state.stack.append(keccak_result)
        return [global_state]

    @instruction
    def gasprice_(self, global_state):
        global_state.mstate.stack.append(BitVec("gasprice", 256))
        return [global_state]

    @instruction
    def codecopy_(self, global_state):
        memory_offset, code_offset, size = global_state.mstate.stack.pop(), global_state.mstate.stack.pop(), global_state.mstate.stack.pop()

        try:
            concrete_memory_offset = helper.get_concrete_int(memory_offset)
        except AttributeError:
            logging.debug("Unsupported symbolic memory offset in CODECOPY")
            return [global_state]

        try:
            concrete_size = helper.get_concrete_int(size)
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
        except:
            # except both attribute error and Exception
            global_state.mstate.mem_extend(concrete_memory_offset, 1)
            global_state.mstate.memory[concrete_memory_offset] = \
                BitVec("code({})".format(global_state.environment.active_account.contract_name), 256)
            return [global_state]

        try:
            concrete_code_offset = helper.get_concrete_int(code_offset)
        except AttributeError:
            logging.debug("Unsupported symbolic code offset in CODECOPY")
            global_state.mstate.mem_extend(concrete_memory_offset, concrete_size)
            for i in range(concrete_size):
                global_state.mstate.memory[concrete_memory_offset + i] = \
                    BitVec("code({})".format(global_state.environment.active_account.contract_name), 256)
            return [global_state]

        bytecode = global_state.environment.code.bytecode

        if concrete_size == 0 and isinstance(global_state.current_transaction, ContractCreationTransaction):
            if concrete_code_offset >= len(global_state.environment.code.bytecode) // 2:
                global_state.mstate.mem_extend(concrete_memory_offset, 1)
                global_state.mstate.memory[concrete_memory_offset] = \
                    BitVec("code({})".format(global_state.environment.active_account.contract_name), 256)
                return [global_state]

        for i in range(concrete_size):
            if 2 * (concrete_code_offset + i + 1) <= len(bytecode):
                global_state.mstate.memory[concrete_memory_offset + i] =\
                    int(bytecode[2*(concrete_code_offset + i): 2*(concrete_code_offset + i + 1)], 16)
            else:
                if hasattr(global_state.environment, "code_extension") and concrete_code_offset + i + 1 <= len(bytecode) / 2 + len(global_state.environment.code_extension):
                    global_state.mstate.memory[concrete_memory_offset + i] = global_state.environment.code_extension[concrete_code_offset + i - int(len(bytecode) / 2)]
                else:
                    global_state.mstate.memory[concrete_memory_offset + i] = \
                        BitVec("code({})".format(global_state.environment.active_account.contract_name), 256)

        return [global_state]

    @instruction
    def extcodesize_(self, global_state):
        state = global_state.mstate
        addr = state.stack.pop()
        environment = global_state.environment
        try:
            addr = hex(helper.get_concrete_int(addr))
        except AttributeError:
            logging.info("unsupported symbolic address for EXTCODESIZE")
            state.stack.append(BitVec("extcodesize_" + str(addr), 256))
            return [global_state]

        try:
            code = self.dynamic_loader.dynld(environment.active_account.address, addr)
        except Exception as e:
            logging.info("error accessing contract storage due to: " + str(e))
            state.stack.append(BitVec("extcodesize_" + str(addr), 256))
            return [global_state]

        if code is None:
            state.stack.append(0)
        else:
            state.stack.append(len(code.bytecode) // 2)

        return [global_state]

    @instruction
    def extcodecopy_(self, global_state):
        state = global_state.mstate
        addr = state.stack.pop()
        start_memory, start_code, size = state.stack.pop(), state.stack.pop(), state.stack.pop()
        try:
            start_memory, start_code, size = util.get_concrete_int(start_memory), util.get_concrete_int(start_code), util.get_concrete_int(size)
        except ValueError as e:
            logging.debug("This should not happen as returndataoffsets and length are constant")
            raise ValueError("Parameters for returndatacopy are not concrete")

        environment = global_state.environment
        try:
            addr = hex(helper.get_concrete_int(addr))
        except AttributeError:
            logging.info("unsupported symbolic address for EXTCODESIZE")
            # Annotary: Here i prefere to hard fail then to return some memory with 0 chuns that will be bad foranalysis
            raise EnvironmentError("Symbolic address value cannot be mapped to concrete or meaningfully symbolic representation of bytecode")
            #state.stack.append(BitVec("extcodesize_" + str(addr), 256))
            #return [global_state]

        try:
            code = self.dynamic_loader.dynld(environment.active_account.address, addr)
        except Exception as e:
            logging.info("error accessing contract storage due to: " + str(e))
            # Annotary: Here i prefere to hard fail then to return some memory with 0 chuns that will be bad foranalysis
            raise EnvironmentError("Symbolic address value cannot be mapped to concrete or meaningfully symbolic representation of bytecode")
            #return [global_state]

        if code is None and size > 0:
            raise ValueError("Code is empty but size is not")
        if start_code + size > len(code.bytecode) / 2:
            raise ValueError("Code to short to copy into memory with the given size")

        for i in range(size):
            if 2 * (start_code + i + 1) <= len(code.bytecode):
                global_state.mstate.memory[start_code + i] =\
                    int(code.bytecode[2*(start_code + i): 2*(start_code + i + 1)], 16)

        return [global_state]

    @instruction # Implemented by Annotary
    def returndatacopy_(self, global_state):

        state = global_state.mstate
        start_memory, start_return_data, size = state.stack.pop(), state.stack.pop(), state.stack.pop()
        try:
            start_memory, start_return_data, size = util.get_concrete_int(start_memory), util.get_concrete_int(start_return_data), util.get_concrete_int(size)
        except ValueError as e:
            logging.debug("This should not happen as returndataoffsets and length are constant")
            raise ValueError("Parameters for returndatacopy are not concrete")
        return_data = global_state.last_return_data



        i = 0
        while i < size:
            global_state.mstate.memory[start_memory + i] = return_data[start_return_data + i]
            i += 1

        return [global_state]

    @instruction
    def returndatasize_(self, global_state):
        if not hasattr(global_state, "last_return_data") or not global_state.last_return_data or type(global_state.last_return_data) != list:
            global_state.mstate.stack.append(BitVecVal(0, 256))
            # global_state.mstate.stack.append(BitVec("returndatasize_" + str(id(global_state)), 256))
        else:
            global_state.mstate.stack.append(BitVecVal(len(global_state.last_return_data), 256))
        return [global_state]

    @instruction
    def blockhash_(self, global_state):
        state = global_state.mstate
        blocknumber = state.stack.pop()
        state.stack.append(BitVec("blockhash_block_" + str(blocknumber), 256))
        return [global_state]

    @instruction
    def coinbase_(self, global_state):
        global_state.mstate.stack.append(BitVec("coinbase", 256))
        return [global_state]

    @instruction
    def timestamp_(self, global_state):
        global_state.mstate.stack.append(BitVec("timestamp", 256))
        return [global_state]

    @instruction
    def number_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_number", 256))
        return [global_state]

    @instruction
    def difficulty_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_difficulty", 256))
        return [global_state]

    @instruction
    def gaslimit_(self, global_state):
        global_state.mstate.stack.append(BitVec("block_gaslimit", 256))
        return [global_state]

    # Memory operations
    @instruction
    def mload_(self, global_state):
        state = global_state.mstate
        op0 = state.stack.pop()

        logging.debug("MLOAD[" + str(op0) + "]")

        try:
            offset = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("Can't MLOAD from symbolic index")
            data = BitVec("mem[" + str(simplify(op0)) + "]", 256)
            state.stack.append(data)
            return [global_state]

        try:
            data = util.concrete_int_from_bytes(state.memory, offset)
        except IndexError:  # Memory slot not allocated
            data = BitVec("mem[" + str(offset) + "]", 256)
        except TypeError:  # Symbolic memory
            data = state.memory[offset]

        logging.debug("Load from memory[" + str(offset) + "]: " + str(data))

        state.stack.append(data)
        return [global_state]

    @instruction
    def mstore_(self, global_state):
        state = global_state.mstate
        try:
            op0, value = state.stack.pop(), state.stack.pop()
        except IndexError:
            raise StackUnderflowException()

        try:
            mstart = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        try:
            state.mem_extend(mstart, 32)
        except Exception:
            logging.debug("Error extending memory, mstart = " + str(mstart) + ", size = 32")

        logging.debug("MSTORE to mem[" + str(mstart) + "]: " + str(value))

        try:
            # Attempt to concretize value
            _bytes = util.concrete_int_to_bytes(value)

            i = 0

            for b in _bytes:
                state.memory[mstart + i] = _bytes[i]
                i += 1
        except:
            try:
                state.memory[mstart] = value
            except:
                logging.debug("Invalid memory access")

        return [global_state]

    @instruction
    def mstore8_(self, global_state):
        state = global_state.mstate
        op0, value = state.stack.pop(), state.stack.pop()

        try:
            offset = util.get_concrete_int(op0)
        except AttributeError:
            logging.debug("MSTORE to symbolic index. Not supported")
            return [global_state]

        state.mem_extend(offset, 1)

        state.memory[offset] = value % 256
        return [global_state]

    @instruction
    def sload_(self, global_state):
        state = global_state.mstate
        index = state.stack.pop()
        logging.debug("Storage access at index " + str(index))

        try:
            index = util.get_concrete_int(index)
        except AttributeError:
            index = str(index)

        try:
            data = global_state.environment.active_account.storage[index]
        except KeyError:
            data = BitVec("storage[" + str(index) + "]", 256)
            global_state.environment.active_account.storage[index] = data

        state.stack.append(data)
        return [global_state]

    @instruction
    def sstore_(self, global_state):
        if hasattr(global_state.environment, "can_write") and not global_state.environment.can_write:
            return [] # Error is thrown, and no state returned if static call is used
        state = global_state.mstate
        index, value = state.stack.pop(), state.stack.pop()

        # print("Index: " + str(simplify(index)))
        # print("Value: " + str(simplify(value)))

        logging.debug("Write to storage[" + str(index) + "]")

        try:
            index = util.get_concrete_int(index)
        except AttributeError:
            index = str(index)

        try:
            global_state.environment.active_account = deepcopy(global_state.environment.active_account)
            global_state.accounts[
                global_state.environment.active_account.address] = global_state.environment.active_account

            global_state.environment.active_account.storage[index] = value
        except KeyError:
            logging.debug("Error writing to storage: Invalid index")
        return [global_state]

    @instruction
    def jump_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.code
        try:
            jump_addr = util.get_concrete_int(state.stack.pop())
        except AttributeError:
            logging.debug("Invalid jump argument (symbolic address)")
            return []
        except IndexError:  # Stack Underflow
            return []

        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if index is None:
            logging.debug("JUMP to invalid address")
            return []

        op_code = disassembly.instruction_list[index]['opcode']

        if op_code != "JUMPDEST":
            logging.debug("Skipping JUMP to invalid destination (not JUMPDEST): " + str(jump_addr))
            return []

        new_state = copy(global_state)
        new_state.mstate.pc = index
        new_state.mstate.depth += 1

        return [new_state]

    @instruction
    def jumpi_(self, global_state):
        state = global_state.mstate
        disassembly = global_state.environment.code
        states = []

        op0, condition = state.stack.pop(), state.stack.pop()

        try:
            jump_addr = util.get_concrete_int(op0)
            # FIXME: to broad exception handler
        except:
            logging.debug("Skipping JUMPI to invalid destination.")
            return [global_state]

        # False case
        negated = simplify(Not(condition)) if type(condition) == BoolRef else condition == 0

        if (type(negated) == bool and negated) or (type(negated) == BoolRef and not is_false(negated)):
            new_state = copy(global_state)
            new_state.mstate.depth += 1
            new_state.mstate.constraints.append(negated)
            states.append(new_state)
        else:
            # print(condition)
            # print("Prunned unreachable false state")
            logging.debug("Pruned unreachable states.")

        # True case

        # Get jump destination
        index = util.get_instruction_index(disassembly.instruction_list, jump_addr)
        if not index:
            logging.debug("Invalid jump destination: " + str(jump_addr))
            return states

        instr = disassembly.instruction_list[index]

        condi = simplify(condition) if type(condition) == BoolRef else condition != 0
        if instr['opcode'] == "JUMPDEST":
            if (type(condi) == bool and condi) or (type(condi) == BoolRef and not is_false(condi)):
                new_state = copy(global_state)
                new_state.mstate.pc = index
                new_state.mstate.depth += 1
                new_state.mstate.constraints.append(condi)

                states.append(new_state)
            else:
                # print(condition)
                # print("Prunned unreachable true state")
                logging.debug("Pruned unreachable states.")

        return states

    @instruction
    def pc_(self, global_state):
        global_state.mstate.stack.append(global_state.mstate.pc - 1)
        return [global_state]

    @instruction
    def msize_(self, global_state):
        global_state.mstate.stack.append(BitVec("msize", 256))
        return [global_state]

    @instruction
    def gas_(self, global_state):
        global_state.mstate.stack.append(BitVec("gas", 256))
        return [global_state]

    @instruction
    def log_(self, global_state):
        # TODO: implement me
        state = global_state.mstate
        dpth = int(self.op_code[3:])
        state.stack.pop(), state.stack.pop()
        [state.stack.pop() for x in range(dpth)]
        # Not supported
        return [global_state]

    @instruction
    def create_(self, global_state):
        state = global_state.mstate
        v, s, l = state.stack.pop(), state.stack.pop(), state.stack.pop()

        global_state.environment.active_account.balance -= v


        try:
            s = util.get_concrete_int(s)
            l = util.get_concrete_int(l)
        except AttributeError:
            logging.debug("Can't MLOAD from symbolic index")
            global_state.mstate.stack.append(1) # To go on with execution
            return [global_state]
        data = ""
        predefined_map = {}
        i = 0
        while i < l:
            try:
                hex_str = hex(state.memory[s+i]).replace("0x", "")
                data += hex_str if len(hex_str) == 2 else "0" + hex_str

            except TypeError:
                predefined_map[i] = state.memory[s+i]
                i += 31
            i += 1

        extension_byte_size = len(predefined_map.keys())*32

        raise CreateNewContractSignal(data, predefined_map, extension_byte_size, global_state, v)


    @instruction
    def return_(self, global_state):
        state = global_state.mstate
        offset, length = state.stack.pop(), state.stack.pop()
        return_data = [BitVec("return_data", 256)]
        try:
            return_data = state.memory[util.get_concrete_int(offset):util.get_concrete_int(offset + length)]
        except AttributeError:
            logging.debug("Return with symbolic length or offset. Not supported")
        global_state.current_transaction.end(global_state, return_data)

    @instruction
    def suicide_(self, global_state):
        return []

    @instruction
    def revert_(self, global_state):
        return []

    @instruction
    def assert_fail_(self, global_state):
        return []

    @instruction
    def invalid_(self, global_state):
        return []

    @instruction
    def stop_(self, global_state):
        global_state.current_transaction.end(global_state)

    @instruction
    def call_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        value = global_state.mstate.stack[-3]
        global_state.environment.active_account.balance -= value
        try:
            callee_address, callee_account, call_data, value, call_data_type, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            # TODO: decide what to do in this case
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]
        callee_account.balance += value
        global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))

        if 0 < int(callee_address, 16) < 5:
            logging.info("Native contract called: " + callee_address)
            if call_data == [] and call_data_type == CalldataType.SYMBOLIC:
                logging.debug("CALL with symbolic data not supported")
                return [global_state]

            try:
                mem_out_start = helper.get_concrete_int(memory_out_offset)
                mem_out_sz = memory_out_size.as_long()
            except AttributeError:
                logging.debug("CALL with symbolic start or offset not supported")
                return [global_state]

            global_state.mstate.mem_extend(mem_out_start, mem_out_sz)
            call_address_int = int(callee_address, 16)
            try:
                data = natives.native_contracts(call_address_int, call_data)
            except natives.NativeContractException:
                contract_list = ['ecerecover', 'sha256', 'ripemd160', 'identity']
                for i in range(mem_out_sz):
                    global_state.mstate.memory[mem_out_start + i] = BitVec(contract_list[call_address_int - 1] +
                                                                           "(" + str(call_data) + ")", 256)

                return [global_state]

            for i in range(min(len(data), mem_out_sz)):  # If more data is used then it's chopped off
                global_state.mstate.memory[mem_out_start + i] = data[i]

            # TODO: maybe use BitVec here constrained to 1
            return [global_state]

        # Todo Annotary CHanged this: storage is set to symbolic
        callee_account.reset_state()

        transaction = MessageCallTransaction(global_state.world_state,
                                             callee_account,
                                             BitVecVal(int(environment.active_account.address, 16), 256),
                                             call_data,
                                             environment.gasprice,
                                             value,
                                             environment.origin,
                                             call_data_type,
                                             can_write=global_state.environment.can_write if hasattr(global_state.environment, "can_write") else True)
        raise TransactionStartSignal(transaction, self.op_code)

    @instruction
    def call_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = BitVec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset, ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size, ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(memory_out_offset, min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = BitVec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]

    @instruction
    def callcode_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, call_data_type, gas, _, _ = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            # CHange to new empty symbolic storage and change the naming of variables
            #delegate = 0
            # todo addition by mythril, delegation can arbitrarely change storage,
            # todo not as trivial, storage vars in constraints must be changed, but how without affecting mythril execution?
            #if global_state.environment.active_account.storage.delegate:
            #    delegate = global_state.environment.active_account.storage.delegate + 1
            global_state.environment.active_account.storage = Storage()
            return [global_state]

        transaction = MessageCallTransaction(global_state.world_state,
                                             environment.active_account,
                                             environment.address,
                                             call_data,
                                             environment.gasprice,
                                             value,
                                             environment.origin,
                                             call_data_type,
                                             callee_account.code,
                                             can_write=global_state.environment.can_write if hasattr(global_state.environment, "can_write") else True
                                             )
        raise TransactionStartSignal(transaction, self.op_code)

    @instruction
    def callcode_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, True)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = BitVec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset, ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size, ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

        # Copy memory
        global_state.mstate.mem_extend(memory_out_offset, min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = BitVec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]


    @instruction
    def delegatecall_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, _, call_data_type, gas, _, _ = get_call_parameters(global_state,
                                                                                                          self.dynamic_loader)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))

            # CHange to new empty symbolic storage and change the naming of variables
            #delegate = 0
            # todo addition by mythril, delegation can arbitrarely change storage,
            # todo not as trivial, storage vars in constraints must be changed, but how without affecting mythril execution?
            #if global_state.environment.active_account.storage.delegate:
            #    delegate = global_state.environment.active_account.storage.delegate + 1
            global_state.environment.active_account.storage = Storage()

            return [global_state]

        transaction = MessageCallTransaction(global_state.world_state,
                                             environment.active_account,
                                             environment.sender,
                                             call_data,
                                             environment.gasprice,
                                             environment.callvalue,
                                             environment.origin,
                                             call_data_type,
                                             callee_account.code,
                                             can_write=global_state.environment.can_write if hasattr(global_state.environment, "can_write") else True
                                             )
        raise TransactionStartSignal(transaction, self.op_code)


    @instruction
    def delegatecall_post(self, global_state):
        instr = global_state.get_current_instruction()

        try:
            _, _, _, _, _, _, memory_out_offset, memory_out_size =\
                get_call_parameters(global_state, self.dynamic_loader)
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

        if global_state.last_return_data is None:
            # Put return value on stack
            return_value = BitVec("retval_" + str(instr['address']), 256)
            global_state.mstate.stack.append(return_value)
            global_state.mstate.constraints.append(return_value == 0)

            return [global_state]

        try:
            memory_out_offset = util.get_concrete_int(memory_out_offset) if isinstance(memory_out_offset,
                                                                                       ExprRef) else memory_out_offset
            memory_out_size = util.get_concrete_int(memory_out_size) if isinstance(memory_out_size,
                                                                                   ExprRef) else memory_out_size
        except AttributeError:
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]

            # Copy memory
        global_state.mstate.mem_extend(memory_out_offset,
                                       min(memory_out_size, len(global_state.last_return_data)))
        for i in range(min(memory_out_size, len(global_state.last_return_data))):
            global_state.mstate.memory[i + memory_out_offset] = global_state.last_return_data[i]

        # Put return value on stack
        return_value = BitVec("retval_" + str(instr['address']), 256)
        global_state.mstate.stack.append(return_value)
        global_state.mstate.constraints.append(return_value == 1)

        return [global_state]

    @instruction
    def staticcall_(self, global_state):
        instr = global_state.get_current_instruction()
        environment = global_state.environment

        try:
            callee_address, callee_account, call_data, value, call_data_type, gas, memory_out_offset, memory_out_size = get_call_parameters(
                global_state, self.dynamic_loader, False) # Only parameter difference to call
        except ValueError as e:
            logging.info(
                "Could not determine required parameters for call, putting fresh symbol on the stack. \n{}".format(e)
            )
            # TODO: decide what to do in this case
            global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))
            return [global_state]
        global_state.mstate.stack.append(BitVec("retval_" + str(instr['address']), 256))

        if 0 < int(callee_address, 16) < 5:
            logging.info("Native contract called: " + callee_address)
            if call_data == [] and call_data_type == CalldataType.SYMBOLIC:
                logging.debug("CALL with symbolic data not supported")
                return [global_state]

            try:
                mem_out_start = helper.get_concrete_int(memory_out_offset)
                mem_out_sz = memory_out_size.as_long()
            except AttributeError:
                logging.debug("CALL with symbolic start or offset not supported")
                return [global_state]

            global_state.mstate.mem_extend(mem_out_start, mem_out_sz)
            call_address_int = int(callee_address, 16)
            try:
                data = natives.native_contracts(call_address_int, call_data)
            except natives.NativeContractException:
                contract_list = ['ecerecover', 'sha256', 'ripemd160', 'identity']
                for i in range(mem_out_sz):
                    global_state.mstate.memory[mem_out_start + i] = BitVec(contract_list[call_address_int - 1] +
                                                                           "(" + str(call_data) + ")", 256)

                return [global_state]

            for i in range(min(len(data), mem_out_sz)):  # If more data is used then it's chopped off
                global_state.mstate.memory[mem_out_start + i] = data[i]

            # TODO: maybe use BitVec here constrained to 1
            return [global_state]

        # Todo Annotary Changed this: storage is set to symbolic
        callee_account.reset_state()

        transaction = MessageCallTransaction(global_state.world_state,
                                             callee_account,
                                             BitVecVal(int(environment.active_account.address, 16), 256),
                                             call_data,
                                             environment.gasprice,
                                             value,
                                             environment.origin,
                                             call_data_type,
                                             can_write=False)
        raise TransactionStartSignal(transaction, self.op_code)
