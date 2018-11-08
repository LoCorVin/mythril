from enum import Enum
from re import match, finditer, escape, sub
from functools import reduce
from .transactiontrace import TransactionTrace
from .codeparser import find_matching_closed_bracket, get_pos_line_col
from .coderewriter import expand_rew, after_implicit_block, get_exp_block_brack_pos, get_editor_indexed_rewriting
from mythril.laser.ethereum.transaction.transaction_models import ContractCreationTransaction
from .z3utility import get_function_from_constraints
from .sn_utils import get_si_from_state
from copy import deepcopy
from .debugc import printd

from mythril.laser.ethereum.instructions import keccac_map



ANNOTATION_START = "@"
ANNOTATION_START_REPLACEMENT_NEW = "/*@"
ANNOTATION_STOP = "*/"
annotation_kw = ["check", "invariant", "set_restricted", "ethersink", "ethersource"]


def comment_out_annotations(filename):
    annotation_starts = []
    with open(filename, 'r') as file:
        filedata = file.read()
    for kw in annotation_kw:
        kw_idxs = reversed([kw_idx for kw_idx in finditer(escape(ANNOTATION_START + kw), filedata)])
        for kw_idx in kw_idxs:
            end_idx = kw_idx.end()
            if filedata[end_idx] == "(":
                end_idx = find_matching_closed_bracket(filedata, end_idx) + 1

            annotation_starts.append((kw_idx.start(), kw_idx.start() - 4 * len(annotation_starts)))
            filedata = filedata[:kw_idx.start()] + "/*" + filedata[kw_idx.start():end_idx] + "*/" + filedata[end_idx:]

    printd(filedata)
    with open(filename, 'w') as file:
        file.write(filedata)
    return annotation_starts


def recomment_annotations(filename):
    with open(filename, 'r') as file:
        filedata = file.read()

    for kw in annotation_kw:
        kw_idxs = reversed([kw_idx for kw_idx in finditer(escape(ANNOTATION_START + kw), filedata)])
        for kw_idx in kw_idxs:
            end_idx = kw_idx.end()
            if filedata[end_idx] == "(":
                end_idx = find_matching_closed_bracket(filedata, end_idx) + 1

            filedata = filedata[:kw_idx.start()] + filedata[kw_idx.start() + 2:end_idx] + filedata[end_idx+2:]

    with open(filename, 'w') as file:
        file.write(filedata)


def get_origin_pos_line_col(text): # Todo attentions, new commenting out
    return get_pos_line_col(text.replace(ANNOTATION_START_REPLACEMENT_NEW, ANNOTATION_START).replace("*/", ""))


def get_annotation_content(code, content_start):
    match_annotation_start = match(r'\s*\(', code[content_start:])
    if not match_annotation_start:
        raise SyntaxError("Annotation needs to be properly defined within (...)")
    m_string = match_annotation_start.group()
    closed_idx = find_matching_closed_bracket(code, content_start + len(m_string) - 1)
    return code[(content_start + len(m_string)):closed_idx], len(m_string)


def get_annotated_members(contract, code, start, annotation_length):
    preceded_member = None
    for member in contract.storage_members:
        if start > member.src[0] - contract.contract_range[0] and start <= member.src[0] + member.src[1] - contract.contract_range[0]:
            return [member] # inside_member
        elif start > member.src[0] - contract.contract_range[0] and (not preceded_member or member.src[0] > preceded_member.src[0]):
            preceded_member = member

    semic_idx = code[:start].rfind(';') if ';' in code[:start] else 0
    preceding_nwl_idx = code[:start].rfind('\n') if '\n' in code[:start] else 0


    if preceded_member.src[0] - contract.contract_range[0] > semic_idx:
        return [preceded_member]

    if not preceded_member or preceded_member.src[0] - contract.contract_range[0] + preceded_member.src[1] < preceding_nwl_idx:
        raise SyntaxError("Member Annotation has to be in the same line as parts of a member definition")

    sameline_members = []
    for member in contract.storage_members:
        if member.src[0] - contract.contract_range[0] > preceding_nwl_idx and member.src[0] - contract.contract_range[0] < start:
            sameline_members.append(member)

    return sameline_members



def init_annotation(contract, code, head, kw, start, end, origin):
    if kw == "check":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return CheckAnnotation(code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), origin)
    elif kw == "invariant":
        content, content_prefix = get_annotation_content(code, start + len(head))
        return InvariantAnnotation(contract, code[start:(end + content_prefix)] + content + ")", get_pos_line_col(code[:start]), origin)
    elif kw == "set_restricted":
        content, content_prefix = get_annotation_content(code, start + len(head))
        member_vars = get_annotated_members(contract, code, start, len(head + content) + 2)
        return SetRestrictionAnnotation(contract, code[start:(end + content_prefix)] + content + ")", content,
                member_vars, get_pos_line_col(code[:start]), origin)

    elif kw == "ethersink":
        pass

    elif kw == "ethersource":
        pass


def increase_rewritten_pos(ano_rewritings, rewriting, nwl_type="\n"):
    for ano_rewriting in ano_rewritings:
        nr_nwl = rewriting.text.count(nwl_type)
        if ano_rewriting != rewriting and ano_rewriting.pos >= rewriting.pos:
            ano_rewriting.line += nr_nwl
            ano_rewriting.pos += len( rewriting.text)
            if not ano_rewriting.text.endswith(nwl_type) and ano_rewriting.line == rewriting.line:
                if nwl_type in ano_rewriting.text:
                    ano_rewriting.col += rewriting.text[::-1].index(nwl_type[::-1])
                else:
                    ano_rewriting.col += len(rewriting.text)


def is_mapping_inside_rew(mapping, rewriting):
    return is_mapping_inside_range(mapping, rewriting.pos, rewriting.pos + len(rewriting.text))


def is_mapping_inside_range(mapping, start_pos, end_pos):
    # mapping.lineno == rewriting.line and
    return mapping.offset >= start_pos and mapping.offset < end_pos and mapping.length + mapping.offset <= end_pos


def get_status_string(status):
    if status == Status.HSINGLE:
        return "hsingle"
    elif status == Status.HOLDS:
        return "holds"
    elif status == Status.VDEPTH:
        return "vdepth"
    elif status == Status.VCHAIN:
        return "vchain"
    elif status == Status.VSINGLE:
        return "vsingle"
    elif status == Status.UNCHECKED:
        return "unchecked"


class Status(Enum):
    UNCHECKED = 1 # Execution still has to run
    HSINGLE = 2 # There is a violation but it contains references to storage (maybe a false positive to be ruled out)
    HOLDS = 3 # SAT solver did not find any possible violation
    VDEPTH = 4 # Transaction chaining according to some strategy did not find a chain with constructor in the beginning
    VCHAIN = 5 # Chain with violation in the end and construction trace in the beginning found
    VSINGLE = 6 # violation with no references to storage found.

    # Maybe an additional status: Violating constraints and or storage reference only prev. trans vals or do it in a way
    # that the violation must have existed before the transaction execution.


class Violation:

    def __init__(self, violation, src_mapping, contract, additional = None, length=None, vio_description="", rew_based=True):
        self.vio_description = vio_description
        self.trace = TransactionTrace(violation, contract)

        self.rew_based = rew_based

        self.src_mapping = src_mapping
        self.src_info = contract.get_source_info_from_mapping(self.src_mapping)

        self.lineno = src_mapping.lineno
        self.offset = src_mapping.offset
        self.length = src_mapping.length
        self.code = self.src_info.code
        self.filename = self.src_info.filename

        if length:
            self.length = length

        self.vio_description = vio_description

        self.contract = contract
        self.additional = additional

    def get_dictionary(self, annotation_contract, filename_map):
        origin_file_code = annotation_contract.origin_file_code
        length_prefix_rew = 0
        for rewriting in annotation_contract.rewritings:
            if rewriting.pos <= self.offset:
                length_prefix_rew += len(rewriting.text)
        loc = get_origin_pos_line_col(origin_file_code[:self.offset-length_prefix_rew + (len(self.code) if self.rew_based else 0)])
        if not self.rew_based:
            self.code = origin_file_code.replace("/*", "").replace("*/", "")[loc[0]:loc[0] + self.length]

        return {"level": get_status_string(self.status), "lvl_description": self.get_lvl_description(),
                "filename": filename_map[self.filename] if self.filename in filename_map else self.filename,
                "row": loc[1], "col": loc[2], "code": self.code, "length": 1 if self.rew_based else self.length,
                "pos": loc[0], "vio_description": self.vio_description, "transaction_depth": self.trace.lvl,
                "chained_functions": [{"name": func.name, "signature": func.signature, "isConstructor": func.isConstructor, "visibility": func.visibility} for func in self.trace.functions]}

    def get_lvl_description(self):
        lvl = self.status
        if lvl == Status.UNCHECKED:
            return "This violation was not checked." # Should not happen.
        elif lvl == Status.HSINGLE:
            return "Violation that can be disregarded looking at the single transaction it appears in." # Should not happen.
        elif lvl == Status.HOLDS:
            return "Violation that can be disregarded looking at the context, the other transaction that can be executed to this contract."
        elif lvl == Status.VDEPTH:
            return "A combination of multiple transactions might allow to trigger this violation. Exploring a chain that does this was not possible due to the depth restriction to the analysis. So the violation may not be exploitable."
        elif lvl == Status.VCHAIN:
            return "A combination of multiple transactions allows to exploit this violation of the annotation. However at least two or more transactions are necessary."
        elif lvl == Status.VSINGLE:
            return "This violation can be triggered by executing only one transaction."


class Annotation:

    def __init__(self, annotation_str, status=Status.UNCHECKED):
        self.status = status
        self.annotation_str = annotation_str[annotation_str.index("@"):]
        self.violations = [] # Filled when executing scheck_single_transactions

        self.viol_rews = [] # List of rewritings that contain code to be traceless in the symbolic execution

        # Todo These may not be necessary for the rest of the execution as enter, exit and violating instr.define enough
        self.viol_rew_instrs = [] # list of instructions lists that are associated to the rewriting in the same position

        self.viol_inst = [] # Single instruction that triggers the violation through 'ASSERT_FAIL'
        self.exit_inst = [] # Single instruction that marks end of the violation rewriting, currently a 'JUMPDEST'
        self.enter_inst = [] # First instruction associated to the rewriting in the same position to save state an be ignored

        self.viol_rts = [] #

        self.anotation_contract = None

    def rewrite_code(self, code):
        # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def set_annotation_contract(self, annotation_contract):
        self.annotation_contract = annotation_contract
        self.build_instruction_lists()

    def get_annotation_description(self):
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def build_instruction_lists(self):

        for v_rewriting in self.viol_rews:
            rewriting_rt = "" # Set when first associated instruction is found in constructor or transaction code
            rewriting = get_editor_indexed_rewriting(v_rewriting)
            rew_asm = []
            viol_instr, exit_instr, enter_instr = None, None, None
            if rewriting_rt != 'c':
                for m_idx in range(len(self.annotation_contract.mappings)):
                    mapping = self.annotation_contract.mappings[m_idx]

                    if is_mapping_inside_rew(mapping, rewriting):
                        instr = self.annotation_contract.disassembly.instruction_list[m_idx]
                        rew_asm.append(instr)
                        if not enter_instr:
                            enter_instr = instr
                            instr['is'] = "Enter"
                            rewriting_rt = 't'

                        if instr['opcode'] == 'ASSERT_FAIL':
                            instr['line'] = mapping.lineno
                            viol_instr = instr
                            instr['is'] = "Violation"

                        if 'is' not in instr:
                            instr['is'] = 'Ignore'

            if rewriting_rt != 't':
                for m_idx in range(len(self.annotation_contract.creation_mappings)):
                    mapping = self.annotation_contract.creation_mappings[m_idx]

                    if is_mapping_inside_rew(mapping, rewriting):
                        instr = self.annotation_contract.creation_disassembly.instruction_list[m_idx]
                        rew_asm.append(instr)
                        if not enter_instr:
                            enter_instr = instr
                            instr['is'] = "Enter"
                            rewriting_rt = 'c'

                        if instr['opcode'] == 'ASSERT_FAIL':
                            instr['line'] = mapping.lineno
                            viol_instr = instr
                            instr['is'] = "Violation"

                        if 'is' not in instr:
                            instr['is'] = 'Ignore'

            if rew_asm:
                exit_instr = reduce(lambda x, y: y if y['address'] > x['address'] else x, rew_asm)
                exit_instr['is'] = 'Exit'

            self.viol_rew_instrs.append(rew_asm)

            self.viol_inst.append(viol_instr)
            self.exit_inst.append(exit_instr)
            self.enter_inst.append(enter_instr)

            self.viol_rts.append(rewriting_rt)


    def get_dictionary(self, filename_map):
        adict = {"title": self.title, "level": get_status_string(self.status), "lvl_description": self.get_lvl_description(),
                 "ano_description": self.get_annotation_description(), "pos": self.origin[0], "line": self.origin[1], "col": self.origin[2],
                 "ano_string": self.annotation_str, "length": len(self.annotation_str),
                 "violations": [violation.get_dictionary(self.annotation_contract, filename_map) for violation in self.violations]}
        return adict

    def add_violations(self, violations, src_mapping, contract, additional=None, length=None, vio_description="", rew_based=True): # Ads new violations to this annotation and sets the status, can be called multiple times
        self.violations.extend([Violation(violation, src_mapping, contract, additional, length, vio_description, rew_based) for violation in violations])
        self.status = Status.HSINGLE if self.violations else Status.HOLDS

    def get_creation_ignore_list(self):
        return [(val0, val1, val2, val3, self) for val0, val1, val2, val3, val4 in list(zip(self.enter_inst, self.exit_inst, self.viol_inst, self.viol_rew_instrs, self.viol_rts)) if val4 == 'c']

    def get_trans_ignore_list(self):
        return [(val0, val1, val2, val3, self) for val0, val1, val2, val3, val4 in list(zip(self.enter_inst, self.exit_inst, self.viol_inst, self.viol_rew_instrs, self.viol_rts)) if val4 == 't']

    def get_rewritten_loc(self):
        if hasattr(self, "rewritten_loc"):
            return self.rewritten_loc
        return []

    def build_violations(self, sym_myth):
        pass


    def get_lvl_description(self):
        lvl = self.status
        if lvl == Status.UNCHECKED:
            return "Status of the annotation was not checked jet, nothing can be said about possibly existing violations."
        elif lvl == Status.HSINGLE:
            return "No possible violation found, no operation in a single transaction can be turned into a violation by setting it up via multiple transactions."
        elif lvl == Status.HOLDS:
            return "The other transactions in the contract prevent a violation from being exploitable. Changing the code of a transaction might create a violation in an other transaction."
        elif lvl == Status.VDEPTH:
            return "There are violations to this annotation, but a combination of multiple transactions might allow to trigger them. Exploring these chains was not possible due to the depth restriction to the analysis. So the violation may not be exploitable."
        elif lvl == Status.VCHAIN:
            return "At least one violation has been found were the combination of multiple transactions can lead to a violation of the annotation. However at least two or more transactions are necessary."
        elif lvl == Status.VSINGLE:
            return "At least one violation has been found that can be triggered by executing one single transaction."

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")


class CheckAnnotation(Annotation):

    def __init__(self, annotation_str, loc, origin_loc):
        self.title = "Check annotation"

        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc # Has to be calculated before
        self.rewritings = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        Annotation.__init__(self, annotation_str)

    def get_annotation_description(self):
        return "This annotation checks whether or not the specified condition '" + self.content + "' can be false at " \
            + "this point in the program. An assert is inserted and symbolic execution tries to find falsifying " \
            + "assigments. The presence of the assert statement does not influence the later execution."

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        assert_rew = expand_rew(code, ("assert(" + self.content + ");", self.loc[0]))
        if after_implicit_block(code, self.loc[0]):
            start, end = get_exp_block_brack_pos(code, self.loc[0])
            self.rewritings.append(expand_rew(code, ("{", start)))
            self.rewritings.append(assert_rew)
            self.rewritings.append(expand_rew(code, ("}", end)))
        else:
            self.rewritings.append(assert_rew)

        self.viol_rews.append(assert_rew)
        return self.rewritings

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

class InvariantAnnotation(Annotation):


    def __init__(self, contract, annotation_str, loc, origin_loc):
        self.title = "Invariant annotation"

        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc

        self.rewritings = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]

        if not hasattr(contract, 'functions'):
            raise RuntimeError("Contract not augmented with functions parsed from ast")
        self.functions = contract.functions

        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range): # In the default case it returns '' empty string, to delete it before handing it over to the compiler
        assertion_text = "assert(" + self.content + ");"
        for function in self.functions:
            if function.constant == True: # Dont' build invariant assertions for functions that do not change storage and thus do not change invariants
                continue
            for term_pos in function.terminating_pos:

                assertion_rew = expand_rew(code, (assertion_text, term_pos[0]))
                if after_implicit_block(code, term_pos[0]):
                    start, end = get_exp_block_brack_pos(code, term_pos[0])

                    self.rewritings.append(expand_rew(code, ("{", start)))
                    self.rewritings.append(expand_rew(code, ("}", end)))

                if term_pos[1] > 0:
                    ret_end = term_pos[0] + term_pos[1]
                    if not code[:ret_end].strip().endswith(';'):
                        inc_pos = code[ret_end:].index(";") + 1
                        ret_end += inc_pos
                    return_content = code[term_pos[0]:ret_end]
                    if return_content.startswith("return"):
                        return_content = return_content[len("return"):].strip()
                    if return_content.endswith(';'):
                        return_content = return_content[:len(return_content) - 1].strip()
                    if return_content:
                        ret_var = "("
                        for ret_idx in range(len(function.return_types)):
                            ret_var += "sol_retvar_" + str(term_pos[0]) + "_" + str(ret_idx) + ","
                        ret_var = ret_var[:len(ret_var)-1] + ")"

                        self.rewritings.append(expand_rew(code, ("var " + ret_var + "="+return_content+";", term_pos[0])))
                        self.rewritings.append(assertion_rew)
                        self.rewritings.append(expand_rew(code, ("return " + ret_var + "; /*", term_pos[0])))
                        self.rewritings.append(expand_rew(code, ("*/", ret_end)))
                    else:
                        self.rewritings.append(assertion_rew)
                else:
                    self.rewritings.append(assertion_rew)
                self.viol_rews.append(assertion_rew)

        return self.rewritings


    def get_annotation_description(self):
        return "This annotation represents an invariant that should hold after every finished transaction execution. The" \
            + " annotations condition '" + self.content + "' is checked by inserting an assert statement at the exit " \
            + "points of every transaction function that can be executed by a transaction and do change the contracts states."



    def build_violations(self, sym_myth):
        pass

    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")

class SetRestrictionAnnotation(Annotation):

    # Any function name, or signature, 'constructor' or contract name for constructor, empty content or '()' as parameter

    def __init__(self, contract, annotation_str, content, member_variables, loc, origin_loc):
        self.title = "Set restriction annotation"

        self.annotation_str = annotation_str
        self.loc = loc
        self.origin = origin_loc

        self.rewritings = []

        self.content = annotation_str[(annotation_str.index("(") + 1):][::-1]
        self.content = self.content[(self.content.index(")") + 1):][::-1]




        self.restricted_f = []
        self.storage_slot_map = {}
        self.contract = contract
        for restriction in content.split(","):
            restriction = sub('\s','',restriction)
            self.restricted_f.append(restriction)

        for m_var in member_variables:
            self.storage_slot_map[m_var.name] = contract.storage_map[m_var.name]

        self.member_variables = member_variables

        # Todo get all storage slots from storage map
        Annotation.__init__(self, annotation_str)

    def rewrite_code(self, code, contract_range):
        return []

    def build_violations(self, sym_myth):
        violations = []
        for _, node in sym_myth.nodes.items():
            for state in node.states:
                if state.instruction['opcode'] == "SSTORE":
                    function = None
                    is_fallback = False
                    in_constructor = isinstance(state.current_transaction, ContractCreationTransaction)
                    if not in_constructor:
                        function = get_function_from_constraints(self.contract, state.mstate.constraints, isinstance(state.current_transaction, ContractCreationTransaction))
                        if function:
                            printd(function.name)
                        else:
                            try:
                                function = list(filter(lambda f: f.name == "", self.contract.functions))[0]
                            except IndexError:
                                raise SyntaxError("Targeted unexisting fallback function")
                            is_fallback = True # Todo Don't forget to add fallback
                    # Skipp if function is somehow mentioned in the restricted list
                    if function and (function.name in self.restricted_f or function.signature in self.restricted_f) or in_constructor and ("constructor" in self.restricted_f
                        or self.contract.name in self.restricted_f or any([restriction.startswith(self.contract.name + "(") for restriction in self.restricted_f])):
                        continue
                    for member_name, storage_slots in self.storage_slot_map.items():
                        for storage_slot in storage_slots:
                            may_write_to, constraints = storage_slot.may_write_to(state.mstate.stack[-1], state.mstate.stack[-2], state.environment.active_account.storage._storage, state.mstate.constraints)
                            if may_write_to:
                                # Todo Add more information to the single violation, e.g. here, which variable is or may be overwritten
                                src_info, mapping = get_si_from_state(self.annotation_contract, state.instruction['address'], state)
                                printd("Contract may write to forbidden slot: " + str(src_info.lineno) + ":: " + src_info.code)
                                new_state = state
                                if constraints and len(constraints) > 0:
                                    new_state = deepcopy(state) # update with the assumtion taken by the may_write
                                    new_state.mstate.constraints.extend(constraints)
                                self.add_violations([new_state], mapping, self.contract, member_name,
                                    vio_description="This statement may write to the member variable '" + storage_slot.member.name
                                                    + "' of type '" + storage_slot.member.type+"' although not allowed by the annotation: " + str(self.annotation_str), rew_based=False)


    def trans_violations_check(self, sym_tran, sym_con): # Or should i get the predfiltered transaction or even builded chains here
        raise NotImplementedError("Abstract function of Annotation abstraction")

    def get_violations_description(self): # Returns a tuple or list of tuples with description, assoviated line and string to highlight.
        raise NotImplementedError("Abstract function of Annotation abstraction")


    def get_annotation_description(self):
        return "This annotation binds a restriction to one or more member variables in the contract and uses symbolic " \
               "execution to find executions were this restriction is violated. If the annotation is inside of a single" \
               " member variable declaration statement, the restriction is bound only to that variable. If not it applies" \
               "to all variables declared in the same line. \n This annotation restricts setting values or content of the " \
               "variables: " + ", ".join([mv.type + " " + mv.name for mv in self.member_variables]) + " to the specified function names or signatures: \n" + self.content



