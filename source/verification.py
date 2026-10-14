from __future__ import annotations
from __future__ import absolute_import
from __future__ import print_function
from pathlib import Path
import re
import uuid
from typeguard import typechecked
import yaml
import json
from optparse import OptionParser
from lark import Lark, tree, Token, Visitor
import math
from datetime import datetime 
from typing import List

from auxilary_variables import AuxVarDict
from config import CONF
from counterexample_checking import VCDAnalyzer
from observations import InitialStateConstraintList, Observation, ObservationList, ObservationPrediction, PreparedObservation, PreparedObservationAtom, PreparedObservationList, collectVars, initObservations, init_initial_state_vars
from verification_environment import VerificationEnvironment
from yosys_cmd_manager import YosysCommandManager
from util import *

# Note the spaces needed for Verilog escaped names
class VBuild:
    def __init__(self):
        pass

    @staticmethod
    @typechecked
    def assert_property(wire_name: str) -> str:
        return f"\t assert property ( {wire_name} );"

    @staticmethod
    @typechecked
    def assume_property(wire_name: str) -> str:
        return f"\t assume property ( {wire_name} );"

    @staticmethod
    @typechecked
    def declare_wire(wire_name: str, expr: str, width: int=1) -> str:
        width_part = "" if width == 1 else "[{}:0] ".format(width - 1)
        return "wire {}{} = {} ;".format(width_part, wire_name, expr)
    
    @staticmethod
    @typechecked
    def build_and(wires: List[str]) -> str:
        if len(wires) == 0:
            return "(1)"
        return " && ".join(["( {} )".format(wire) for wire in wires])
    
    @staticmethod
    @typechecked
    def build_or(wires: List[str]) -> str:
        assert len(wires) > 0, "wires should not be empty"
        return " || ".join(["( {} )".format(wire) for wire in wires])
    
    @staticmethod
    @typechecked
    def build_not(wire: str) -> str:
        return "(! {} )".format(wire)
    
    @staticmethod
    @typechecked
    def on_init(expr: str) -> str:
        return f"( ({CONF.selfCompositionInitVariable} != 1) || ( {expr} ) )"
    
    @staticmethod
    @typechecked
    def on_cycle(cycle_num: int, expr: str) -> str:
        return "( (CYCLE_NUM != {}) || ( {} ) )".format(cycle_num, expr)
    
    @staticmethod
    @typechecked
    def on_both_sides_retire(expr: str) -> str:
        return "(( ! ( Retire_obs_trg_arg0_trg_right && Retire_obs_trg_arg0_trg_left ) ) || ( {} ))".format(expr)

    @staticmethod
    @typechecked
    def left_eq_right(wire_name: str) -> str:
        l = "{}_left".format(wire_name)
        r = "{}_right".format(wire_name)
        return "{} {} {} ".format( l, CONF.selfCompositionEquality, r)


class VerilogConstructor:
    def __init__(self):
        self.exprs = []

    @typechecked
    def add(self, expr: str):
        self.exprs.append(expr)

    @typechecked
    def to_string(self) -> str:
        return "\n".join(self.exprs)
    
    def add_comment(self, comment: str):
        assert "\n" not in comment, "Single line comments should not contain new lines"
        self.exprs.append("// " + comment)
    

####
#### Helper functions for product circuit
####


@typechecked
def equiv_prediction(constr: VerilogConstructor, obs_pred: ObservationPrediction, postfix: str):
    wire_name = "{}_{}".format(obs_pred.id, postfix)
    appl_wire = "{}_{}".format(obs_pred.applicability, postfix)
    attr_wire = "{}_{}".format(obs_pred.observation.var, postfix)

    appl_eq = VBuild.left_eq_right(appl_wire)
    attr_eq = VBuild.left_eq_right(attr_wire)


    appl_r = "{}_{}_right".format(obs_pred.applicability, postfix)

    same_obs = "({} && ((! {}) || ({})))".format(appl_eq, appl_r, attr_eq)

    lft_avail = "{}_{}_left".format(obs_pred.avail, postfix)
    rgt_avail = "{}_{}_right".format(obs_pred.avail, postfix)

    expr = VBuild.build_or([VBuild.build_not(lft_avail), VBuild.build_not(rgt_avail), same_obs])

    constr.add(VBuild.declare_wire(wire_name, expr))

@typechecked
def selfCompositionObservationPredictionEquivalence(constr: VerilogConstructor, wireId: str, obs_predictions: List[ObservationPrediction], prefix: str) -> None:
    assert wireId == "src_equiv"

    for obs_pred in obs_predictions:
        # TODO: this looks extremely sus. I should refactor all those random names into separate classes
        # Like class LeftWireName, etc.
        equiv_prediction(constr, obs_pred, postfix=prefix)

    if len(obs_predictions) > 0:
        # And of all the equivalences of observations
        equiv_cond = VBuild.build_and(["{}_{}".format(obs_pred.id, prefix) for obs_pred in obs_predictions] )
        constr.add(VBuild.declare_wire(wireId, equiv_cond))
    

@typechecked
def selfCompositionObservationEquivalence(constr: VerilogConstructor, wireId: str, obs_list: PreparedObservationList, prefix: str) -> None:
    for obs in obs_list.get_observation_list():
        self_composition_equiv_constraint(constr, obs, prefix)
    if len(obs_list.get_observation_list()) > 0:
        # And of all the equivalences of observations
        equiv_cond = VBuild.build_and(["{}_{}".format(obs.id, prefix) for obs in obs_list.get_observation_list()] )
        if wireId == "src_equiv":
            equiv_cond = VBuild.on_both_sides_retire(equiv_cond)
        constr.add(VBuild.declare_wire(wireId, equiv_cond))

@typechecked
def selfCompositionStateInvariant(wire_id: str, inv_vars: PreparedObservationList, prefix: str, constr: VerilogConstructor):
    for obs in inv_vars.get_observation_list():
        selfCompositionInvsConstraint(constr, obs, prefix)
    if len(inv_vars.get_observation_list()) > 0:
        wires = ["{}_{}".format(obs.id, prefix) for obs in inv_vars.get_observation_list()]
        constr.add(VBuild.declare_wire(wire_id, VBuild.build_and(wires)))

@typechecked
def declare_inductive_state_invariant_wire(constr: VerilogConstructor, obs: PreparedObservation, cstrType: str):
    wire_name = "{}_{}".format(obs.id, cstrType)
    # TODO: I am discarding init, cause it's inductive invariant
    # TODO: Note: I am only checking the property on left
    comb = ["{}_{}_left".format(arg.var, cstrType) for arg in obs.attrs]
    constr.add(VBuild.declare_wire(wire_name, VBuild.build_and(comb)))

@typechecked
def self_composition_inductive_state_invariant(wire_id: str, inductive_inv_vars: PreparedObservationList, prefix: str, constr: VerilogConstructor):
    for obs in inductive_inv_vars.get_observation_list():
        declare_inductive_state_invariant_wire(constr, obs, prefix)
    if len(inductive_inv_vars.get_observation_list()) > 0:
        wires = ["{}_{}".format(obs.id, prefix) for obs in inductive_inv_vars.get_observation_list()]
        constr.add(VBuild.declare_wire(wire_id, VBuild.build_and(wires)))

def selfCompositionAssume(wireId):
    return f"\tassume property ({wireId});\n"

def selfCompositionOnInit(wireId, init, var):
    return  f"\twire {wireId} = ({init} {CONF.selfCompositionInequality} 0) || ({var}) ;\n"

def selfCompositionOnCounter(wireId, counter, var1, var2):
    return  f"\twire {wireId} = ({counter} > 1) || ({var1} && {var2}) ;\n"

@typechecked
def satisfaction_of_initial_state_constraints(wire_id: str, constraints: InitialStateConstraintList, prefix: str):
    constr_str_list = []
    for c in constraints.get_constraints():
        right = "{}_{}_right".format(c.var, prefix)
        left = "{}_{}_left".format(c.var, prefix)
        left_eq_right = "{} {} {}".format(left, CONF.selfCompositionEquality, right)
        constr_str_list.append(left_eq_right)

        if c.val is not None:
            left_eq_val = "{} {} {}".format(left, CONF.selfCompositionEquality, c.val)
            constr_str_list.append(left_eq_val)
    
    return VBuild.declare_wire(wire_id, VBuild.build_and(constr_str_list))

@typechecked
def selfCompositionInvsAttrsConstraint(arg: PreparedObservationAtom, cstrType: str):
    right = "{}_{}_right".format(arg.var, cstrType)
    left = "{}_{}_left".format(arg.var, cstrType)
    res = VBuild.build_and([right, left])
    if arg.init:
        res = VBuild.on_init(res)
    return res

@typechecked
def self_composition_equiv_constraint(constr: VerilogConstructor, observation: PreparedObservation, cstrType: str):
    wire_name = "{}_{}".format(observation.id, cstrType)

    # TODO: I had a bug here, because the first argument was "observation.cond". I think I can avoid such bugs by just 
    cond_wire = "{}_{}".format(observation.cond.var, cstrType)
    cond_eq = VBuild.left_eq_right(cond_wire)

    expr = cond_eq
    if len(observation.attrs) > 0:
        # We only check cond of right, because both are equal
        cond_r = "{}_{}_right".format(observation.cond.var, cstrType)
        attr_eq = VBuild.build_and([VBuild.left_eq_right("{}_{}".format(a.var, cstrType)) for a in observation.attrs])
        expr = "{} && (! {} || ( {} ) )".format(expr, cond_r, attr_eq)

    constr.add(VBuild.declare_wire(wire_name, expr))


@typechecked
def selfCompositionInvsConstraint(constr: VerilogConstructor, obs: PreparedObservation, cstrType: str):
    wire_name = "{}_{}".format(obs.id, cstrType)
    comb = [selfCompositionInvsAttrsConstraint(arg, cstrType) for arg in obs.attrs]
    constr.add(VBuild.declare_wire(wire_name, VBuild.build_and(comb)))

def selfCompositionCycleDelayedCheck(src_obs_list: PreparedObservationList, trg_obs_list: PreparedObservationList, initial_state_constraints: InitialStateConstraintList, state_assumption_vars: PreparedObservationList, inductive_state_invariants_vars: PreparedObservationList, cstrType):
    clock = CONF.clockInput
    trg = trg_obs_list.get_combined_name()
    delayed_trg = "delayed_trg_equiv"
    delayed_trg_now = "delayed_trg_equiv_now"
    # Here I am adding a bit of slack with 5 and 1 to avoid off by one errors
    reg_size = math.floor( math.log2(int(CONF.lookAhead) + 5) ) + 1
    verificationConditions = ""
    verificationConditions += f"\t // CYCLE_NUM goes through 0, 1, ... CONF.lookAhead over the entire execution\n"
    verificationConditions += f"\t reg  [{reg_size} : 0 ] CYCLE_NUM;\n"
    verificationConditions += f"\t wire  [{reg_size} : 0 ] LAST_CYCLE = {CONF.lookAhead};\n"

    verificationConditions += f"\t always @ (posedge {clock}) begin\n"
    verificationConditions += f"\t\t if (CYCLE_NUM <= {CONF.lookAhead}) begin\n"
    verificationConditions += f"\t\t\t CYCLE_NUM <= CYCLE_NUM + 1;\n"
    verificationConditions += f"\t\t end\n"
    verificationConditions += f"\t end\n"

    verificationConditions += f"\t reg {delayed_trg};\n"
    verificationConditions += "\t " + VBuild.declare_wire(delayed_trg_now, VBuild.on_cycle(1, trg)) + "\n"
    verificationConditions += f"\t reg delayed_base_equiv;\n"
    verificationConditions += f"\t always @ (posedge {clock}) begin\n"
    verificationConditions += f"\t\t {delayed_trg} = {delayed_trg} && ({VBuild.on_cycle(1, trg)});\n"
    verificationConditions += f"\t\t delayed_base_equiv <= delayed_base_equiv && {VBuild.on_init(trg)};\n"
    verificationConditions += f"\t end\n"

    verificationConditions += VBuild.assume_property(src_obs_list.get_combined_name()) + "\n"
    verificationConditions += VBuild.assume_property(state_assumption_vars.get_combined_name()) + "\n"

    # TODO: I can add k-induction here
    if CONF.do_inductive_invariant_verification:
        if cstrType == "inductive":
            verificationConditions += VBuild.assume_property(VBuild.on_cycle(0, inductive_state_invariants_vars.get_combined_name())) + "\n"
            verificationConditions += VBuild.assert_property(VBuild.on_cycle(1, inductive_state_invariants_vars.get_combined_name())) + "\n"
        else:
            verificationConditions += VBuild.assume_property(VBuild.on_cycle(0, initial_state_constraints.get_combined_name())) + "\n"
            verificationConditions += VBuild.assert_property(VBuild.on_cycle(0, inductive_state_invariants_vars.get_combined_name())) + "\n"
    else:
        if cstrType == "base":
            verificationConditions += VBuild.assume_property(VBuild.on_cycle(0, initial_state_constraints.get_combined_name())) + "\n"

            # This enforces that delayed_trg_equiv is 1 on init
            verificationConditions += VBuild.assume_property(VBuild.on_init("delayed_base_equiv")) + "\n"
            
            verificationConditions += VBuild.assert_property(VBuild.on_cycle(int(CONF.lookAhead), "delayed_base_equiv")) + "\n"
        elif cstrType == "inductive":
            verificationConditions += VBuild.assume_property(VBuild.on_init(trg)) + "\n"

            # This enforces that delayed_trg_equiv is 1 on init
            verificationConditions += VBuild.assume_property(VBuild.on_init(delayed_trg)) + "\n"
            
            verificationConditions += VBuild.assert_property(VBuild.on_cycle(int(CONF.lookAhead), delayed_trg)) + "\n"
            # This needs to be done if lookahead is 1, cause otherwise it doesn't look fully
            verificationConditions += VBuild.assert_property(VBuild.on_cycle(int(CONF.lookAhead), delayed_trg_now)) + "\n"
        else:
            assert False, "cases are base or inductive"

        verificationConditions += VBuild.assume_property(inductive_state_invariants_vars.get_combined_name()) + "\n"

    # useful for sanity checks and so on
    # verificationConditions += "assert property ((CYCLE_NUM != LAST) || 1'b0);"

    return verificationConditions




@typechecked
def selfCompositionVariableDecl(obs_dict: PreparedObservationList|InitialStateConstraintList, prod_type: str):
    decls = ""
    for b in obs_dict.get_all_blocks():
        wire_base_name = "{}_{}".format(b.var, prod_type)
        if b.width == 1:
            decls += "\twire {}_left ;\n".format(wire_base_name)
            decls += "\twire {}_right ;\n".format(wire_base_name)
        else:
            decls += "\twire [{}:0] {}_left ;\n".format(b.width - 1, wire_base_name)
            decls += "\twire [{}:0] {}_right ;\n".format(b.width - 1, wire_base_name) 
    return decls

class LeftRightInputs:
    def __init__(self):
        self.ids = []
        self.rights = []
        self.lefts = []

    @typechecked
    def add_input(self, id: str, left: str, right: str):
        assert id not in self.ids, "There should not be duplicate ids (I can't deal with them)"
        self.ids.append(id)
        self.lefts.append(left)
        self.rights.append(right)

    @typechecked
    def get_side(self, side) -> List[tuple[str, str]]:
        assert side == "left" or side == "right", "Side must be either left of right"
        if side == "left":
            return list(zip(self.ids, self.lefts))
        else:
            return list(zip(self.ids, self.rights))

@typechecked
def selfCompositionModuleInstantiation(moduleName: str, side: str, vars_map: LeftRightInputs):
    moduleInst = "\t{} {} (\n".format(moduleName, side) 
    varsList = []
    for (var, val) in vars_map.get_side(side):
        varsList += [ ".{} ( {} )".format(var, val)  ]
    moduleInst += ' , \n'.join(["\t\t\t{}".format(var) for var in varsList])
    moduleInst += "\n\t\t);\n"
    return moduleInst

@typechecked
def parseInputs(inputList) -> LeftRightInputs:
    l_r_inputs = LeftRightInputs()
    for i in inputList:
        id = i.get("id")
        left = i.get("valueLeft")
        right = i.get("valueRight")
        l_r_inputs.add_input(id, left, right)
    return l_r_inputs


@typechecked
def constructProductCircuit(common_env: VerificationEnvironment, base_ver_env: VerificationEnvironment, ind_ver_env: VerificationEnvironment, src_obs_list: PreparedObservationList, trg_obs_list: PreparedObservationList, initial_state_constraints: InitialStateConstraintList, state_assumption_vars: PreparedObservationList, inductive_state_invariants_vars: PreparedObservationList, clock, filtertype: str, use_predictor: bool):

    WIRE_DECLARATION_PLACEHOLDER = "//**Wire declarations**//"
    MODULE_DECLARATION_PLACEHOLDER = "//**Self-composed modules**//"
    INITIAL_STATE_PLACEHOLDER = "//**Initial state**//"
    STATE_INVARIANT_PLACEHOLDER = "//**State invariants**//"
    INIT_REGISTER_PLACEHOLDER = "//**Init register**//"
    STUTTERING_SIGNAL_PLACEHOLDER = "//**Stuttering Signal**//"
    VERIFICATION_CONDITIONS_PLACEHOLDER = "//**Verification conditions**//"
    INVARIANT_ASSERTIONS_PLACEHOLDER = "//**Invariant**//"

    # 0. Read product circuit template
    productCircuit_base = ""
    productCircuit_inductive = ""

    with open(common_env.target_path() / CONF.prodCircuitTemplate, 'r') as f:
        productCircuit_base = f.read()
        productCircuit_inductive = productCircuit_base


    # 1. Create wire declarations
    if WIRE_DECLARATION_PLACEHOLDER in productCircuit_base:
        wireDeclaration = ""
        wireDeclaration += "\t// wire declaration\n"
        wireDeclaration += selfCompositionVariableDecl(trg_obs_list,  "trg")
        wireDeclaration += selfCompositionVariableDecl(src_obs_list,  "src")
        wireDeclaration += selfCompositionVariableDecl(initial_state_constraints,  "state") 
        if len(state_assumption_vars.get_observation_list()) > 0:
            wireDeclaration += selfCompositionVariableDecl(state_assumption_vars,  "inv")
        if len(inductive_state_invariants_vars.get_observation_list()) > 0:
            wireDeclaration += selfCompositionVariableDecl(inductive_state_invariants_vars,  "provable_inv")
        wireDeclaration += "\n"
        productCircuit_base = productCircuit_base.replace(WIRE_DECLARATION_PLACEHOLDER, wireDeclaration)
        productCircuit_inductive = productCircuit_inductive.replace(WIRE_DECLARATION_PLACEHOLDER, wireDeclaration)
    else:
        print(f"The product circuit template at {CONF.prodCircuitTemplate} does not contain a placeholder {WIRE_DECLARATION_PLACEHOLDER}")
        exit(1)

    # 2. Init register
    if INIT_REGISTER_PLACEHOLDER in productCircuit_base:
        init = CONF.selfCompositionInitVariable
        initRegister = ""
        initRegister += f"\t // auxiliary register for initial state\n"
        initRegister += f"\t wire {init} = (CYCLE_NUM == 0);\n"
        productCircuit_base = productCircuit_base.replace(INIT_REGISTER_PLACEHOLDER, initRegister)
        productCircuit_inductive = productCircuit_inductive.replace(INIT_REGISTER_PLACEHOLDER, initRegister)
    else:
        init = CONF.initRegister

    # 3.  stuttering signal
    if STUTTERING_SIGNAL_PLACEHOLDER in productCircuit_base:
        stutteringSignal = ""
        stutteringSignal += "\t// Stuttering signal\n"
        stutteringSignal += f"\twire stuttering_left ;\n"
        stutteringSignal += f"\twire stuttering_right ;\n"
        stutteringSignal += f"\tassign stuttering_left = ( Retire_obs_trg_arg0_trg_left && ( ! Retire_obs_trg_arg0_trg_right ) ) ;\n"
        stutteringSignal += f"\tassign stuttering_right = ( Retire_obs_trg_arg0_trg_right && ( ! Retire_obs_trg_arg0_trg_left ) ) ;\n"
        productCircuit_base = productCircuit_base.replace(STUTTERING_SIGNAL_PLACEHOLDER, stutteringSignal)
        productCircuit_inductive = productCircuit_inductive.replace(STUTTERING_SIGNAL_PLACEHOLDER, stutteringSignal)


    # 3. Instantiate modules
    if MODULE_DECLARATION_PLACEHOLDER in productCircuit_base:
        # 3.11 Read inputs
        l_r_inputs = parseInputs(CONF.inputs)

        # 3.2 Modules
        moduleDeclarations = "\t// self-composed modules\n"

        for (name, collection) in [("trg", trg_obs_list), ("src", src_obs_list), ("state", initial_state_constraints), ("inv", state_assumption_vars), ("provable_inv", inductive_state_invariants_vars)]:
            for b in collection.get_all_blocks():
                left = "{}_{}_left".format(b.var, name)
                right = "{}_{}_right".format(b.var, name)
                l_r_inputs.add_input(b.var, left, right)

        moduleDeclarations += selfCompositionModuleInstantiation(CONF.module, "left", l_r_inputs)
        moduleDeclarations += selfCompositionModuleInstantiation(CONF.module, "right", l_r_inputs)
        productCircuit_base = productCircuit_base.replace(MODULE_DECLARATION_PLACEHOLDER, moduleDeclarations)
        productCircuit_inductive = productCircuit_inductive.replace(MODULE_DECLARATION_PLACEHOLDER, moduleDeclarations)
    else:
        print(f"The product circuit template at {CONF.prodCircuitTemplate} does not contain a placeholder {MODULE_DECLARATION_PLACEHOLDER}")
        exit(1)


    # Verification for base case
    # 4. Low-equivalence constraints
    if INITIAL_STATE_PLACEHOLDER in productCircuit_base:
        initial_state = satisfaction_of_initial_state_constraints(initial_state_constraints.get_combined_name(), initial_state_constraints, "state") + "\n"
        productCircuit_base = productCircuit_base.replace(INITIAL_STATE_PLACEHOLDER, initial_state)


    # 5. State invariants constraints

    state_inv_ctr = VerilogConstructor()

    if state_assumption_vars.get_observation_list():
        state_inv_ctr.add_comment("State Assumptions")
        selfCompositionStateInvariant(state_assumption_vars.get_combined_name(), state_assumption_vars, "inv", state_inv_ctr)

    if inductive_state_invariants_vars.get_observation_list():
        self_composition_inductive_state_invariant(inductive_state_invariants_vars.get_combined_name(), inductive_state_invariants_vars, "provable_inv", state_inv_ctr)
        
    if STATE_INVARIANT_PLACEHOLDER in productCircuit_base:
        productCircuit_base = productCircuit_base.replace(STATE_INVARIANT_PLACEHOLDER, state_inv_ctr.to_string())

    if STATE_INVARIANT_PLACEHOLDER in productCircuit_inductive:
        productCircuit_inductive = productCircuit_inductive.replace(STATE_INVARIANT_PLACEHOLDER, state_inv_ctr.to_string())

    
    verification_constr = VerilogConstructor()
    verification_constr.add_comment("\t// contract-equivalence")
    if use_predictor:
        predictions = src_obs_list.parse_predictions()
        selfCompositionObservationPredictionEquivalence(verification_constr, src_obs_list.get_combined_name(), predictions, "src")
    else:
        selfCompositionObservationEquivalence(verification_constr, src_obs_list.get_combined_name(), src_obs_list, "src")
    

    verification_constr.add_comment("\t// verification assertion")
    selfCompositionObservationEquivalence(verification_constr, trg_obs_list.get_combined_name(), trg_obs_list, "trg")

    verification_constr.add_comment("\t// contract-equivalence")

    
    if VERIFICATION_CONDITIONS_PLACEHOLDER in productCircuit_base:
        composition_code = selfCompositionCycleDelayedCheck(src_obs_list, trg_obs_list, initial_state_constraints, state_assumption_vars, inductive_state_invariants_vars, "base")
        productCircuit_base = productCircuit_base.replace(VERIFICATION_CONDITIONS_PLACEHOLDER, verification_constr.to_string() + composition_code)
    else:
        assert False, "No placeholder"

    if VERIFICATION_CONDITIONS_PLACEHOLDER in productCircuit_inductive:
        composition_code = selfCompositionCycleDelayedCheck(src_obs_list, trg_obs_list, initial_state_constraints, state_assumption_vars, inductive_state_invariants_vars, "inductive")
        productCircuit_inductive = productCircuit_inductive.replace(VERIFICATION_CONDITIONS_PLACEHOLDER, verification_constr.to_string() + composition_code)
    else:
        assert False, "No placeholder"
    
    base_ver_env.add_file(CONF.prodCircuitTemplate.replace(".v", "_verification.temp"), productCircuit_base)
    ind_ver_env.add_file(CONF.prodCircuitTemplate.replace(".v", "_verification.temp"), productCircuit_inductive)


@typechecked
def createModule(outFolder: str, module: str, obs_dict: PreparedObservationList|InitialStateConstraintList, inputs_dict: AuxVarDict, suffix: str) -> None:
    input_vars = set()
    output_vars = set()

    for obs_atom in obs_dict.get_all_blocks():
        for v in collectVars(obs_atom.expr):
            assert v in inputs_dict.ids, "Variable {v} not in dictionary of auxiliary variables"
            var = inputs_dict.get_aux_var(v)
            if var.width == 1:
                input_vars.add(v)
            else:
                input_vars.add("[{}:0] {}".format(var.width - 1, v))

        if obs_atom.width == 1:
            output_vars.add(obs_atom.var)
        else:
            output_vars.add("[{}:0] {}".format(obs_atom.width - 1, obs_atom.var))

    moduleSrc = "module {} ".format("{}_{}".format(module, suffix))
    moduleSrc += "( "
    moduleSrc += ' , '.join(["input {}".format(var) for var in input_vars] + ["output {}".format(var) for var in output_vars])
    moduleSrc += " );\n"
    for obs_atom in obs_dict.get_all_blocks():
        moduleSrc += "\tassign {} = {} ;\n".format(obs_atom.var, obs_atom.expr)
    moduleSrc += "endmodule"

    with open("{}/{}_{}.v".format(outFolder, module, suffix) , 'w') as f:
        f.write(moduleSrc)

####
#### Helper variabels for yosys comamnds
####


####
#### Helper functions for verification
#### 

@typechecked
def inlineObservations(yosys_cmd_manager: YosysCommandManager, outFolder, aux_var_dict: AuxVarDict, observations: ObservationList, module, prefix) -> PreparedObservationList:
    print("STARTING FOR PREFIX: ", prefix)
    obs_list = initObservations(observations, aux_var_dict, prefix)
    if len(obs_list.get_observation_list()) > 0:
        ### 4. Create observation module
        createModule(outFolder, module, obs_list, aux_var_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, obs_list, aux_var_dict, "{}".format(prefix))
    print("ENDING FOR PREFIX: ", prefix)
    return obs_list

@typechecked
def inline_initial_state_vars(yosys_cmd_manager: YosysCommandManager, outFolder, aux_var_dict: AuxVarDict, variables, module: str, combined_name: str, prefix: str) -> InitialStateConstraintList:
    ### 3. Build observation dictionary and update auxVars dictionary
    vars_dict = init_initial_state_vars(variables, aux_var_dict, combined_name, prefix)
    
    if len(vars_dict.constraints) > 0:
        ### 4. Create observation module 
        createModule(outFolder, module, vars_dict, aux_var_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, vars_dict, aux_var_dict, "{}".format(prefix))
    return vars_dict

@typechecked
def inlinePipelineInvs(yosys_cmd_manager: YosysCommandManager, outFolder, aux_var_dict: AuxVarDict, invariants: ObservationList, module: str, prefix: str) -> PreparedObservationList:
    ### 3. Build observation dictionary and update auxVars dictionary
    invs_list = initObservations(invariants, aux_var_dict, prefix)
    
    if len(invs_list.get_observation_list()) > 0:
        ### 4. Create observation module 
        createModule(outFolder, module, invs_list, aux_var_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, invs_list, aux_var_dict, "{}".format(prefix))
    return invs_list


####
#### Main verification routine
####

@typechecked
def precomputing(srcObservations: ObservationList, trgObservations: ObservationList, state_assumptions: ObservationList, inductive_state_invariant: ObservationList, auxVars: AuxVarDict, delayed_check_str: str, common_env: VerificationEnvironment, base_ver_env: VerificationEnvironment, ind_ver_env: VerificationEnvironment, usePredictor):
    assert delayed_check_str == "delayedcheck", "I think that what this refers to"
    state = CONF.state
    module = CONF.module

    # construct yosys script
    yosys_cmd_manager = YosysCommandManager()

    log("START")

    time1 = datetime.now()

    ## 1. flatten source and target code
    log(f"Flattening {CONF.module}")
    yosys_cmd_manager.flatten_with_extra_steps(common_env.target_str(), CONF.module)
    time2 = datetime.now()
    logtimefile("\n\t\tTime for flatten the source code: "+ str((time2- time1).seconds))

    ## 2. inline target observations
    log("Inline target observations")
    trg_obs_var = inlineObservations(yosys_cmd_manager, common_env.target_str(), auxVars, trgObservations, module, "obs_trg")

    ## 3. inline source observations
    log("Inline src observations")
    srcObsVar = inlineObservations(yosys_cmd_manager, common_env.target_str(), auxVars, srcObservations, module, "obs_src")

    ## 4. inline state variables
    log("Inline state variables")
    initial_state_constraints = inline_initial_state_vars(yosys_cmd_manager, common_env.target_str(), auxVars, state, module, "init_state_constraints", "state_trg")

    ## 5. inline state invariants
    state_assumption_vars = PreparedObservationList(state_assumptions.get_combined_name())
    if not state_assumptions.is_empty():
        log("Inline state assumptions")
        state_assumption_vars = inlinePipelineInvs(yosys_cmd_manager, common_env.target_str(), auxVars, state_assumptions, module, "state_assumption")

    inductive_state_invariant_vars = PreparedObservationList(inductive_state_invariant.get_combined_name())
    if not inductive_state_invariant.is_empty():
        log("Inline inductive state invariants")
        inductive_state_invariant_vars = inlinePipelineInvs(yosys_cmd_manager, common_env.target_str(), auxVars, inductive_state_invariant, module, "provable_inv")

    ## 6. Create product circuit
    log("Create product circuit")
    constructProductCircuit(common_env, base_ver_env, ind_ver_env, srcObsVar, trg_obs_var, initial_state_constraints, state_assumption_vars, inductive_state_invariant_vars, CONF.clockInput, delayed_check_str, usePredictor)

    time25 = datetime.now()
    logtimefile("\n\t\tTime for create observation circuits and prod circuit: "+ str((time25- time2).seconds))
    ## 7. Finalize
    log("Finalize target module changes")
    yosys_cmd_manager.finalize_module_changes(module, common_env.target_str(), "trg")
    time3 = datetime.now()
    logtimefile("\n\t\tTime for inline observations: "+ str((time3- time25).seconds))

    ## 8. verify contract satisfaction

    log(f"Generate the product circuit for base step")
    base_ver_env.copy_actual_code()
    base_ver_env.add_prod_template(prod_location=base_ver_env.target_path() / "prod_verification.temp")

    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    yosys_cmd_manager = YosysCommandManager()
    yosys_cmd_manager.add_read_verilog_whole_folder(base_ver_env.target_str())
    yosys_cmd_manager.add_hierarchy_with_top(targetName)
    yosys_cmd_manager.add_proc_no_rom()
    yosys_cmd_manager.add_flattening()
    yosys_cmd_manager.add_opt()
    base_output_file_path = "{}/{}_renamed.temp".format(base_ver_env.target_str(), targetName)
    yosys_cmd_manager.export_to_verilog(base_output_file_path)
    base_script_file_path = "{}/yosys-verification_base.script".format(base_ver_env.target_str())
    yosys_cmd_manager.run_from_script(base_script_file_path)
    base_ver_env.un_add_code_files(CONF.moduleFile)

            
    log(f"Generate the product circuit for inductive step")
    ind_ver_env.copy_actual_code()
    ind_ver_env.add_prod_template(prod_location=ind_ver_env.target_path() / "prod_verification.temp")

    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    
    yosys_cmd_manager = YosysCommandManager()
    yosys_cmd_manager.add_read_verilog_whole_folder(ind_ver_env.target_str())
    yosys_cmd_manager.add_hierarchy_with_top(targetName)
    yosys_cmd_manager.add_proc_no_rom()
    yosys_cmd_manager.add_flattening()
    yosys_cmd_manager.add_opt()
    inductive_output_file_path = "{}/{}_renamed.temp".format(ind_ver_env.target_str(), targetName)
    yosys_cmd_manager.export_to_verilog(inductive_output_file_path)
    inductive_script_file_path = "{}/yosys-verification_inductive.script".format(ind_ver_env.target_str())
    yosys_cmd_manager.run_from_script(inductive_script_file_path)
    ind_ver_env.un_add_code_files(CONF.moduleFile)

    time4 = datetime.now()
    logtimefile("\n\t\tTime for generating flattened product circuits: "+ str((time4- time3).seconds))


@typechecked
def verify(specific_env: VerificationEnvironment, trgObservations: ObservationList, case_name: str, filtertype: str, vcd_analyzer: VCDAnalyzer) -> tuple[str, str|None, PreparedObservationList]:
    print("PRADEDU VERIFICATION")

    # 1. replace the right trg_equiv in the prod.
 
    trg_obs = initObservations(trgObservations, AuxVarDict(), "obs_trg")
 
    new_trg_equiv = ""
    if len(trg_obs.observations) > 0:
        new_trg_equiv += "\twire trg_equiv = {} ;\n".format( " && ".join( ["{}_trg ".format(obs.id) for obs in trg_obs.get_observation_list()] ))

    replaced_target_equiv = False
    prod = ""
    TRG_EQUIV_DECL = re.compile(r"^\s*wire\s+trg_equiv\s*=")
    with open(specific_env.target_path() / "prod_verification.temp", "r") as f:
        lines = f.readlines()   
        for line in lines:
            if TRG_EQUIV_DECL.match(line):
                assert not replaced_target_equiv, "Target equivalence should only be replaced once"
                prod += new_trg_equiv
                replaced_target_equiv = True
            else: 
                prod += line
    assert replaced_target_equiv, "Check that replace happened as expected"
    specific_env.add_file(CONF.prodCircuitTemplate, prod)


    # 2. run the BMC to get a ctx or pass
    log("Verification")
    verifMode="yosys-smt"
    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    assert verifMode == "yosys-smt", "The only supported mode"
    if verifMode == "yosys-smt":
        log(f"Verification with {verifMode}")
        log("SMTLib encoding")
        ## Create smtlib encoding with yosys
        time3 = datetime.now()
        yosys_cmd_manager = YosysCommandManager()
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(specific_env.target_str(), CONF.prodCircuitTemplate))
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(specific_env.target_str(), CONF.moduleFile))
        yosys_cmd_manager.add_hierarchy_with_top(targetName)
        yosys_cmd_manager.add_proc_no_rom()
        yosys_cmd_manager.add_flattening()
        yosys_cmd_manager.add_opt()
        
        for yosys_pass in CONF.yosysSMTPreprocessing:
            yosys_cmd_manager.add_string_pass(yosys_pass)
        yosys_cmd_manager.export_to_smt2("{}/{}.smt".format(specific_env.target_str(), targetName), with_wires=True)
        script_path = "{}/yosys-verification.script".format(specific_env.target_str())
        yosys_cmd_manager.run_from_script(script_path)
 
        time4 = datetime.now()
        logtimefile("\n\t\tTime for generating prod.smt: "+ str((time4- time3).seconds))
        log("Bounded model checking")
        cmd = [CONF.yosysBMCPath, "-s", CONF.yosysBMCSolver]
        assert filtertype == "delayedcheck", "The only filtertype that is implemented"
        # both checks are delayed until after the lookahead
        # This ensures that assertions are only checked when the CYCLE_NUM == CONF.lookAhead
        cmd += ["-t", "{}:{}".format(int(CONF.lookAhead), int(CONF.lookAhead) + 1)]
        
        cmd += ["--dump-vlogtb" , "{}/{}_tb.v".format(specific_env.target_str(), targetName)] 
        cmd += ["--dump-smtc", "{}/{}_smtc".format(specific_env.target_str(), targetName)]
        cmd += ["--dump-vcd", str(vcd_analyzer.give_file_name())]
        cmd += ["--noinit"]
        cmd += ["--noincr"]
        cmd += ["{}/{}.smt".format(specific_env.target_str(), targetName)]
        output = run_process(cmd, CONF.verbose_verification)
        time5 = datetime.now()
        logtimefile("\n\t\tTime for BMC: "+ str((time5 - time4).seconds))

        if "Status: FAILED" in output:
            tb_file = "{}/{}_tb.v".format(specific_env.target_str(), targetName)
            log("Verification FAILED")
            export_counter_example(tb_file)
            return "FAIL",tb_file, trg_obs

        elif "Status: PASSED" in output:
            log("Verification PASSED")
            return "PASS", None, trg_obs
        else:
            print("Unknown verification result")
            exit(1)



@typechecked
def verify_invariants(specific_env: VerificationEnvironment, inductive_state_invariant: ObservationList, case_name: str, filtertype: str, 
suffix, vcd_analyzer: VCDAnalyzer) -> tuple[str, str|None, PreparedObservationList]:
    print("PRADEDU VERIFICATION")

    # 1. replace the right trg_equiv in the prod.
 
    ind_state_inv_obs = initObservations(inductive_state_invariant, AuxVarDict(), "inductive_state_invariant")
 
    new_inductive_state_invariant = ""
    if len(ind_state_inv_obs.observations) > 0:
        new_inductive_state_invariant += "\twire inductive_state_invariant = {} ;\n".format( " && ".join( ["{}_{} ".format(obs.id, suffix) for obs in ind_state_inv_obs.get_observation_list()] ))

    replaced_inductive_state_invariant = False
    prod = ""
    IND_STATE_INV_DECL = re.compile(r"^\s*wire\s+inductive_state_invariant\s*=")
    with open(specific_env.target_path() / "prod_verification.temp", "r") as f:
        lines = f.readlines()   
        for line in lines:
            if IND_STATE_INV_DECL.match(line):
                assert not replaced_inductive_state_invariant, "Target equivalence should only be replaced once"
                prod += new_inductive_state_invariant
                replaced_inductive_state_invariant = True
            else: 
                prod += line
    assert replaced_inductive_state_invariant, "Check that replace happened as expected"
    specific_env.add_file(CONF.prodCircuitTemplate, prod)


    # 2. run the BMC to get a ctx or pass
    log("Verification")
    verifMode="yosys-smt"
    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    assert verifMode == "yosys-smt", "The only supported mode"
    if verifMode == "yosys-smt":
        log(f"Verification with {verifMode}")
        log("SMTLib encoding")
        ## Create smtlib encoding with yosys
        time3 = datetime.now()
        yosys_cmd_manager = YosysCommandManager()
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(specific_env.target_str(), CONF.prodCircuitTemplate))
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(specific_env.target_str(), CONF.moduleFile))
        yosys_cmd_manager.add_hierarchy_with_top(targetName)
        yosys_cmd_manager.add_proc_no_rom()
        yosys_cmd_manager.add_flattening()
        yosys_cmd_manager.add_opt()
        
        for yosys_pass in CONF.yosysSMTPreprocessing:
            yosys_cmd_manager.add_string_pass(yosys_pass)
        yosys_cmd_manager.export_to_smt2("{}/{}.smt".format(specific_env.target_str(), targetName), with_wires=True)
        script_path = "{}/yosys-verification.script".format(specific_env.target_str())
        yosys_cmd_manager.run_from_script(script_path)
 
        time4 = datetime.now()
        logtimefile("\n\t\tTime for generating prod.smt: "+ str((time4- time3).seconds))
        log("Bounded model checking")
        cmd = [CONF.yosysBMCPath, "-s", CONF.yosysBMCSolver]
        assert filtertype == "delayedcheck", "The only filtertype that is implemented"

        if case_name == "base":
            cmd += ["-t", "1"]
        elif case_name == "inductive":
            cmd += ["-t", "1:2"]
        else:
            assert False, "case must be base or inductive"
        
        cmd += ["--dump-vlogtb" , "{}/{}_tb.v".format(specific_env.target_str(), targetName)] 
        cmd += ["--dump-smtc", "{}/{}_smtc".format(specific_env.target_str(), targetName)]
        cmd += ["--dump-vcd", str(vcd_analyzer.give_file_name())]
        cmd += ["--noincr"]
        cmd += ["--noinit"]
        cmd += ["{}/{}.smt".format(specific_env.target_str(), targetName)]
        output = run_process(cmd, CONF.verbose_verification)
        time5 = datetime.now()
        logtimefile("\n\t\tTime for BMC: "+ str((time5 - time4).seconds))

        if "Status: FAILED" in output:
            tb_file = "{}/{}_tb.v".format(specific_env.target_str(), targetName)
            log("Verification FAILED")
            export_counter_example(tb_file)
            return "FAIL",tb_file, ind_state_inv_obs

        elif "Status: PASSED" in output:
            log("Verification PASSED")
            return "PASS", None, ind_state_inv_obs
        else:
            print("Unknown verification result")
            exit(1)


