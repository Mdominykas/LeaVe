from __future__ import absolute_import
from __future__ import print_function
from pathlib import Path
from typeguard import typechecked
import yaml
import json
from optparse import OptionParser
from lark import Lark, tree, Token, Visitor
import math
from datetime import datetime 
from typing import List

from config import CONF, SourceObservationPrediction
from observations import collectVars, initAuxVars, initMetaVars, initObservations, initStateVars
from yosys_cmd_manager import YosysCommandManager
from util import *


####
#### Helper functions for product circuit
####

# pagal: selfCompositionEquivConstraint
@typechecked
def equivPrediction(obs_pred: SourceObservationPrediction, postfix):
    cond = obs_pred.cond
    avail = obs_pred.avail
    attr = obs_pred.attr

    wire_name = "{}_{}".format(obs_pred.id, postfix)

    lft_cond = "{}_{}_left".format(cond, postfix)
    rgt_cond = "{}_{}_right".format(cond, postfix)
    eq = CONF.selfCompositionEquality
    cond_eq = "({} {} {})".format(lft_cond, eq, rgt_cond)

    lft_attr = "{}_{}_left".format(attr, postfix)
    rgt_attr = "{}_{}_right".format(attr, postfix)
    attr_eq = "({} {} {})".format(lft_attr, eq, rgt_attr)

    lft_avail = "{}_{}_left".format(avail, postfix)
    rgt_avail = "{}_{}_right".format(avail, postfix)

    same_obs = "({} && ((! {}) || ({})))".format(cond_eq, lft_cond, attr_eq)

    constraint = "wire {} = (! {}) || (! {}) || ({});".format(wire_name, lft_avail, rgt_avail, same_obs)
    return constraint

@typechecked
def selfCompositionObservationPredictionEquivalence(wireId, obsDict, prefix):
    assert wireId == "src_equiv"

    combined_values = {}
    AVAIL_PREF = "avail_"
    for pos_obs_id, obs_val in obsDict.items():
        if pos_obs_id.startswith(AVAIL_PREF):
            obs_id = pos_obs_id[len(AVAIL_PREF):]
            if obs_id not in combined_values:
                combined_values[obs_id] = SourceObservationPrediction()
            combined_values[obs_id].id = obs_id
            combined_values[obs_id].avail = obs_val[0]["var"]
            assert combined_values[obs_id].avail.endswith("_obs_src_cond")
        else:
            obs_id = pos_obs_id
            if obs_id not in combined_values:
                combined_values[obs_id] = SourceObservationPrediction()
            combined_values[obs_id].id = obs_id

            combined_values[obs_id].cond = obs_val[0]["var"]
            assert combined_values[obs_id].cond.endswith("_obs_src_cond")

            combined_values[obs_id].attr = obs_val[1]["var"]
            assert combined_values[obs_id].attr.endswith("_obs_src_arg0")
    
    src_obs_predictions: List[SourceObservationPrediction] = [val for val in combined_values.values()]

    condition = ""
    for obs_pred in src_obs_predictions:
        condition += "\t{}\n".format(equivPrediction(obs_pred, prefix))

    if len(src_obs_predictions) > 0:
        condition+="\twire {} = ( {} ) ;\n".format(wireId, " && ".join( ["{}_{}".format(src_obs_prediction.id, prefix) for src_obs_prediction in src_obs_predictions ] ))
    
    return condition

def selfCompositionObservationEquivalence(wireId, obsDict, prefix):
    condition = ""
    for obsId in obsDict.keys():
        condition += "\t{}\n".format(selfCompositionEquivConstraint(obsId, obsDict[obsId], prefix))
    if len(obsDict.keys()) > 0:
        if wireId == "src_equiv":
            condition+="\twire {} = ( ! ( Retire_obs_trg_arg0_trg_right && Retire_obs_trg_arg0_trg_left ) ) || ( {} ) ;\n".format(wireId, " && ".join( ["{}_{}".format(obsId, prefix) for obsId in obsDict.keys() ] ))
        else:
            condition+="\twire {} = {} ;\n".format(wireId, " && ".join( ["{}_{}".format(obsId, prefix) for obsId in obsDict.keys() ] ))
        return condition
    else:
        return ""

def selfCompositionStateInvariant(wireId, invVars, prefix):
    condition = ""
    for obsId in invVars.keys():
        condition += "\t{}\n".format(selfCompositionInvsConstraint(obsId, invVars[obsId], prefix))
    if len(invVars.keys()) > 0:
        condition+="\twire {} = {} ;\n".format(wireId, " && ".join( ["{}_{}".format(obsId, prefix) for obsId in invVars.keys() ] ))
        return condition
    else:
        return ""


def selfCompositionAssume(wireId):
    return f"\tassume property ({wireId});\n"

def selfCompositionAssert(wireId):
    return f"\tassert property ({wireId});\n"

def selfCompositionOnInit(wireId, init, var):
    return  f"\twire {wireId} = ({init} {CONF.selfCompositionInequality} 0) || ({var}) ;\n"

def selfCompositionOnCounter(wireId, counter, var1, var2):
    return  f"\twire {wireId} = ({counter} > 1) || ({var1} && {var2}) ;\n"

def selfCompositionVariableEquivalence(wireId, vars, prefix):
    args1 = []  # without init value
    args2 = []  # with init value
    val = {}
    for varId in vars.keys():
        for var in vars[varId]:
            if  var.get("val") == None or var.get("val") == "":
                args1.append(var.get("var"))
            else:
                args2.append(var.get("var"))
                val[var.get("var")] = var.get("val")

    if len(vars.keys()) > 0:
        constraint = ""
        constraint += "\twire {} =  {} ;\n".format(wireId, 
                    " && ".join(
                        [ "{} {} {}".format("{}_{}_right".format(arg,prefix), CONF.selfCompositionEquality, "{}_{}_left".format(arg,prefix)) for arg in args1 + args2]
                        +
                        [ "{} {} {}".format("{}_{}_right".format(arg,prefix), CONF.selfCompositionEquality, val[arg]) for arg in args2]
                        ) )
        return constraint
    else:
        return ""

def selfCompositionAttrsConstraint(arg, cstrType):
    constraint = "" 
    
    constraint = "{} {} {}".format("{}_{}_right".format(arg.get("var"), cstrType), CONF.selfCompositionEquality, "{}_{}_left".format(arg.get("var"), cstrType))
    return constraint


def selfCompositionInvsAttrsConstraint(arg, cstrType):
    constraint = "" 
    if arg.get("init") == "1":
        constraint = "( (init != 0) || ( {} && {} ) )".format("{}_{}_right".format(arg.get("var"), cstrType), "{}_{}_left".format(arg.get("var"), cstrType))
    else:
        constraint = "( {} && {} )".format("{}_{}_right".format(arg.get("var"), cstrType), "{}_{}_left".format(arg.get("var"), cstrType))
    return constraint

def selfCompositionEquivConstraint(obsId, observations, cstrType):
    args = []
    for obs in observations:
        if obs.get("var").endswith("_cond"):
            cond = obs.get("var")
        else:
            args.append(obs)
            
    if len(args) == 0:
        constraint = "wire {}_{} = {} {} {} ;".format( obsId, cstrType, "{}_{}_right".format(cond, cstrType), CONF.selfCompositionEquality, 
        "{}_{}_left".format(cond, cstrType) )
    else:
        constraint = "wire {}_{} = {} {} {} && (! {} || ( {} ) ) ;".format(obsId, cstrType, "{}_{}_right".format(cond, cstrType), CONF.selfCompositionEquality,
            "{}_{}_left".format(cond, cstrType), "{}_{}_right".format(cond, cstrType), 
            " && ".join([selfCompositionAttrsConstraint(arg, cstrType) for arg in args]) )
    return constraint

def selfCompositionInvsConstraint(obsId, observations, cstrType):
    args = []
    for obs in observations:
        if obs.get("var").endswith("_cond"):
            cond = obs.get("var")
        else:
            args.append(obs)

    constraint = "wire {}_{} = {} ;".format(obsId, cstrType, " && ".join([selfCompositionInvsAttrsConstraint(arg, cstrType) for arg in args]) )
    return constraint


def selfCompositionCycleDelayedCheck(clock, delay, cstrType):
    verificationConditions = ""
    verificationConditions += "\t// auxiliary register for Bound and Counter\n"
    if cstrType == "base":
        verificationConditions += f"\treg  [{ math.floor( math.log2(int(delay) + 1) ) + 1} : 0 ] bound = {delay};\n"
        verificationConditions += f"\treg  [{ math.floor( math.log2(int(delay) + 1) ) + 1} : 0 ] counter = 1;\n"
    elif cstrType == "inductive":
        verificationConditions += f"\treg  [{ math.floor( math.log2(int(delay) + 1) ) + 1} : 0 ] bound = {delay} + 1 ;\n"
        verificationConditions += f"\treg  [{ math.floor( math.log2(int(delay) + 1) ) + 1} : 0 ] counter = 2;\n"
    verificationConditions += "\talways @ (posedge {}) begin\n".format(clock)
    verificationConditions += f"\t\tif (counter > 0) begin\n"
    verificationConditions += f"\t\t\tcounter <= counter - 1;\n"
    verificationConditions += "\t\tend\n"
    verificationConditions += f"\t\tif (bound > 0) begin\n"
    verificationConditions += f"\t\t\tbound <= bound - 1;\n"
    verificationConditions += "\t\tend\n"
    verificationConditions += "\tend\n"

    verificationConditions += "\t// update the states for verification\n"
    verificationConditions += f"\treg state_trg_equiv = 1;\n"
    verificationConditions += f"\treg init_state_trg_equiv = 1;\n"
    verificationConditions += "\talways @ (posedge {}) begin\n".format(clock)
    verificationConditions += f"\t\tif (counter > 0) begin\n"
    verificationConditions += f"\t\t\tstate_trg_equiv <= state_trg_equiv && trg_equiv;\n"
    verificationConditions += "\t\tend\n"

    if cstrType == "inductive":
        verificationConditions += f"\t\tif (counter > 1) begin\n"
        verificationConditions += f"\t\t\tinit_state_trg_equiv <= init_state_trg_equiv && trg_equiv;\n"
        verificationConditions += "\t\tend\n"

    verificationConditions += "\tend\n\n"
    verificationConditions += "\twire fin_state_trg_equiv = ( bound > 0 ) ||  state_trg_equiv ;\n"
    
    if cstrType == "inductive":
        verificationConditions += selfCompositionAssume("init_state_trg_equiv")
    elif cstrType == "base":
        verificationConditions += selfCompositionAssume("init_state_equiv")
    verificationConditions += selfCompositionAssume("src_equiv")
    verificationConditions += selfCompositionAssume("state_invariant")
    verificationConditions += selfCompositionAssert("fin_state_trg_equiv")

    return verificationConditions



def selfCompositionPrefixCheck(clock, bound, filtertype = "nondelayed"):
    verificationConditions = ""
    verificationConditions += "\t// auxiliary register for Counter\n"
    verificationConditions += f"\treg  [{ math.floor( math.log2(int(bound)) ) + 1} : 0 ] counter = {bound};\n"
    verificationConditions += "\talways @ (posedge {}) begin\n".format(clock)
    verificationConditions += f"\t\tcounter <= counter - 1;\n"
    verificationConditions += "\tend\n"

    verificationConditions += "\t// update the states for verification\n"
    verificationConditions += f"\treg state_src_equiv = 1;\n"
    verificationConditions += f"\treg state_trg_equiv = 1;\n"
    verificationConditions += "\talways @ (posedge {}) begin\n".format(clock)
    verificationConditions += f"\t\tstate_src_equiv <= state_src_equiv && src_equiv;\n"
    verificationConditions += f"\t\tstate_trg_equiv <= state_trg_equiv && trg_equiv;\n"
    verificationConditions += "\tend\n\n"
    if filtertype =="nondelayed":
        verificationConditions += selfCompositionOnCounter("counter_state_src_equiv", "counter", "state_src_equiv", "src_equiv")
    else:
        verificationConditions += selfCompositionOnCounter("counter_state_src_equiv", "counter", "state_src_equiv", "1")
    verificationConditions += selfCompositionAssume("counter_state_src_equiv")
    verificationConditions += selfCompositionOnCounter("init_state_trg_equiv", "counter", "state_trg_equiv", "1")
    verificationConditions += selfCompositionAssume("init_state_trg_equiv")
    verificationConditions += selfCompositionOnCounter("counter_state_trg_equiv", "counter", "state_trg_equiv", "trg_equiv")
    verificationConditions += selfCompositionAssert("counter_state_trg_equiv")
    verificationConditions += "\n"
    return verificationConditions



def selfCompositionVariableDecl(obsDict,  prodType):
    decls = ""
    for obsId in obsDict.keys():
        for obs in obsDict[obsId]:
            var = obs.get("var")
            if obs.get("width") == 1:
                decls += "\twire {}_{}_left ;\n".format(var,prodType)
                decls += "\twire {}_{}_right ;\n".format(var,prodType)
            else:
                decls += "\twire [{}:0] {}_{}_left ;\n".format(obs.get("width")-1, var,prodType)  
                decls += "\twire [{}:0] {}_{}_right ;\n".format(obs.get("width")-1, var,prodType) 
    return decls

def selfCompositionModuleInstantiation(moduleName, side, varsMap):
    moduleInst = "\t{} {} (\n".format(moduleName, side) 
    varsList = []
    for var in varsMap.keys():
            varsList += [ ".{} ( {} )".format(var, varsMap[var])  ]
    moduleInst += ' , \n'.join(["\t\t\t{}".format(var) for var in varsList])
    moduleInst += "\n\t\t);\n"
    return moduleInst

def parseInputs(inputList):
    leftDict = {}
    rightDict = {}
    for i in inputList:
        inputId = i.get("id")
        leftDict[inputId] = i.get("valueLeft")
        rightDict[inputId] = i.get("valueRight")
    return leftDict, rightDict


def constructProductCircuit(outFolder, srcObsVar, trgObsVar, state, invVars, clock, filtertype, usePredictor):

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

    with open("{}/{}".format(outFolder, CONF.prodCircuitTemplate) , 'r') as f:
        productCircuit_base = f.read()
        productCircuit_inductive = productCircuit_base


    # 1. Create wire declarations
    if WIRE_DECLARATION_PLACEHOLDER in productCircuit_base:
        wireDeclaration = ""
        wireDeclaration += "\t// wire declaration\n"
        wireDeclaration += selfCompositionVariableDecl(trgObsVar,  "trg")
        wireDeclaration += selfCompositionVariableDecl(srcObsVar,  "src")
        wireDeclaration += selfCompositionVariableDecl(state,  "state") 
        if invVars:
            wireDeclaration += selfCompositionVariableDecl(invVars,  "inv")         
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
        initRegister += "\t// auxiliary register for initial state\n"
        initRegister += f"\treg {init} = 0;\n"
        initRegister += "\talways @ (posedge {}) begin\n".format(clock)
        initRegister += f"\t\tif ({init} == 0) begin\n"
        initRegister += f"\t\t\t{init} <= 1;\n"
        initRegister += "\t\tend\n"
        initRegister += "\tend\n"
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
        leftVarMap, rightVarMap = parseInputs(CONF.inputs)

        # 3.2 Modules
        moduleDeclarations = "\t// self-composed modules\n"

        for obsId in trgObsVar:
            for obs in trgObsVar[obsId]:
                leftVarMap[obs["var"]] = "{}_trg_left".format(obs["var"])
                rightVarMap[obs["var"]] = "{}_trg_right".format(obs["var"])

        for obsId in srcObsVar:
            for obs in srcObsVar[obsId]:
                leftVarMap[obs["var"]] = "{}_src_left".format(obs["var"])
                rightVarMap[obs["var"]] = "{}_src_right".format(obs["var"])

        for obsId in state:
            for obs in state[obsId]:
                leftVarMap[obs["var"]] = "{}_state_left".format(obs["var"])
                rightVarMap[obs["var"]] = "{}_state_right".format(obs["var"])

        for obsId in invVars:
            for obs in invVars[obsId]:
                leftVarMap[obs["var"]] = "{}_inv_left".format(obs["var"])
                rightVarMap[obs["var"]] = "{}_inv_right".format(obs["var"])

        moduleDeclarations += selfCompositionModuleInstantiation(CONF.module, "left", leftVarMap)
        moduleDeclarations += selfCompositionModuleInstantiation(CONF.module, "right", rightVarMap)
        productCircuit_base = productCircuit_base.replace(MODULE_DECLARATION_PLACEHOLDER, moduleDeclarations)
        productCircuit_inductive = productCircuit_inductive.replace(MODULE_DECLARATION_PLACEHOLDER, moduleDeclarations)
    else:
        print(f"The product circuit template at {CONF.prodCircuitTemplate} does not contain a placeholder {MODULE_DECLARATION_PLACEHOLDER}")
        exit(1)


    # Verification for base case
    # 4. Low-equivalence constraints
    if INITIAL_STATE_PLACEHOLDER in productCircuit_base:
        initial_state = ""
        if len(state) > 0:
            initial_state += "\t// Initial state\n"
            initial_state += selfCompositionVariableEquivalence("state_equiv", state, "state")
            initial_state += selfCompositionOnInit("init_state_equiv", init, "state_equiv")
            #initial_state += selfCompositionAssume("init_state_equiv")
            initial_state += "\n"
        productCircuit_base = productCircuit_base.replace(INITIAL_STATE_PLACEHOLDER, initial_state)


    # 5. State invariants constraints
    if STATE_INVARIANT_PLACEHOLDER in productCircuit_base:
        state_invariant = ""
        if len(invVars) > 0:
            state_invariant += "\t// State invariant\n"
            state_invariant += selfCompositionStateInvariant("state_invariant", invVars, "inv")
            #state_invariant += selfCompositionAssume("state_invariant")
            state_invariant += "\n"
        productCircuit_base = productCircuit_base.replace(STATE_INVARIANT_PLACEHOLDER, state_invariant)
    

    if VERIFICATION_CONDITIONS_PLACEHOLDER in productCircuit_base:
        verificationConditions = ""
        if filtertype == "delayedcheck":
            # 5. contract equivalence
            verificationConditions += "\t// contract-equivalence\n"
            if usePredictor:
                verificationConditions += selfCompositionObservationPredictionEquivalence("src_equiv", srcObsVar, "src")
            else:
                verificationConditions += selfCompositionObservationEquivalence("src_equiv", srcObsVar, "src")
            verificationConditions += "\n"
            # 6. target equivalence
            verificationConditions += "\t// verification assertion\n"
            verificationConditions += selfCompositionObservationEquivalence("trg_equiv", trgObsVar, "trg")
            verificationConditions += "\n"

            verificationConditions += "\t// contract-equivalence\n"
            verificationConditions += selfCompositionCycleDelayedCheck(clock, CONF.lookAhead, "base")
            verificationConditions += "\n"
        else:
            if len(state) > 0:
                verificationConditions += selfCompositionAssume("init_state_equiv")
            if len(invVars) > 0:
                verificationConditions += selfCompositionAssume("state_invariant")

            # 6. target equivalence
            verificationConditions += "\t// verification assertion\n"
            verificationConditions += selfCompositionObservationEquivalence("trg_equiv", trgObsVar, "trg")
            verificationConditions += "\n"
            verificationConditions += selfCompositionAssert("trg_equiv")
            verificationConditions += "\n"

        productCircuit_base = productCircuit_base.replace(VERIFICATION_CONDITIONS_PLACEHOLDER, verificationConditions)


    # Verification for inductive step
            # 5. Pipeline invariants constraints
    if STATE_INVARIANT_PLACEHOLDER in productCircuit_inductive:
        state_invariant = ""
        if len(invVars) > 0:
            state_invariant += "\t// Pipeline invariant\n"
            state_invariant += selfCompositionStateInvariant("state_invariant", invVars, "inv")
            #state_invariant += selfCompositionAssume("state_invariant")
            state_invariant += "\n"
        productCircuit_inductive = productCircuit_inductive.replace(STATE_INVARIANT_PLACEHOLDER, state_invariant)

    if VERIFICATION_CONDITIONS_PLACEHOLDER in productCircuit_inductive:
        verificationConditions = ""
        assert filtertype == "delayedcheck", "The only check that is implemented"
        if filtertype == "delayedcheck":
            # 5. contract equivalence
            verificationConditions += "\t// contract-equivalence\n"
            if usePredictor:
                verificationConditions += selfCompositionObservationPredictionEquivalence("src_equiv", srcObsVar, "src")
            else:
                verificationConditions += selfCompositionObservationEquivalence("src_equiv", srcObsVar, "src")
            verificationConditions += "\n"
            # 6. target equivalence
            verificationConditions += "\t// verification assertion\n"
            verificationConditions += selfCompositionObservationEquivalence("trg_equiv", trgObsVar, "trg")
            verificationConditions += "\n"

            verificationConditions += "\t// contract-equivalence\n"
            verificationConditions += selfCompositionCycleDelayedCheck(clock, CONF.lookAhead, "inductive")
            verificationConditions += "\n"

        productCircuit_inductive = productCircuit_inductive.replace(VERIFICATION_CONDITIONS_PLACEHOLDER, verificationConditions)
    else:
        print(f"The product circuit template at {CONF.prodCircuitTemplate} does not contain a placeholder {VERIFICATION_CONDITIONS_PLACEHOLDER}")
        exit(1)

    with open("{}/{}".format(outFolder, CONF.prodCircuitTemplate.replace(".v", "_base.v")) , 'w') as f:
        f.write(productCircuit_base)
    with open("{}/{}".format(outFolder, CONF.prodCircuitTemplate.replace(".v", "_inductive.v")) , 'w') as f:
        f.write(productCircuit_inductive)



def createModule(outFolder, module, obsDict, inputsDict, suffix):
    inputVars = set()
    outputVars = set()

    for obsId in obsDict.keys():
        for obs in obsDict[obsId]:

            for v in collectVars(obs.get("expr")):
                if v in inputsDict.keys():
                    varWidth = int(inputsDict[v]["width"])
                    if varWidth == 1:
                        inputVars.add(v)
                    else:
                        inputVars.add("[{}:0] {}".format(varWidth-1, v))
                else:
                    print(f"Variable {v} not in dictionary of auxiliary variables")
                    exit(1)

            var = obs.get("var")
            if obs.get("width") == 1:
                outputVars.add(var)
            else:
                outputVars.add("[{}:0] {}".format(obs.get("width")-1, var))

    moduleSrc = "module {} ".format("{}_{}".format(module, suffix))
    moduleSrc += "( "
    moduleSrc += ' , '.join(["input {}".format(var) for var in inputVars] + ["output {}".format(var) for var in outputVars])
    moduleSrc += " );\n"
    for obsId in obsDict.keys():
        for obs in obsDict[obsId]:
            moduleSrc += "\tassign {} = {} ;\n".format(obs.get("var"), obs.get("expr"))
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
def inlineObservations(yosys_cmd_manager: YosysCommandManager, outFolder, metavars, auxvars, observations, module, prefix):
    ### 1. Get meta-variables for indexes
    idx_dict = initMetaVars(metavars)
    ### 2. Get auxiliary variable dictionary
    auxVars_dict = initAuxVars(auxvars, idx_dict)
    ### 3. Build observation dictionary and update auxVars dictionary
    obs_dict, auxVars_dict = initObservations(observations, auxVars_dict, idx_dict, prefix)
    if len(obs_dict) > 0:
        ### 4. Create observation module
        createModule(outFolder, module, obs_dict, auxVars_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, obs_dict, auxVars_dict, "{}".format(prefix))
    return obs_dict

@typechecked
def inlineStateVars(yosys_cmd_manager: YosysCommandManager, outFolder, metavars, auxvars, variables, module, prefix):
    ### 1. Get meta-variables for indexes
    idx_dict = initMetaVars(metavars)
    ### 2. Get auxiliary variable dictionary
    auxVars_dict = initAuxVars(auxvars, idx_dict)
    ### 3. Build observation dictionary and update auxVars dictionary
    vars_dict, auxVars_dict = initStateVars(variables, auxVars_dict, idx_dict, prefix)
    
    if len(vars_dict) > 0:
        ### 4. Create observation module 
        createModule(outFolder, module, vars_dict, auxVars_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, vars_dict, auxVars_dict, "{}".format(prefix))
    return vars_dict

@typechecked
def inlinePipelineInvs(yosys_cmd_manager: YosysCommandManager, outFolder, metavars, auxvars, invariants, module, prefix):
    ### 1. Get meta-variables for indexes
    idx_dict = initMetaVars(metavars)
    ### 2. Get auxiliary variable dictionary
    auxVars_dict = initAuxVars(auxvars, idx_dict)
    ### 3. Build observation dictionary and update auxVars dictionary
    invs_dict, auxVars_dict = initObservations(invariants, auxVars_dict, idx_dict, prefix)
    
    if len(invs_dict) > 0:
        ### 4. Create observation module 
        createModule(outFolder, module, invs_dict, auxVars_dict, "{}".format(prefix))
        ### 5. Link observation module, connect inputs, expose outputs
        yosys_cmd_manager.link_module(outFolder, module, invs_dict, auxVars_dict, "{}".format(prefix))
    return invs_dict


####
#### Main verification routine
####

def precomputing(srcObservations, trgObservations, stateInvariant, auxVars, metaVars, filtertype, usePredictor):
    state = CONF.state
    module = CONF.module
    outFolder = CONF.outFolder


    # construct yosys script
    yosys_cmd_manager = YosysCommandManager()

    log("START")

    time1 = datetime.now()

    ## 1. flatten source and target code
    log(f"Flattening {CONF.module}")
    yosys_cmd_manager.flatten_with_extra_steps(outFolder, CONF.module)
    time2 = datetime.now()
    logtimefile("\n\t\tTime for flatten the source code: "+ str((time2- time1).seconds))

    ## 2. inline target observations
    log("Inline target observations")
    trgObsVar = inlineObservations(yosys_cmd_manager, outFolder, metaVars, auxVars, trgObservations, module, "obs_trg")

    ## 3. inline source observations
    log("Inline src observations")
    srcObsVar = inlineObservations(yosys_cmd_manager, outFolder, metaVars, auxVars, srcObservations, module, "obs_src")

    ## 4. inline state variables
    log("Inline state variables")
    trgStateVars = inlineStateVars(yosys_cmd_manager, outFolder, metaVars, auxVars, state, module, "state_trg")

    ## 5. inline state invariants
    srcInvsVars = []
    if stateInvariant:
        log("Inline state invariants")
        srcInvsVars = inlinePipelineInvs(yosys_cmd_manager, outFolder, metaVars, auxVars, stateInvariant, module, "invariant_src")

    ## 6. Create product circuit
    log("Create product circuit")
    constructProductCircuit(outFolder, srcObsVar, trgObsVar, trgStateVars, srcInvsVars, CONF.clockInput, filtertype, usePredictor)
    run_process(["rm", "{}/{}".format(outFolder, CONF.prodCircuitTemplate)])
    run_process(["mv", "{}/prod_base.v".format(outFolder), "{}/prod_base.temp".format(outFolder)])
    run_process(["mv", "{}/prod_inductive.v".format(outFolder), "{}/prod_inductive.temp".format(outFolder)])
    time25 = datetime.now()
    logtimefile("\n\t\tTime for create observation circuits and prod circuit: "+ str((time25- time2).seconds))
    ## 7. Finalize
    log("Finalize target module changes")
    yosys_cmd_manager.finalize_module_changes(module, outFolder, "trg")
    time3 = datetime.now()
    logtimefile("\n\t\tTime for inline observations: "+ str((time3- time25).seconds))

    ## 8. verify contract satisfaction

    log(f"Generate the product circuit for base step")
    outFolder_base = outFolder + "/" + filtertype +"_base"
    run_process(["cp", "{}/prod_base.temp".format(outFolder), "{}/prod.v".format(outFolder)])
    run_process(["mkdir", "{}".format(outFolder_base)])
    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    yosys_cmd_manager = YosysCommandManager()
    yosys_cmd_manager.add_read_verilog_whole_folder(outFolder)
    yosys_cmd_manager.add_hierarchy_with_top(targetName)
    yosys_cmd_manager.add_proc_no_rom()
    yosys_cmd_manager.add_flattening()
    yosys_cmd_manager.add_opt()
    base_output_file_path = "{}/{}_renamed.temp".format(outFolder_base, targetName)
    yosys_cmd_manager.export_to_verilog(base_output_file_path)
    base_script_file_path = "{}/yosys-verification_base.script".format(outFolder)
    yosys_cmd_manager.run_from_script(base_script_file_path)
    run_process(["rm", "{}/prod.v".format(outFolder)])
            
    log(f"Generate the product circuit for inductive step")
    outFolder_inductive = outFolder + "/" + filtertype +"_inductive"
    run_process(["cp", "{}/prod_inductive.temp".format(outFolder), "{}/prod.v".format(outFolder)])
    run_process(["mkdir", "{}".format(outFolder_inductive)])
    targetName = CONF.prodCircuitTemplate.replace(".v", "")
    
    yosys_cmd_manager = YosysCommandManager()
    yosys_cmd_manager.add_read_verilog_whole_folder(outFolder)
    yosys_cmd_manager.add_hierarchy_with_top(targetName)
    yosys_cmd_manager.add_proc_no_rom()
    yosys_cmd_manager.add_flattening()
    yosys_cmd_manager.add_opt()
    inductive_output_file_path = "{}/{}_renamed.temp".format(outFolder_inductive, targetName)
    yosys_cmd_manager.export_to_verilog(inductive_output_file_path)
    inductive_script_file_path = "{}/yosys-verification_inductive.script".format(outFolder)
    yosys_cmd_manager.run_from_script(inductive_script_file_path)

    run_process(["rm", "{}/prod.v".format(outFolder)])
    time4 = datetime.now()
    logtimefile("\n\t\tTime for generating flattened product circuits: "+ str((time4- time3).seconds))

def verify(trgObservations, cstrtype, filtertype):
    print("PRADEDU VERIFICATION")
    outFolder = CONF.outFolder + "/" + filtertype + "_" + cstrtype

    # 1. replace the right trg_equiv in the prod.v
    run_process(["cp", "{}/prod.temp".format(outFolder), "{}/prod.v".format(outFolder)])
 
    trg_obs_dict, auxVars_dict = initObservations(trgObservations, {}, {}, "obs_trg")
 
    new_trg_equiv = ""
    if len(trg_obs_dict.keys()) > 0:
        new_trg_equiv += "\twire trg_equiv = {} ;\n".format( " && ".join( ["{}_trg".format(obsId) for obsId in trg_obs_dict.keys() ] ))
    # print(new_trg_equiv)

    prod = ""
    with open("{}/{}".format(outFolder,CONF.prodCircuitTemplate), "r") as f:
        lines = f.readlines()   
        for line in lines:
            if "wire trg_equiv" in line:
                prod += new_trg_equiv 
            else: 
                prod += line
    with open("{}/{}".format(outFolder,CONF.prodCircuitTemplate), "w+") as f:
        f.write(prod)   


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
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(outFolder, CONF.prodCircuitTemplate))
        yosys_cmd_manager.add_read_verilog_single_file("{}/{}".format(outFolder, CONF.moduleFile))
        yosys_cmd_manager.add_hierarchy_with_top(targetName)
        yosys_cmd_manager.add_proc_no_rom()
        yosys_cmd_manager.add_flattening()
        yosys_cmd_manager.add_opt()
        
        for yosys_pass in CONF.yosysSMTPreprocessing:
            yosys_cmd_manager.add_string_pass(yosys_pass)
        yosys_cmd_manager.export_to_smt2("{}/{}.smt".format(outFolder, targetName), with_wires=True)
        script_path = "{}/yosys-verification.script".format(outFolder)
        yosys_cmd_manager.run_from_script(script_path)

        run_process(["rm", "{}/prod.v".format(outFolder)])
 
        time4 = datetime.now()
        logtimefile("\n\t\tTime for generating prod.smt: "+ str((time4- time3).seconds))
        log("Bounded model checking")
        cmd = [CONF.yosysBMCPath, "-s", CONF.yosysBMCSolver]
        assert filtertype == "delayedcheck", "The only filtertype that is implemented"
        assert cstrtype == "base" or cstrtype == "inductive", "The only check that is implemented"
        if cstrtype == "base":
            cmd += ["-t", str(int(CONF.lookAhead)+1)]
        elif cstrtype == "inductive":
            cmd += ["-t", str(int(CONF.lookAhead)+2)]
        
        cmd +=["--dump-vlogtb" , "{}/{}_tb.v".format(outFolder, targetName)] 
        cmd += ["--dump-smtc", "{}/{}_smtc".format(outFolder, targetName)]
        cmd += ["--dump-vcd", "{}/{}_trace.vcd".format(outFolder, targetName)]
        cmd += ["--noincr"]
        cmd += ["{}/{}.smt".format(outFolder, targetName)]
        output = run_process(cmd, CONF.verbose_verification)
        time5 = datetime.now()
        logtimefile("\n\t\tTime for BMC: "+ str((time5- time4).seconds))

        if "Status: FAILED" in output:
            tb_file = "{}/{}_tb.v".format(outFolder, targetName)
            log("Verification FAILED")
            export_counter_example(tb_file)
            return "FAIL",tb_file, trg_obs_dict

        elif "Status: PASSED" in output:
            log("Verification PASSED")
            return "PASS", None, trg_obs_dict
        else:
            print("Unknown verification result")
            exit(1)
