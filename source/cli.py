from __future__ import absolute_import
from __future__ import print_function
from pathlib import Path
import sys
import os
from typing import List
from typeguard import typechecked
import yaml
from optparse import OptionParser
from observations import Observation, ObservationList
from util import *
from datetime import datetime 


from config import CONF
from preprocessing import preprocessing
from verification import verify, verify_invariants
from counterexample_checking import VCDAnalyzer, run_counterexample
from invariant import doesContainAllObservations, initInvariant
from invariant import refineInvariant
from verification_environment import VerificationEnvironment


@typechecked
def microEquivCheck(base_ver_env: VerificationEnvironment, ind_ver_env: VerificationEnvironment, invariant: ObservationList, target_observations: ObservationList, delayed_check_str: str, vcd_analyzer: VCDAnalyzer):
    counter = 1
    timers = [datetime.now()]
    for (case_name, specific_env) in [("base", base_ver_env), ("inductive", ind_ver_env)]:
        while not invariant.is_empty():
            logfile("\nBegin the {}th loop...\n".format(counter))
            logtimefile("\n\n\tTime for the {}th loop...".format(counter))
            counter += 1
            print(f"Checking the {case_name} case")
            logfile("\nChecking the micro-equivalence relation...\n")
            logfile(f"\nChecking the {case_name} case...\n")
            verifStatus, cex, inv = verify(specific_env, invariant, case_name, delayed_check_str, vcd_analyzer)
            print(verifStatus)

            if verifStatus == "FAIL":
                diffInvList = run_counterexample(vcd_analyzer, inv)
                logfile(f"  The {case_name} step is not satisfied!\n" + "\tthe difference set of invariant is:\n------\n"+ "\n".join(diffInvList)+"\n------\n")
                print(f"The {case_name} case is not satisfied!")
                if diffInvList == []:
                    logfile("  Nothing learned from counterexample! The result is UNKNOWN!")
                    print("Nothing learned from counterexample!")
                    return False, None
                invariant = refineInvariant(invariant, diffInvList)
                if not doesContainAllObservations(invariant, target_observations):
                    logfile("Target observations are no longer part of invariant. Breaking early")
                    return False, []
            else:
                logfile(f"  The {case_name} case is satisfied!\n")
                break
        timers.append(datetime.now())
    start_time = timers[0]
    base_time = timers[1]
    inv_time = timers[2]
    logfile("\n\n\tTime for base step: "+ str((base_time- start_time).seconds))
    logfile("\n\tTime for inductive step: "+ str((inv_time - base_time).seconds))
    logtimefile("\n\n\tTime for base step: "+ str((base_time- start_time).seconds))
    logtimefile("\n\tTime for inductive step: "+ str((inv_time - base_time).seconds))
    return not invariant.is_empty(), invariant

@typechecked
def check_inductive_invariants(base_ver_env: VerificationEnvironment, ind_ver_env: VerificationEnvironment, inductive_state_invariant: ObservationList, delayed_check_str: str, vcd_analyzer: VCDAnalyzer) -> List[str]:
    suffix = "provable_inv"
    dropped_invariants = []
    counter = 1
    timers = [datetime.now()]
    for (case_name, specific_env) in [("base", base_ver_env), ("inductive", ind_ver_env)]:
        print(f"starting {case_name} case")
        while not inductive_state_invariant.is_empty():
            counter += 1
            verifStatus, cex, inv = verify_invariants(specific_env, inductive_state_invariant, case_name, delayed_check_str, suffix, vcd_analyzer)
            if verifStatus == "FAIL":
                diffInvList = run_counterexample(vcd_analyzer, inv)
                logfile(f"  The {case_name} step is not satisfied!\n" + "\tthe difference set of invariant is:\n------\n"+ "\n".join(diffInvList)+"\n------\n")
                dropped_invariants += diffInvList
                if diffInvList == []:
                    assert False, "I don't think this should happen"
                inductive_state_invariant = refineInvariant(inductive_state_invariant, diffInvList)
            else:
                break
    return dropped_invariants

def main():
    INFO = "Verification of contract satisfaction"
    VERSION = "0.0 :-|"
    USAGE = "Usage: python cli.py configFile"

    def showVersion():
        print(INFO)
        print(VERSION)
        print(USAGE)
        sys.exit()

    optparser = OptionParser()
    optparser.add_option("-v", "--version", action="store_true", dest="showversion",
                         default=False, help="Show the version")
    optparser.add_option("-D", dest="define", action="append",
                         default=[], help="Macro Definition")
    optparser.add_option("-c", dest="clk", action="append",
                         default='clk', help="Clock Signal Name")
    optparser.add_option("--usePredictor", action="store_true", dest="usePredictor", default=False, help="Enable the predictor")
    optparser.add_option("--validateInductiveStateInvariants", action="store_true", dest="validateInductiveStateInvariants", default=False, help="Check only i")

    (options, args) = optparser.parse_args()

    if options.usePredictor:
        (options, args) = optparser.parse_args()

    filelist = args
    if options.showversion: # or options.showhelp:
        showVersion()

    for f in filelist:
        if not os.path.exists(f):
            raise IOError("file not found: " + f)

    if len(filelist) == 0:
        showVersion()

    ## Init configuration
    configFile = filelist[0]
    
    if getattr(args, 'verbose', 0):
        CONF.set('verbose', 1)
    with open(configFile, "r") as f:
        config_update: Dict = yaml.safe_load(f)
    for var, value in config_update.items():
        CONF.set(var, value)

    if CONF.selfCompositionEquality == "==":
        CONF.selfCompositionInequality = "!="
    if CONF.selfCompositionEquality == "===":
        CONF.selfCompositionInequality = "!=="

    run_process(["mkdir", CONF.outFolder], CONF.verbose_preprocessing)
    logfile("1. Preparing the environment for verification....\n")

    common_env_folder = Path(CONF.outFolder + "/" + "common_env").resolve()
    print("common_env_folder:", common_env_folder)
    common_env = VerificationEnvironment(common_env_folder, source=Path(CONF.codeFolder))

    config_storage_folder = Path(CONF.outFolder + "/" + "config_storage").resolve()
    config_storage = VerificationEnvironment(config_storage_folder, source=Path(CONF.codeFolder))
    config_storage.copy_file(Path(configFile), "leave_config.yaml")
    config_storage.copy_file(Path(CONF.wireLiftingPath), "final_wire_lifting.json")

    common_env.copy_actual_code()
    common_env.add_prod_template()

    delayed_check_str = "delayedcheck"
    # large-bound-check
    auxVars, to_expand, invariant = initInvariant(common_env, delayed_check_str)
    # generating toexpandArray
    toexpandArray = to_expand + CONF.expandArrays
    # normal pipeline invariant
    state_assumptions = ObservationList(combined_name="state_assumptions")
    state_assumptions.extend_with_observation([Observation.from_dict(d) for d in CONF.stateInvariant])
    
    # provable state invariants
    inductive_state_invariants = ObservationList(combined_name="inductive_state_invariant")
    if options.validateInductiveStateInvariants:
        CONF.do_inductive_invariant_verification = True
        inductive_state_invariants.extend_with_observation([Observation.from_dict(d) for d in CONF.inductiveStateInvariant])
    else:
        state_assumptions.extend_with_observation([Observation.from_dict(d) for d in CONF.inductiveStateInvariant])
    # observations

    src_observations = ObservationList(combined_name="src_equiv")
    src_observations.extend_with_observation([Observation.from_dict(d) for d in CONF.srcObservations])
    trg_observations = ObservationList(combined_name="trg_equiv")
    trg_observations.extend_with_observation([Observation.from_dict(d) for d in CONF.trgObservations])
    
    assert options.usePredictor == CONF.usePredictor, "Both options for predictors are different. There is an error in one of the options"

    usePredictor = CONF.usePredictor
    if usePredictor:
        assert CONF.wireLiftingPath != ""


    time1 = datetime.now() 
    logfile("\n2. Start the delayed leakage ordering check...\n")
    logfile("\n\t2.1 Start the preprocessing...\n")
    logtimefile("1. Start the preprocessing...\n")   
    

    base_name = "{}_base".format(delayed_check_str)
    base_folder = Path(CONF.outFolder + "/" + base_name).resolve()
    base_ver_env = VerificationEnvironment(base_folder, source=common_env.target_path())

    ind_name = "{}_inductive".format(delayed_check_str)
    ind_folder = Path(CONF.outFolder + "/" + ind_name).resolve()
    ind_ver_env = VerificationEnvironment(ind_folder, source=common_env.target_path())

    vcd_analyzer = VCDAnalyzer(Path(CONF.outFolder) / "vcd")


    preprocessing(common_env, base_ver_env, ind_ver_env, toexpandArray, src_observations, invariant, state_assumptions, inductive_state_invariants, auxVars, delayed_check_str, usePredictor)
    time2 = datetime.now() 

    if options.validateInductiveStateInvariants:
        dropped_invariants = check_inductive_invariants(base_ver_env, ind_ver_env, inductive_state_invariants, delayed_check_str, vcd_analyzer)
        if dropped_invariants:
            print("Verification dropped these invariants: ", dropped_invariants)
            # TODO: change this somehow
            logfile("\n\tThe CPU is VULNERABLE under the attack w.r.t the contract!!")
        else:
            logfile("\n\tThe CPU is SECURE under the attack w.r.t the contract!!")
    else:
        logtimefile("\n\n2. Start the verification...")
        State, invariant = microEquivCheck(base_ver_env, ind_ver_env, invariant, trg_observations, delayed_check_str, vcd_analyzer)
        if State:    
            logfile("\n\n3. Check the satisfaction based on learned strongest attacker.\n")
            if doesContainAllObservations(invariant, trg_observations):
                logfile("\n\n\tVerification passed!!\n\n")
                logtimefile("\n\n\tVerification passed!!\n\n")
                logfile("\n\tThe CPU is SECURE under the attack w.r.t the contract!!")
            else:
                logfile("\n\tThe CPU is VULNERABLE under the attack w.r.t the contract!!")
        else:
            if invariant is not None:
                logfile("\n\tThe CPU is VULNERABLE under the attack w.r.t the contract!!")
        time3 = datetime.now()  
        logtimefile("\n\n\tTime for preprocessing: "+ str((time2- time1).seconds))
        logtimefile("\n\tTime for learning the strongest attacker: "+ str((time3- time2).seconds))






if __name__ == '__main__':
    main()
