from __future__ import absolute_import
from __future__ import print_function
from pathlib import Path
import sys
import os
from typeguard import typechecked
import yaml
from optparse import OptionParser
from observations import Observation, ObservationList
from util import *
from datetime import datetime 


from config import CONF
from preprocessing import preprocessing
from verification import verify
from counterexample_checking import runCounterexample
from invariant import doesContainAllObservations, initInvariant
from invariant import refineInvariant
from verification_environment import VerificationEnvironment


@typechecked
def microEquivCheck(common_env: VerificationEnvironment, base_ver_env: VerificationEnvironment, ind_ver_env: VerificationEnvironment, invariant: ObservationList, target_observations: ObservationList, delayed_check_str: str):
    counter = 1
    basepass = False
    starttime = datetime.now()
    # TODO: this can be done with one loop. I think I should make some environment (base/inductive) and then simplify everything by a lot
    while not invariant.is_empty():
        logfile("\nBegin the {}th loop...\n".format(counter))
        logtimefile("\n\n\tTime for the {}th loop...".format(counter))
        counter+=1
        # TODO: I would like to have this in log, but I don't want to edit it now
        # logfile("\tThe invariant for verification is:\n" + "".join(inv2str(invariant)))
        if not basepass: 
            # 1.1 verification_base
            print("Checking the base case")
            logfile("\n3.1. Checking the micro-equivalence relation...\n")
            logfile("\n3.1.1. Checking the base case...\n")
            verifStatus, cex, inv = verify(common_env, base_ver_env, invariant, "base", delayed_check_str)
            print(verifStatus)

            if verifStatus == "FAIL":
                diffInvList = runCounterexample(common_env, base_ver_env, cex, inv)
                logfile("  The base step is not satisfied!\n" + "\tthe difference set of invariant is:\n------\n"+ "\n".join(diffInvList)+"\n------\n")
                print("The base case is not satisfied!")
                if diffInvList == []:
                    logfile("  Nothing learned from counterexample! The result is UNKNOWN!")
                    print("Nothing learned from counterexample!")
                    return False, None
                invariant = refineInvariant(invariant, diffInvList)
                continue
            else:
                basepass = True
                logfile("  The base case is satisfied!\n")
                basetime = datetime.now()
                continue
        else:
            # 1.2 verification_inductive
            print("  Checking the inductive step")
            logfile("\n\t Checking the inductive step...\n")
            verifStatus, cex, inv = verify(common_env, ind_ver_env, invariant, "inductive", delayed_check_str)
            if verifStatus == "FAIL":
                print("The inductive step is not satisfied!")
                diffInvList = runCounterexample(common_env, ind_ver_env, cex, inv)
                logfile("\tThe inductive step is not satisfied!\n" + "\tthe difference set of invariant is:\n------\n"+ "\n".join(diffInvList)+"\n------\n")
                if diffInvList == []:
                    print("Nothing learned from counterexample!")
                    logfile("\tNothing learned from counterexample! The result is UNKNOWN!")
                    return False, None
                invariant = refineInvariant(invariant, diffInvList)
                if not doesContainAllObservations(invariant, target_observations):
                    logfile("Target observations are no longer part of invariant. Breaking early")
                    return False, []
                continue
            else:
                logfile("\tThe inductive step is satisfied!\n")
                invtime = datetime.now()
                # TODO: I would like to have this in log, but I don't want to edit it now
                # logfile("\tThe invariant learned is:\n" + "".join(inv2str(invariant)))
                # print("The invariant learned is: \n",invariant)
                
                logfile("\n\n\tTime for base step: "+ str((basetime- starttime).seconds))
                logfile("\n\tTime for inductive step: "+ str((invtime - basetime).seconds))
                logtimefile("\n\n\tTime for base step: "+ str((basetime- starttime).seconds))
                logtimefile("\n\tTime for inductive step: "+ str((invtime - basetime).seconds))
                return True, invariant
    logfile("  \n\t No invariant found!\n")
    return False, None


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

    common_env.copy_actual_code()
    common_env.add_prod_template()

    delayed_check_str = "delayedcheck"
    # large-bound-check
    auxVars, to_expand, invariant = initInvariant(common_env, delayed_check_str)
    # generating toexpandArray
    toexpandArray = to_expand + CONF.expandArrays
    # normal pipeline invariant
    stateInvariant = ObservationList()
    stateInvariant.extend_with_observation([Observation.from_dict(d) for d in CONF.stateInvariant])
    # observations

    src_observations = ObservationList()
    src_observations.extend_with_observation([Observation.from_dict(d) for d in CONF.srcObservations])
    trg_observations = ObservationList()
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


    preprocessing(common_env, base_ver_env, ind_ver_env, toexpandArray, src_observations, invariant, stateInvariant, auxVars, delayed_check_str, usePredictor)
    time2 = datetime.now() 
    logtimefile("\n\n2. Start the verification...")
    State, invariant = microEquivCheck(common_env, base_ver_env, ind_ver_env, invariant, trg_observations, delayed_check_str)
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
