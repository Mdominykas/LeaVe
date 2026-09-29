import os
from pathlib import Path

from typeguard import typechecked
from config import CONF
import re
from datetime import datetime 
from observations import PreparedObservationList
from util import *
from verification_environment import VerificationEnvironment


## Variables (TODO MG: Move to config)
ctr = 0

def log(msg):
    global ctr
    if CONF.verbose_preprocessing:
        print(f">>> Counterexample {ctr}) {msg}")
        ctr += 1

def compileWithIVerilog(file,outFolder):
    cmd = [CONF.iverilogPath]
    cmd.append("-gno-assertions")
    cmd.append("-g2005-sv")
    cmd.append("-o{}/{}".format(outFolder, CONF.prodCircuitTemplate.replace(".v","")))
    cmd.append(f"-I{outFolder}")
    cmd.append(f"-y{outFolder}")
    cmd.append(file)
    output = run_process(cmd, CONF.verbose_counterexample_checking)
    if "error" in output:
        print("Errors during counterexample compilation!")
        exit(1)
    return "{}/{}".format(outFolder, CONF.prodCircuitTemplate.replace(".v",""))

@typechecked
def runTestbed(testbed) -> list[str]:
    cmd = [CONF.vvpPath, testbed]
    ctx = run_process(cmd, CONF.verbose_counterexample_checking)
    cycles = ctx.split(">>>>>")
        
    
    diffcycle = False
    for cycle in cycles:
        if diffcycle:
            break
        else:
            diffInvList = []
            invs = cycle.split("\n")
            for inv in invs:
                tbname = inv.split(" ")
                if (tbname[-1] == "0" or tbname[-1] == "x") and len(tbname) == 2:
                    name = tbname[0].split("_trg")[0].split(".")[-1]
                    if name == " ":
                        logtimefile("Failed to prove " + name)
                        logtimefile("\nVerification failed!!!\n ")
                        logfile("\nVerification failed!!!\n ")
                        exit(1)
                    diffInvList.append(name)
            if len(diffInvList) < 2:
                diffcycle = False
            else:
                diffcycle = True

    print("diffInvList: ",diffInvList[0:-1])
    return diffInvList[0:-1]

                    


@typechecked
def displayObservations(counterexample: str, obs_list: PreparedObservationList, prodType: str, keyword: str):
    debug = True
    if len(obs_list.observations) > 0:
        code = ""
        with open(counterexample, "r") as f:
            code = f.read()

        if CONF.yosysCtxDisplayAtEdge:
            displayObs = f"\talways @(posedge {CONF.yosysCtxClock}) begin\n"
        else:
            displayObs = f"\talways @* begin\n"
        displayObs += f"\t\t$display(\">>>>> CYCLE %0d -- {keyword}\", {CONF.yosysCtxCycle});\n"
        for id in obs_list.observation_ids.keys():
            displayObs += f"\t\t $display(\"{CONF.yosysCtxUUT}.{id}_{prodType} %b\", {CONF.yosysCtxUUT}.{id}_{prodType});\n"
        displayObs += f"\t\t$display(\"{CONF.yosysCtxUUT}.{prodType}_equiv %b\", {CONF.yosysCtxUUT}.{prodType}_equiv);\n"
        if debug:
            for obs in obs_list.observations:
                displayObs += f"\t\t$display(\">>> {obs.id}\");\n"
                for atom in obs.attrs:
                    displayObs += f"\t\t$display(\"{atom.var} %b =?= %b\", {CONF.yosysCtxUUT}.{atom.var}_{prodType}_left,  {CONF.yosysCtxUUT}.{atom.var}_{prodType}_right);\n"
        displayObs += "\tend\n"
        displayObs += "endmodule\n"

        code = code.replace("endmodule", displayObs)
        with open(counterexample, "w") as f:
            f.write(code)


def rename(id_):
    renamed = "renamed_"+id_.replace(".","__").replace("[","___").replace("]","").replace("\\","").replace(" ","")
    return renamed

def renameDotNotation(file, testbed: bool):
    print("file yra:", file)
    code = ""
    with open(file, "r") as f:
        code = f.read()
    timein1 = datetime.now()
    #1) find all occurrences of . notation
    if testbed:
        #ids = re.findall('UUT\.([A-Za-z0-9_\.\\]*)(\[[A-Za-z0-9\']*\])?[A-Za-z0-9_\.\\\\]*', code)
        ids = re.findall('UUT\.(left\.[A-Za-z0-9_\.\\\\$/;]*)(?:\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)? =', code)  
        ids += re.findall('UUT\.(right\.[A-Za-z0-9_\.\\\\$/;]*)(?:\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)? =', code)

        ids_auto = re.findall('UUT\.(left\.[A-Za-z0-9_\.$/;]*)(\\\\[A-Za-z_\.]*\[[A-Za-z0-9\']*\] )([A-Za-z0-9_\.\\\\]*)? =', code)
        ids_auto += re.findall('UUT\.(right\.[A-Za-z0-9_\.$/;]*)(\\\\[A-Za-z_\.]*\[[A-Za-z0-9\']*\] )([A-Za-z0-9_\.\\\\]*)? =', code)

        # rename the variables defined in the prod.v start with "\\"
        namedArrays = re.findall('UUT\.(\\\\[A-Za-z0-9_\.\\\\$/;]*)(\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)?', code)
        # currently yosys puts two spaces before the assignment whenever the [..] is used as part of an identifier :-\
        namedArrays += re.findall('UUT\.(left\.\\\\[A-Za-z0-9_\.\\\\$/;]*)(\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)?  =', code)  # UUT.left.\IACK_reg[7]  =
        namedArrays += re.findall('UUT\.(right\.\\\\[A-Za-z0-9_\.\\\\$/;]*)(\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)?  =', code)
        
        namedArrays += re.findall('UUT\.(left\.[A-Za-z0-9_\.\\\\$/;]*)(\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)?  =', code)  # UUT.left.\IACK_reg[7]  =
        namedArrays += re.findall('UUT\.(right\.[A-Za-z0-9_\.\\\\$/;]*)(\[[A-Za-z0-9\']*\])?([A-Za-z0-9_\.\\\\]*)?  =', code)

        ids+=ids_auto
        ids+=namedArrays
    else:
        # We are renaming prod.v
        # yosys syntax for dot notation is "\xx.yy.zz"
        # These should be all definitions of registers and wires using DOT notation 
        ids =  re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\([A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)? (?:;| =)', code)  #  wire [31:0] \IOMUX[0]_obs_trg_arg0_trg_left ;
        ids += re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\(left\.[A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)? (?:;| =)', code)
        ids += re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\(right\.[A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)? (?:;| =)', code)

        # These should be all definitions of vector registers using DOT notation 
        ids += re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\([A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)?  \[[0-9]*:[0-9]*\]', code)
        ids += re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\(left\.[A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)?  \[[0-9]*:[0-9]*\]', code)
        ids += re.findall('(?:wire|reg) (?:\[[0-9]*:[0-9]*\] )?\\\\(right\.[A-Za-z0-9_\.\\\\$/;]*)(\[[0-9]*\])?([A-Za-z0-9_\.\\\\]*)?  \[[0-9]*:[0-9]*\]', code)
    # logtimefile("\n\t\t\tTime for finding illegal strings: "+ str((timein2- timein1).seconds))
    ids.sort(reverse=True,key=lambda id_: len(id_[0]+id_[1]) )
    list(set(ids))
    # logtimefile("\n\t\t\tTime for processing list: "+ str((timein3- timein2).seconds))
    print(f"Renamed {len(ids)} identifiers in {file}")
    for id_ in ids:
        if testbed:
            if id_ in namedArrays:
                id_ = id_[0] + id_[1] +id_[2]
                code = code.replace("UUT."+id_, "UUT."+rename(id_))
            elif id_ in ids_auto:
                id_ = id_[0] + id_[1] +id_[2]
                code = code.replace("UUT."+id_, "UUT."+rename(id_))
            else:
                id_ = id_[0] + id_[1]
                code = code.replace("UUT."+id_, "UUT."+rename(id_))

        else:
            id_ = id_[0]+id_[1]+id_[2]
            code = code.replace("\\"+id_+" ", rename(id_)+" ")

    with open(file, "w") as f:
        f.write(code)
    timein4 = datetime.now()
    # logtimefile("\n\t\t\tTime for replacing illegal strings: "+ str((timein4- timein3).seconds))
def fixClock(file):
    code = ""
    with open(file, "r") as f:
        code = f.read()

    testbed_clock = "PI_"+CONF.clockInput

    if f"wire [0:0] {testbed_clock} = clock;" not in code:
        ## yosys-smtbmc messed up, we need to fix it :-|
        code = code.replace(f".{CONF.clockInput}({testbed_clock})", f".{CONF.clockInput}(clock)")
        with open(file, "w") as f:
            f.write(code)
        print("Fixed clock signal")
    else:
        print("Yosys-smtbmc correctly assigned the clock signal")
        

@typechecked
def runCounterexample(common_env: VerificationEnvironment, specific_env: VerificationEnvironment, counterexample: str, trg_observations: PreparedObservationList) -> list[str]:
    log("START - RUN CTX")
    time1 = datetime.now()

    specific_env.add_prod_template(specific_env.target_path() / "prod_renamed.temp")

    # 1nd hack:
    # yosys-smtbmc sometimes uses the wrong clock signal for the generated testbed
    # we're fixing this manually
    log(f"Check if clock signal need to be fixed in {counterexample}")
    fixClock(counterexample)

    # 2st append display statements to the counterexample
    log(f"Append display statements")
    displayObservations(counterexample, trg_observations, "trg", "ASSERT")

    # 3st hack:
    # iverilog seems to have trouble with using dot notation, which is used by yosys
    # we therefore need to rename stuff in prod.v :-|
    log(f"Rename dot notation in {counterexample}")
    renameDotNotation(counterexample, testbed=True)
    
    # compile and run counterexample
    log(f"Compile counterexample testbed")
    tb = compileWithIVerilog(counterexample, specific_env.target_str())
    log(f"Run counterexample testbed")
    diffInvList = runTestbed(tb)

    time2 = datetime.now()
    logtimefile("\n\t\tTime for analyzing counterexample: "+ str((time2 - time1).seconds))
    log("END - RUN CTX")
    # exit(1)
    return diffInvList


