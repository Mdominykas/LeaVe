import os
from pathlib import Path
from typing import List
from vcdvcd import VCDVCD

from typeguard import typechecked
from config import CONF
import re
from datetime import datetime 
from observations import PreparedObservationList
from util import *
from verification_environment import VerificationEnvironment

class VCDAnalyzer:
    @typechecked
    def __init__(self, folder_path: Path):
        self.folder_path = folder_path
        folder_path.mkdir(parents=True, exist_ok=True)

        self.trace_number = 0

    @typechecked
    def last_file_name(self) -> Path:
        return self.folder_path / "trace_{}.vcd".format(self.trace_number)

    @typechecked
    def give_file_name(self) -> Path:
        self.trace_number += 1
        return self.last_file_name()
    
    @typechecked
    def vcd_name(self, wire: str) -> str:
        # yosys-smtbmc drops the leading backslash and writes [7] as <7>,
        # e.g. \core.reg_trg -> prod.core.reg_trg, \IACK_reg[7]_trg -> prod.IACK_reg<7>_trg
        top = CONF.prodCircuitTemplate.replace(".v", "")
        return top + "." + wire.lstrip("\\").replace("[", "<").replace("]", ">")

    
    @typechecked
    def analyze_last_file(self, trg_observations: PreparedObservationList) -> List[str]:
        ids = list(trg_observations.observation_ids)
        obs_wires = {id_: self.vcd_name(id_ + "_trg") for id_ in ids}
        equiv = self.vcd_name("trg_equiv")

        vcd = VCDVCD(str(self.last_file_name()), signals=[equiv, *obs_wires.values()])
        missing = [w for w in [equiv, *obs_wires.values()] if w not in vcd.signals]
        assert not missing, f"Not found in {self.last_file_name()}: {missing}"

        fail_time = next((t for t, v in vcd[equiv].tv if v != "1"), None)
        if fail_time is None:
            return []

        diff = [id_ for id_ in ids if vcd[obs_wires[id_]][fail_time] != "1"]
        print(f"trg_equiv fails at step {fail_time // 10}, differing: {diff}")
        return diff




## Variables (TODO MG: Move to config)
ctr = 0

def log(msg):
    global ctr
    if CONF.verbose_preprocessing:
        print(f">>> Counterexample {ctr}) {msg}")
        ctr += 1


@typechecked
def get_diff_inv_list(vcd_analyzer: VCDAnalyzer, trg_observations: PreparedObservationList) -> list[str]:
    vcd_diff_list = vcd_analyzer.analyze_last_file(trg_observations)

    return vcd_diff_list




def rename(id_):
    renamed = "renamed_"+id_.replace(".","__").replace("[","___").replace("]","").replace("\\","").replace(" ","")
    return renamed

        

@typechecked
def run_counterexample(vcd_analyzer: VCDAnalyzer, trg_observations: PreparedObservationList) -> list[str]:
    time1 = datetime.now()

    log(f"Get invariant difference list from vcd")
    diffInvList = get_diff_inv_list(vcd_analyzer, trg_observations)

    time2 = datetime.now()
    logtimefile("\n\t\tTime for analyzing counterexample: "+ str((time2 - time1).seconds))
    log("END - RUN CTX")
    # exit(1)
    return diffInvList


