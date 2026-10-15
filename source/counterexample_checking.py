import os
import sys
from pathlib import Path
from typing import List
from vcd import VCDWriter
from vcdvcd import VCDVCD

from typeguard import typechecked
from config import CONF
import re
from datetime import datetime 
from observations import PreparedObservationList
from util import *
from verification_environment import VerificationEnvironment

import vcd.writer
# Note, here I am modifying a private function, so this can break at pretty much any time
vcd.writer._encode_identifier = lambda i: f"n{i}"

class VCDAnalyzer:
    @typechecked
    def __init__(self, folder_path: Path):
        self.folder_path = folder_path
        folder_path.mkdir(parents=True, exist_ok=True)

        self.trace_number = 0

    @typechecked
    def last_file_name(self, suffix: str = "") -> Path:
        return self.folder_path / "trace_{}{}.vcd".format(self.trace_number, suffix)

    @typechecked
    def give_file_name(self) -> Path:
        self.trace_number += 1
        return self.last_file_name()

    def split_left_right(self):
        src = VCDVCD(self.last_file_name())
    
        for module in ["left", "right"]:
            prefix = "prod." + module + "."
            names = [n for n in src.signals if n.startswith(prefix)]
            if not names:
                sys.exit(f"No signals found for module '{module}'")
        
            ts = src.timescale
            with open(str(self.last_file_name("_" + module)), "w") as f, VCDWriter(f, timescale=f"{ts['magnitude']} {ts['unit']}") as out:
                vars = {}
                for n in names:
                    scope, _, ref = n[len(prefix):].rpartition(".")
                    sig = src[n]
                    # Signals directly in <module> keep it as scope (VCD needs a scope)
                    vars[n] = out.register_var(scope or module, ref, sig.var_type, size=int(sig.size))
        
                # Write all value changes in time order
                changes = sorted((t, n, v) for n in names for t, v in src[n].tv)
                for t, n, v in changes:
                    out.change(vars[n], t, v)
    
    @typechecked
    def vcd_name(self, wire: str) -> str:
        # yosys-smtbmc drops the leading backslash and writes [7] as <7>,
        # e.g. \core.reg_trg -> prod.core.reg_trg, \IACK_reg[7]_trg -> prod.IACK_reg<7>_trg
        top = CONF.prodCircuitTemplate.replace(".v", "")
        return top + "." + wire.lstrip("\\").replace("[", "<").replace("]", ">")

    
    @typechecked
    def analyze_last_file(self, trg_observations: PreparedObservationList) -> List[str]:
        suffix = "_trg" if not CONF.do_inductive_invariant_verification else "_provable_inv"
        ids = list(trg_observations.observation_ids)
        obs_wires = {id_: self.vcd_name(id_ + suffix) for id_ in ids}
        
        wire_name = "trg_equiv" if not CONF.do_inductive_invariant_verification else "inductive_state_invariant"
        equiv = self.vcd_name(wire_name)

        vcd = VCDVCD(str(self.last_file_name()), signals=[equiv, *obs_wires.values()])
        missing = [w for w in [equiv, *obs_wires.values()] if w not in vcd.signals]
        assert not missing, f"Not found in {self.last_file_name()}: {missing}"

        fail_time = next((t for t, v in vcd[equiv].tv if v != "1"), None)
        if fail_time is None:
            return []

        diff = [id_ for id_ in ids if vcd[obs_wires[id_]][fail_time] != "1"]
        print(f"{wire_name} fails at step {fail_time // 10}, differing: {diff}")
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


