from __future__ import absolute_import
from __future__ import print_function
from pathlib import Path
import time
from typing import List

from typeguard import typechecked
from auxilary_variables import AuxVarDict, get_aux_vars_from_config
from config import CONF
from observations import Observation, ObservationList, PreparedObservationList
from rtl_parts import RTLMemory
from util import *
from counterexample_checking import rename

from config import CONF
from verification_environment import VerificationEnvironment
from yosys_cmd_manager import YosysCommandManager

def escape_id(id):
    if (id.count("[")) and (id.count(".") == 0):
        return "\\" + id
    else:
        return id

def id2val(id):
    if id.count(".") == 0:
        return id
    else:
        return "\\" + id


@typechecked
def initInvariant(common_env: VerificationEnvironment, filtertype) -> tuple[AuxVarDict, List[dict], ObservationList]:
    
    yosys_cmd_manager = YosysCommandManager()
    memories, variables = yosys_cmd_manager.show_regs_mems_workflow(common_env.target_str(), CONF.module)

    invariant: ObservationList = ObservationList()
    to_expand = []

    aux_var_dict: AuxVarDict = get_aux_vars_from_config(CONF)

    for mem in memories:
        to_expand.append(mem.to_to_expand())
        for i in range(mem.size):
            aux_var_dict.add_aux_var(mem.to_aux_var(i))
            invariant.add_observation(mem.to_invariant(i))
       
    for var in variables:
        aux_var_dict.add_aux_var(var.to_aux_var())
        invariant.add_observation(var.to_invariant())

    new_obs = [Observation.from_dict(d) for d in CONF.predicateRetire + CONF.trgObservations + CONF.invariant]
    invariant.extend_with_observation(new_obs)
    return aux_var_dict, to_expand, invariant


@typechecked
def refineInvariant(invariant: ObservationList, diffInvList: list[str]) -> ObservationList:
    ans = ObservationList()
    for obs in invariant.observations:
        if (obs.id not in diffInvList) and (rename(obs.id) not in diffInvList):
            ans.add_observation(obs)
    return ans

@typechecked
def doesContainAllObservations(source: ObservationList, target: ObservationList):
    for obs in target.get_observation_list():
        if not obs in source.get_observation_list():
            return False
    return True