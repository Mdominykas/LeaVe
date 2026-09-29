from __future__ import annotations
import re
from typing import List

from typeguard import typechecked

from auxilary_variables import AuxVar, AuxVarDict
from expr_parser import collectVars, parser

from copy import copy, deepcopy

Expr = str

class ObservationAtom:
    @typechecked
    def __init__(self, value: Expr, width: int, init: bool = False):
        self.value = value
        self.width = width
        # TODO: I think init is only needed for state assumptions. It might be good to refactor it later
        self.init = init

    def __copy__(self):
        return ObservationAtom(self.value, self.width, self.init)

    def __deepcopy__(self, memo):
        return ObservationAtom(
            deepcopy(self.value, memo),
            deepcopy(self.width, memo),
            deepcopy(self.init, memo),
        )

    @staticmethod
    @typechecked
    def from_dict(d: dict) -> ObservationAtom:
        return ObservationAtom(value=d["value"], width=d["width"], init=d.get("init", False) == "1")
    
    def __eq__(self, other):
        if not isinstance(other, ObservationAtom):
            return NotImplemented
        return self.value == other.value and self.width == other.width and self.init == other.init

    def __repr__(self):
        return f"ObservationAtom(value={self.value!r}, width={self.width}, init={self.init})"



class Observation:
    @typechecked
    def __init__(self, id: str, cond: Expr, attrs: List[ObservationAtom], init: bool = False):
        self.id = id
        self.cond = cond
        self.attrs = deepcopy(attrs)
        self.init = init

    @staticmethod
    @typechecked
    def from_dict(d: dict) -> Observation:
        attrs = [ObservationAtom.from_dict(at)for at in d["attrs"]]
        # It's a stupid thing to keep it consistent with legacy configurations
        init = d["init"] == "1" if "init" in d.keys() else False
        return Observation(id=d["id"], cond=d["cond"], attrs=attrs, init=init)
    
    def __eq__(self, other):
        if not isinstance(other, Observation):
            return NotImplemented
        return self.id == other.id and self.cond == other.cond and self.attrs == other.attrs and self.init == other.init

    def __repr__(self):
        return f"Observation(id={self.id!r}, cond={self.cond}, attrs={self.attrs!r}, init={self.init})"



# TODO: I think this can be done in a generic way
# arba galiu tiesiog laikyti lista ir uztiprinti invarianta
class ObservationList:
    observation_ids: dict[str, None]
    # TODO: I think this might be wrong...
    observations: list[PreparedObservation]

    def __init__(self):
        self.observation_ids = {}
        self.observations = []
    
    @typechecked
    def add_observation(self, observation: Observation, okay_if_identical_exists=True):
        already_there = False
        if not okay_if_identical_exists:
            assert observation.id not in self.observation_ids, "The aux_var id: \"{}\" is duplicated".format(observation.id)
        elif observation.id in self.observation_ids:
            for obs in self.observations:
                assert obs.id != observation.id or obs == observation, "We can only add an identical observation, they are: old={} and new={}".format(obs, observation)
                if obs.id == observation.id:
                    already_there = True
        if not already_there:
            self.observations.append(observation)
            self.observation_ids[observation.id] = True

    @typechecked
    def extend_with_observation(self, observations: List[Observation]):
        for obs in observations:
            self.add_observation(obs)

    @typechecked
    def get_observation_list(self) -> List[Observation]:
        return self.observations

    @typechecked
    def is_empty(self) -> bool:
        return len(self.observations) == 0



# TODO: use this class for the code that I write (after I used observation somewhere else)
class ObservationPrediction:
    @typechecked
    def __init__(self, id: str, avail: str, applicability: str, observation: PreparedObservationAtom):
        self.id = id
        self.avail = avail
        self.applicability = applicability
        self.observation = observation

def getIndexMetaVariables(expr:str):
    return set(re.findall('\$\$(.*?)\$\$', expr))

def replaceIndexMetaVariable(expr:str, metavar:str, value:str):
    return re.sub(f'\$\${metavar}\$\$', value, expr)


# TODO: I think I can skip whole previous step and just go directly here
class PreparedObservationAtom:
    @typechecked
    def __init__(self, var: str, expr: Expr, width: int, init: bool = False):
        self.var = var
        self.expr = expr
        self.width = width
        self.init = init
    
    def __copy__(self):
        return PreparedObservationAtom(self.var, self.expr, self.width, self.init)

    def __deepcopy__(self, memo):
        return PreparedObservationAtom(
            deepcopy(self.var, memo),
            deepcopy(self.expr, memo),
            deepcopy(self.width, memo),
            deepcopy(self.init, memo),
        )
    
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PreparedObservationAtom):
            return NotImplemented
        return (self.var, self.expr, self.width, self.init) == (
            other.var, other.expr, other.width, other.init
        )
    
    def __repr__(self):
        return f"PreparedObservationAtom(var={self.var!r}, expr={self.expr}, width={self.width!r}, init={self.init})"



class PreparedObservation:
    @typechecked
    def __init__(self, id: str, cond: PreparedObservationAtom, attrs: List[PreparedObservationAtom], init: bool = False):
        self.id = id
        self.cond = cond
        self.attrs = deepcopy(attrs)
        self.init = init

    def get_all_atoms(self) -> List[PreparedObservationAtom]:
        return [self.cond] + self.attrs

    @typechecked
    def collect_vars_from_expressions(self) -> set[str]:
        ans = set()
        for a in self.get_all_atoms():
            ans = ans.union(collectVars(a.expr))
        return ans
    
    def __eq__(self, other):
        if not isinstance(other, PreparedObservation):
            return NotImplemented
        return self.id == other.id and self.cond == other.cond and self.attrs == other.attrs and self.init == other.init

    def __repr__(self):
        return f"Observation(id={self.id!r}, cond={self.cond}, attrs={self.attrs!r}, init={self.init})"


class PreparedObservationList:
    observation_ids: dict[str, None]
    observations: list[PreparedObservation]
    
    def __init__(self):
        self.observation_ids = {}
        self.observations = []
    
    @typechecked
    def add_observation(self, observation: PreparedObservation, okay_if_identical_exists=True):
        already_there = False
        if not okay_if_identical_exists:
            assert observation.id not in self.observation_ids, "The aux_var id: \"{}\" is duplicated".format(observation.id)
        elif observation.id in self.observation_ids:
            for obs in self.observations:
                assert obs.id != observation.id or obs == observation, "We can only add an identical observation, they are: old={} and new={}".format(obs, observation)
                if obs.id == observation.id:
                    already_there = True
        
        if not already_there:
            self.observations.append(observation)
            self.observation_ids[observation.id] = True

    @typechecked
    def extend_with_observation(self, observations: List[PreparedObservation]):
        for obs in observations:
            self.add_observation(obs)

    @typechecked
    def get_observation_list(self) -> List[PreparedObservation]:
        return self.observations[:]

    @typechecked
    def is_empty(self) -> bool:
        return len(self.observations) == 0

    def get_all_blocks(self):
        ans = []
        for obs in self.observations:
            for at in obs.attrs:
                ans.append(at)
            ans.append(obs.cond)
        return ans
    
    @typechecked
    def collect_vars_from_expressions(self) -> set[str]:
        ans = set()
        for prep_obs in self.get_observation_list():
            for obs_atom in prep_obs.get_all_atoms():
                ans = ans.union(collectVars(obs_atom.expr))
        return ans
        
    # TODO: this should be done from configuration file, cause this is just a terrible workaround
    def parse_predictions(self) -> List[ObservationPrediction]:
        AVAIL_PREF = "avail_"

        # [id -> [obs, avail]]
        obs_pairs = {}
        for id in self.observation_ids.keys():
            if not id.startswith(AVAIL_PREF):
                obs_pairs[id] = [None, None]

        for obs in self.observations:
            if obs.id.startswith(AVAIL_PREF):
                true_id = obs.id[len(AVAIL_PREF):]
                obs_pairs[true_id] = [obs_pairs[true_id][0], obs]
            else:
                obs_pairs[obs.id] = [obs, obs_pairs[obs.id][1]]

        src_obs_predictions = []

        for id, (obs, avail) in obs_pairs.items():
            assert isinstance(obs, PreparedObservation)
            assert isinstance(avail, PreparedObservation)
            assert len(obs.attrs) == 1
            assert len(avail.attrs) == 1
            assert obs.attrs[0].expr == avail.attrs[0].expr and obs.attrs[0].width == avail.attrs[0].width, "Attributes were supposed to be equal, but they are: obs.attr={}, avail.attr={}".format(obs.attrs[0], avail.attrs[0])
            assert obs.cond.var.endswith("_obs_src_cond")
            assert avail.cond.var.endswith("_obs_src_cond")
            assert obs.attrs[0].var.endswith("_obs_src_arg0")

            src_obs_predictions.append(ObservationPrediction(id=id, applicability=obs.cond.var, avail=avail.cond.var, observation=obs.attrs[0]))
        
        return src_obs_predictions
        



@typechecked
def initObservations(observations: ObservationList, aux_var_dict: AuxVarDict, prefix: str) -> PreparedObservationList:
    prepared_observations = PreparedObservationList()
    for obs in observations.get_observation_list():
        cond_var = "{}_{}_cond".format(obs.id, prefix)
        cond = PreparedObservationAtom(cond_var, obs.cond, 1)
        attrs = []
        for (idx, attr) in enumerate(obs.attrs):
            # TODO: I asume that for observations and invariants init is always False
            arg_var = "{}_{}_arg{}".format(obs.id, prefix, idx)
            attrs.append(PreparedObservationAtom(arg_var, attr.value, attr.width, init=attr.init))
        prepared_observations.add_observation(PreparedObservation(obs.id, cond, attrs, init=obs.init))
        
    ##### 3. Update auxVars dictionary
    for obs in prepared_observations.get_observation_list():
        for obs_atom in [obs.cond] + obs.attrs:
            for var in collectVars(obs_atom.expr):
                # TODO: We will only add auxiliary variables with width 1. It seems like a bug, but I should fix that later
                if var not in aux_var_dict.ids:
                    aux_var_dict.add_aux_var_if_none(AuxVar(var, 1, var))

    return prepared_observations


class InitialStateConstraint:
    @typechecked
    def __init__(self, id: str, var: str, expr: Expr, width: int, val: int):
        self.id = id
        self.var = var
        self.expr = expr
        self.width = width
        self.val = val


class InitialStateConstraintList:
    @typechecked
    def __init__(self):
        self.ids = set()
        self.constraints = []
    
    def get_constraints(self) -> List[InitialStateConstraint]:
        return self.constraints[:]
    
    def get_all_blocks(self) -> List[InitialStateConstraint]:
        return self.constraints[:]

    @typechecked
    def add_constraint(self, constraint: InitialStateConstraint):
        assert constraint.id not in self.ids
        self.constraints.append(constraint)
        self.ids.add(constraint.id)

    @typechecked
    def collect_vars_from_expressions(self) -> set[str]:
        ans = set()
        for a in self.constraints:
            ans = ans.union(collectVars(a.expr))
        return ans


@typechecked
def init_initial_state_vars(variables: List[dict], aux_var_dict: AuxVarDict, prefix: str) -> InitialStateConstraintList:
    ##### 1. Parse state variables 
    constraints = InitialStateConstraintList()
    # I am having a set here, because this is the only place that deals with state vars
    id_set = set()
    for d in variables:
        id = d.get("id")
        assert id not in id_set, "Duplicated variable id {}".format(id)
        id_set.add(id)
        # TODO: this is terrible choice. Also, one should be able to do that directly from Yosys
        if "width" not in d.keys():
            width = 1 
        else:
            width = d.get("width")
        expr = d.get("expr")
        var = "{}_{}".format(id, prefix)
        val = d.get("val")
        constraints.add_constraint(InitialStateConstraint(id, var, expr, width, val))

    for var in constraints.collect_vars_from_expressions():
        if var not in aux_var_dict.ids:
            aux_var_dict.add_aux_var_if_none(AuxVar(var, 1, var))

    return constraints


#### 
#### Helper functions for metavariables
#### 


def expandMetaVariable(var: str, rng: int, dict_):
    newDict = {}
    for in_ in dict_.keys():
        in_idxs = getIndexMetaVariables(in_)
        if var in in_idxs:
            for i in range(rng):
                in_new = replaceIndexMetaVariable(in_, var, str(i))
                if in_new in dict_.keys():
                    print(f"Duplicated identifier {in_new} resulting from expansion process")
                    exit(1)
                if isinstance(dict_[in_], list):
                    l = []
                    for o in dict_[in_]:
                        val_new = {}
                        for k in o.keys():
                            if type(o[k]) is str:
                                val_new[k] = replaceIndexMetaVariable(o[k], var, str(i))
                            else:
                                val_new[k] = o[k]
                        l.append(val_new)
                    newDict[in_new] = l
                elif isinstance(dict_[in_], dict):
                    val_new = {}
                    for k in dict_[in_].keys():
                        if type(dict_[in_][k]) is str:
                            val_new[k] = replaceIndexMetaVariable(dict_[in_][k], var, str(i))
                        else:
                            val_new[k] = dict_[in_][k]
                    newDict[in_new] = val_new
                else:
                    print(f"The values in dictionary {dict_} can only be other dictionaries or lists of dictionaries")
                    exit(1)
        else:
            newDict[in_] = dict_[in_]
    return newDict

####
#### Helper functions for constructing observations and state variables
####
