import re

from expr_parser import parser


def getIndexMetaVariables(expr:str):
    return set(re.findall('\$\$(.*?)\$\$', expr))

def replaceIndexMetaVariable(expr:str, metavar:str, value:str):
    return re.sub(f'\$\${metavar}\$\$', value, expr)


def collectVars(expr):
    varsSet = set()
    # if expr.startswith("\\") and expr.count("["):
    #     print("xxxxxxxxxx",expr)
    #     varsSet.add(expr)
    # else:
    tree = parser.parse(expr)
    for varNode in tree.find_data("var"):
        ## construct varName
        varName = ""
        for child in varNode.children:
            varName += child.value
        varsSet.add(varName)
    for varNode in tree.find_data("escapedvar"):
        ## construct varName
        varName = ""
        for child in varNode.children:
            varName += child.value
        varsSet.add(varName)
    return varsSet

def initAuxVars(auxvars, idx_dict):
    ## auxVar --> {width, value}
    auxVars_dict = {}
    for in_ in auxvars:
        var_id =  in_.get("id")
        if var_id is not None:
            if var_id not in auxVars_dict.keys():
                var_dict = {}

                var_width = in_.get("width")
                if var_width is None:
                    var_dict["width"] = 1
                else:
                    var_dict["width"] = var_width
                
                var_value = in_.get("value")
                if var_value is None:
                    var_dict["value"] = var_id
                else:
                    var_dict["value"] = var_value
                
                auxVars_dict[var_id] = var_dict
            else:
                print(f"Duplicated identifier {var_id}")
                exit(1)
        else:
            print(f"Auxiliary variable {in_} without identifier")
            exit(1)

    ##### 1. Collect meta-variables
    idxs = idx_dict.keys()

    ##### 2. Expand meta-variables
    for idx in idxs:
        auxVars_dict = expandMetaVariable(idx, idx_dict[idx], auxVars_dict)

    ##### 3. Check that values of aux variables are wires/vars
    for var in auxVars_dict.keys():
        tree = parser.parse(auxVars_dict[var]["value"])
        wires = tree.find_data("wire")
        flag = False
        for w in wires:
            if flag:
                print("The value {} of variable {} is not a wire!".format(auxVars_dict[var]["value"], var))
                exit(1)
            flag = True
            break

    return auxVars_dict


def initObservations(observations, auxVars_dict, idx_dict, prefix):
    ##### 1. Parse observations 
    obs_dict = {} ## obsId -> [ condObs, argObs ]
    for obs in observations:
        obsId = obs.get("id")
        if obsId in obs_dict.keys():
            print(f"Duplicated observation id {obsId}")
            exit(1)
        condObs = { "var" : "{}_{}_cond".format(obsId, prefix) , "expr" : obs.get("cond") , "width" : 1 }
        obs_dict[obsId] = [condObs] 
        idx=0
        for attr in obs.get("attrs"):
            if attr.get("width") is None:
                width = 1 
            else:
                width = attr.get("width")
            if attr.get("init") is None:
                init = "none"
            else:
                init = attr.get("init")
            argObs = { "var" : "{}_{}_arg{}".format(obs.get("id"), prefix, idx) , "expr" : attr.get("value") , "width" : width, "init": init}
            obs_dict[obsId].append(argObs)
            idx=idx+1

    ##### 2. Expand observations (instantiate meta-vars)
    idxs = idx_dict.keys()
    for idx in idxs:
        obs_dict = expandMetaVariable(idx, idx_dict[idx], obs_dict)

    ##### 3. Update auxVars dictionary
    for obsId in obs_dict.keys():
        for obs in obs_dict[obsId]:
            for var in collectVars(obs["expr"]):
                if var not in auxVars_dict.keys():
                    var_dict = {"width": 1, "value": var}
                    auxVars_dict[var] = var_dict

    return obs_dict, auxVars_dict

def initStateVars(variables, auxVars_dict, idx_dict, prefix):
    ##### 1. Parse state variables 
    vars_dict = {} ## varId -> [ expr, width, level ]
    for var in variables:
        varId = var.get("id")
        if varId in vars_dict.keys():
            print(f"Duplicated variable id {varId}")
            exit(1)
        if var.get("width") is None:
            width = 1 
        else:
            width = var.get("width")
        var = { "var": "{}_{}".format(varId, prefix), "expr" : var.get("expr") , "width" : width, "val": var.get("val") }
        vars_dict[varId] = [var] 

    ##### 2. Expand observations (instantiate meta-vars)
    idxs = idx_dict.keys()
    for idx in idxs:
        vars_dict = expandMetaVariable(idx, idx_dict[idx], vars_dict)

    ##### 3. Update auxVars dictionary
    for varId in vars_dict.keys():
        for var_ in vars_dict[varId]:
            for var in collectVars(var_["expr"]):
                if var not in auxVars_dict.keys():
                    var_dict = {"width": 1, "value": var}
                    auxVars_dict[var] = var_dict
    return vars_dict, auxVars_dict


#### 
#### Helper functions for metavariables
#### 

def initMetaVars(metavars):
    idx_dict = {}
    for idx in metavars:
        idx_id = idx.get("id")
        if idx_id is not None:
            if idx_id not in idx_dict.keys():
                if idx.get("range") is None:
                    print(f"Missing range for index meta-variables {idx_id}")
                    exit(1)
                idx_dict[idx_id] = idx.get("range")
            else:
                print(f"Duplicated index meta-variable {idx_id}")
                exit(1)
        else:
            print(f"Missing identifier in index meta-variable {idx}")
            exit(1)
    return idx_dict

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
