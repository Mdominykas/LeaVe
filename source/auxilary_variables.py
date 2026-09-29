from typeguard import typechecked

from config import ConfCls


# TODO: there could be some parsing to ensure that expressions are not wrong
Expr = str

class AuxVar:
    @typechecked
    def __init__(self, id: str, width: int, value: Expr):
        self.id = id
        self.width = width
        self.value = value
    
    def __eq__(self, other):
        if not isinstance(other, AuxVar):
            return NotImplemented
        return self.id == other.id and self.width == other.width and self.value == other.value

    def __repr__(self):
        return f"AuxVar(id={self.id!r}, width={self.width}, value={self.value!r})"


class AuxVarDict:
    @typechecked
    def __init__(self):
        self.aux_vars = []
        self.ids = set()

    @typechecked
    def add_aux_var(self, aux_var: AuxVar, okay_if_identical_exists=True) -> None:
        if not okay_if_identical_exists:
            assert aux_var.id not in self.ids, "The aux_var id: \"{}\" is duplicated".format(aux_var.id)
        elif aux_var.id in self.ids:
            for av in self.aux_vars:
                assert av.id != aux_var.id or av == aux_var, "We can only add an identical aux var, they are: old={} and new={}".format(av, aux_var)
        self.ids.add(aux_var.id)
        self.aux_vars.append(aux_var)

    @typechecked
    def get_aux_var(self, id: str) -> AuxVar:
        for aux_var in self.aux_vars:
            if id == aux_var.id:
                return aux_var
        assert False, "No aux var with such an id"

    @typechecked
    def add_aux_var_if_none(self, aux_var: AuxVar):
        if aux_var.id not in self.ids:
            self.add_aux_var(aux_var)
        else:
            old_aux_var = self.get_aux_var(aux_var.id)
            assert aux_var == old_aux_var, "aux vars are different: old={}, new={}".format(old_aux_var, aux_var)


@typechecked
def get_aux_vars_from_config(conf: ConfCls) -> AuxVarDict:
    aux_var_dict = AuxVarDict()
    for entry in conf.auxiliaryVariables:
        var_id =  entry.get("id")
        assert var_id is not None, "Auxilary variable is without an id"

        # TODO: this seems like a terrible, legacy approach that could lead to a lot of bugs.
        # Sadly,to fix it one needs to go through a lot of configuration files
        width = entry.get("width")
        if width is None:
            width = 1
        
        var_value = entry.get("value")
        if var_value is None:
            var_value = var_id
        
        aux_var_dict.add_aux_var(AuxVar(var_id, width, var_value))
    return aux_var_dict


