from typeguard import typechecked

from auxilary_variables import AuxVar
from observations import Observation, ObservationAtom

@typechecked
def escape_id(id: str) -> str:
    if (id.count("[")) and (id.count(".") == 0):
        return "\\" + id
    else:
        return id

@typechecked
def id2val(id: str) -> str:
    if id.count(".") == 0:
        return id
    else:
        return "\\" + id


class RTLVariable:
    @typechecked
    def __init__(self, id: str, width: int):
        self.id = id
        self.width = width

    @typechecked
    def to_aux_var(self) -> AuxVar:
        new_name = id2val(escape_id(self.id))
        return AuxVar(new_name, self.width, new_name)

    @typechecked
    def to_invariant(self) -> Observation:
        new_name = id2val(self.id)
        attrs = [ObservationAtom(new_name, self.width)]
        return Observation(new_name, "1", attrs)


class RTLMemory:
    @typechecked
    def __init__(self, id: str, width: int, size: int, filename: str):
        self.id = id
        self.width = width
        self.size = size
        self.filename = filename

    def to_to_expand(self) -> dict:
        return {"filename": self.filename, "array": self.id.split(".")[-1], "width": self.width, "size": self.size, "mult": "true"}
    
    def to_aux_var(self, i) -> AuxVar:
        new_name = id2val(self.id) + "_" + str(i)
        return AuxVar(new_name, self.width, new_name)

    @typechecked
    def to_invariant(self, i: int) -> Observation:
        new_name = id2val(self.id) + "_" + str(i)
        attrs = [ObservationAtom(new_name, self.width)]
        return Observation(new_name, "1", attrs)