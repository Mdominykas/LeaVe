from typeguard import typechecked


@typechecked
class SourceObservationPrediction:
    def __init__(self, id=None, cond=None, avail=None, attr=None):
        self.id = id
        self.cond = cond
        self.avail = avail
        self.attr = attr


## Config
class ConfCls:
    # input/output information
    codeFolder: str = "" # folder with Verilog sources
    outFolder: str = "" # target folder for intermediate data
    prodCircuitTemplate: str = ""
    clockInput: str = ""
    initRegister: str = ""
    lookAhead: str = ""
    usePredictor: str = "True"
    cycleDelayedBound: str = ""

    # Backends
    yosysPath: str = ""
    avrPath: str = ""
    yosysBMCPath : str = ""
    yosysAdditionalModules = []
    inductiveyosysBMCBound : str = ""
    checkyosysBMCBound : str = ""
    directlycheckyosysBMCBound : str = ""
    prefixCheck: str = ""
    yosysBMCSolver: str = "yices"
    yosysSMTPreprocessing  = ["async2sync","dffunmap"] 
    ## alternatives can be ["clk2fflogic"] or ["dffunmap"] or ["async2sync", "dffunmap"]

    yosysCtxCycle = "cycle"
    yosysCtxClock = "clock"
    yosysCtxUUT = "UUT"
    yosysCtxDisplayAtEdge : bool = True

    # iverilog and vpp
    iverilogPath: str = ""
    vvpPath: str = ""

    # product circuit
    selfCompositionInitVariable: str = "init"
    selfCompositionEquality: str = "=="
    selfCompositionInequality: str = "!="

    # root module for analysis
    module: str = ""
    moduleFile: str = ""
    maxinstruction: str = ""
    retirepredicate: str = ""
    memoryList = []

    # output
    outputformat = ""

    #invariant
    invariant = []
    stateInvariant = []

    # observations
    srcObservations = []
    trgObservations = []
    filteredSrcObservations = []

    # predictions
    srcObservationPredictions = []

    #predicates
    predicateRetire = []
    predicatePI = []
    
    # visible state
    state = []
    extrastate = []

    # inputs
    inputs = []

    # auxiliary variables
    auxiliaryVariables = []

    # index metavariables
    metaVars = []

    # preprocessing
    expandArrays = []

    verbose_preprocessing = True
    verbose_verification = True
    verbose_counterexample_checking = True
    verbose_external_processes = False

    def set(self, name, value):
        options = {
            'selfCompositionEquality': ['==', '==='],
            'selfCompositionInequality': ['!=', '!==']
        }

        if self.__getattribute__(name) is None:
            print(f"Error: Unknown configuration variable {name}.\n"
                  f"It's likely a typo in the configuration file.")
            exit(1)
        if type(self.__getattribute__(name)) != type(value):
            print(f"Error: Wrong type of the configuration variable {name}.\n"
                  f"It's likely a typo in the configuration file.")
            exit(1)

        # value checks
        # TODO: would be great to have more of these
        if options.get(name, '') != '' and value not in options[name]:
            print(f"Error: Unknown value '{value}' of configuration variable '{name}'")
            exit(1)

        self.__setattr__(name, value)


    def parseSrcObservationPredictions(self):
        parsed_src_obs_pred = []
        for src_obs_pred in self.srcObservationPredictions:
            assert False, "I removed this part"
            id = src_obs_pred["id"]
            cond = src_obs_pred["cond"]
            avail = src_obs_pred["avail"]
            attrs = src_obs_pred["attrs"]
            assert len(attrs) == 1, "TODO: fix it when there are more (also, there shouldn't be collisions)"
            attr = attrs[0]["value"]
            parsed_src_obs_pred.append(SourceObservationPrediction(id, cond, avail, attr))
        self.srcObservationPredictions = parsed_src_obs_pred


CONF = ConfCls()