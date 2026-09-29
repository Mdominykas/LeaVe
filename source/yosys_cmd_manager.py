# this code is more or less copied from the contract_predictors repository
from pathlib import Path
import subprocess

from subprocess import run, PIPE, STDOUT
from typing import List, Tuple

from typeguard import typechecked

from auxilary_variables import AuxVarDict
from config import CONF
from observations import InitialStateConstraintList, PreparedObservationList, collectVars
from rtl_parts import RTLMemory, RTLVariable
from util import run_process

def escape_id(id):
    if (id.count("[")) and (id.count(".") == 0):
        return "\\" + id
    else:
        return id

class YosysCommand:
    def __init__(self):
        assert False, "base yosys command should not be constructed"


    def to_string(sefl):
        assert False, "base yosys command can not be converted to string"


class StringYosysCommand(YosysCommand):
    def __init__(self, cmd_str):
        self.cmd_str = cmd_str


    def to_string(self):
        return self.cmd_str


class YosysSMTCommandManager:
    def __init__(self, yosys_smtbmc_path):
        # TODO: rewrite with a map, if I end up using this thing, cause that can prevent some errors
        self.options = []
        self.set_solver("yices")
        self.set_no_init()
        self.yosys_smtbmc_path = yosys_smtbmc_path


    @typechecked
    def set_dump_vcd(self, vcd_file_name: str):
        self.options.append("--dump-vcd")
        self.options.append(vcd_file_name)


    def set_no_init(self):
        self.options.append("--noinit")


    @typechecked
    def set_solver(self, solver_name: str):
        self.options.append("-s")
        self.options.append(solver_name)


    @typechecked
    def set_time_steps(self, step_cnt: int, skip_init: int|None = None):
        self.options.append("-t")
        if skip_init is not None:
            self.options.append("{}:{}".format(skip_init, step_cnt))
        else:
            self.options.append("{}".format(step_cnt))


    @typechecked
    def verify(self, smt_output_file: str, log=True):
        cmd = [self.yosys_smtbmc_path, *self.options, smt_output_file]

        if log:
            print("yosys-smtbmc will run script: \"{}\"".format(cmd))

        here = Path(__file__).resolve().parent
        process = subprocess.run(
            cmd,
            cwd=here,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            )

        if process.stdout:
            if log:
                for line in process.stdout:
                    print(line, end='')  # output lines as they appear
        
        if not log:
            self.process_for_logging = process

        if process.returncode != 0:
            if log:
                print(f"yosys-smtbmc exited with return code {process.returncode}")
                print("standard output was:")
                for line in process.stdout:
                    print(line, end='')
                print("yosys-smtbmc error msgs:")
                if process.stderr:
                    for line in process.stderr:
                        print(line, end='')
            return False
        return True


class YosysCommandManager:
    def __init__(self):
        self.cmds = []
        self.preservation_passes = {}

    def build_cmd_string(self):
        return " ; ".join([cmd.to_string() for cmd in self.cmds])
    
    def build_script(self):
        return " \n ".join([cmd.to_string() for cmd in self.cmds])

    @typechecked
    def write_script(self, script_path: str):
        with open(script_path , 'w') as f:
            f.write(self.build_script())

    @typechecked
    def run_from_script(self, script_path: str, verbose: bool=True):
        print("script turi buti:", script_path)
        self.write_script(script_path)
        print("nes sukuriau script:", script_path)
        cmd = [CONF.yosysPath]
        cmd.append("-s{}".format(script_path))
        if verbose and CONF.verbose_verification and CONF.verbose_external_processes:
            print("Execute {}".format(" ".join(cmd) ))
        for m in CONF.yosysAdditionalModules:
            cmd.append(f"-m{m}")

        o_ = run(cmd, stdout=PIPE, stderr=STDOUT)

        output = o_.stdout.decode("utf-8")

        if verbose and CONF.verbose_verification and CONF.verbose_external_processes:
            print(output)

        assert o_.returncode == 0, "Command failed with exit code {}: {}".format(o_.returncode, " ".join(cmd))

    @typechecked
    def add_wire_lifting_pass(self, wire_lifting_json_path: str):
        self.cmds.append(StringYosysCommand("lifting_wires {} ".format(wire_lifting_json_path)))

    @typechecked
    def add_string_pass(self, yosys_pass: str):
        self.cmds.append(StringYosysCommand(yosys_pass))

    def add_hierarchy(self):
        self.cmds.append(StringYosysCommand("hierarchy"))

    @typechecked
    def add_hierarchy_with_top(self, top_module: str):
        self.cmds.append(StringYosysCommand("hierarchy -top {}".format(top_module)))


    def add_hierarchy_auto_top(self):
        self.cmds.append(StringYosysCommand("hierarchy -auto-top"))


    def add_read_verilog_whole_folder(self, verilog_folder: str, add_sv: bool = True):
        sv_flag = "-sv" if add_sv else ""
        self.cmds.append(StringYosysCommand("read_verilog {} {}/*.v".format(sv_flag, verilog_folder)))

    def add_read_verilog_single_file(self, file_name: str, add_sv: bool = True):
        sv_flag = "-sv" if add_sv else ""
        self.cmds.append(StringYosysCommand("read_verilog {} {}".format(sv_flag, file_name)))


    def add_flattening(self):
        self.cmds.append(StringYosysCommand("flatten"))

    @typechecked
    def add_proc_no_rom(self, silent:bool=True):
        if silent:
            prefix = "tee -q "
        else:
            prefix = ""
        self.cmds.append(StringYosysCommand(prefix + "proc -norom"))

    def fix_multi_clock(self):
        self.cmds.append(StringYosysCommand("async2sync ; dffunmap"))

    @typechecked
    def add_proc(self, silent:bool=True):
        if silent:
            prefix = "tee -q "
        else:
            prefix = ""
        self.cmds.append(StringYosysCommand(prefix + "proc"))

    
    def add_set_undef(self):
        self.cmds.append(StringYosysCommand("setundef -anyconst -params"))


    @typechecked
    def add_opt(self, silent:bool=True):
        if silent:
            prefix = "tee -q "
        else:
            prefix = ""
        self.cmds.append(StringYosysCommand(prefix + "opt"))

    # TODO: memory is specific to LeaVe


    def add_techmap(self):
        self.cmds.append(StringYosysCommand("techmap"))

    def add_check(self, output_file=None, assert_errors=False):
        cmd = "check"
        if output_file is not None:
            cmd = "tee -q -o {} check".format(output_file)

        if assert_errors:
            cmd = cmd + " -assert"
        
        self.cmds.append(StringYosysCommand(cmd))

    def add_assert(self, assert_wire: str, assert_cond=None):
        assert isinstance(assert_wire, str)

        if assert_cond is None:
            assert_cmd = ""
        else:
            assert isinstance(assert_cond, str)
            assert_cmd = "-if " + assert_cond
        self.cmds.append(StringYosysCommand("add -assert " + assert_wire + " " + assert_cmd))


    def add_assume(self, assume_wire: str, assume_cond=None):
        assert isinstance(assume_wire, str)
        if assume_cond is None:
            assume_cmd = ""
        else:
            assert isinstance(assume_cond, str)
            assume_cmd = "-if " + assume_cond
        cmd_str = "add -assume " + assume_wire + " " + assume_cmd
        self.cmds.append(StringYosysCommand(cmd_str))


    def add_equality_wire(self, name: str, left_wire: str, right_wire: str, signed=False):
        assert isinstance(name, str) and isinstance(left_wire, str) and isinstance(right_wire, str)
        cmd_str = "add_equality_check {} {} {} ".format(name, left_wire, right_wire) + (" --signed " if signed else "")
        self.cmds.append(StringYosysCommand(cmd_str))


    def add_bitwise_negation_wire(self, out_wire_name: str, in_wire_name: str):
        assert isinstance(out_wire_name, str) and isinstance(in_wire_name, str)
        cmd_str = "add_bitwise_negation {} {}".format(out_wire_name, in_wire_name)
        self.cmds.append(StringYosysCommand(cmd_str))


    @typechecked
    def add_and_of_multiple_wires(self, wire_list, out_name: str):
        temporary_file = self.temporary_file_folder.create_file()
        assert isinstance(out_name, str)
        with open(temporary_file, "w") as out:
            out.write(str(len(wire_list)) + "\n")
            for wire in wire_list:
                assert isinstance(wire, str)
                out.write(wire + "\n")

        self.cmds.append(StringYosysCommand("and_of_multiple_wires {} {}".format(str(temporary_file), out_name)))


    @typechecked
    def get_temporary_file(self, extension="") -> Path:
        temporary_file = self.temporary_file_folder.create_file(extension=extension)
        return temporary_file


    # it generates some unreadable verilog code
    @typechecked
    def export_to_verilog(self, file_name: str, selected: bool = False):
        suffix = " -selected " if selected else ""
        self.cmds.append(StringYosysCommand("write_verilog" + " " + suffix + " " + file_name))

    
    @typechecked
    def export_to_smt2(self, file_name: str, with_wires:bool=True):
        self.cmds.append(StringYosysCommand("write_smt2 " + (" -wires " if with_wires else "") + file_name))

    @typechecked
    def set_top_of_hierarchy(self, module_name: str):
        self.cmds.append(StringYosysCommand("hierarchy -top {}".format(module_name)))

    @typechecked
    def add_select_pass(self, module: str):
        self.cmds.append(StringYosysCommand("select {}".format(module)))

    @typechecked
    def add_module_pass(self, main_module: str, new_module: str, cell_name: str):
        self.cmds.append(StringYosysCommand("addmodule {} {} {}".format(main_module, new_module, cell_name)))

    @typechecked
    def add_connect_port(self, cell: str, port: str, expr: str):
        self.cmds.append(StringYosysCommand("connect -port {} {} {}".format(cell, port, expr)))

    @typechecked
    def add_expose_pass(self, ports_to_expose: List[str]):
        self.cmds.append(StringYosysCommand("expose {} ".format(" ".join(ports_to_expose))))

    # Btw, I don't know what this one does
    @typechecked
    def finalize_module_changes(self, module_name: str, outFolder: str, suffix: str):
        self.set_top_of_hierarchy(module_name)
        self.add_proc_no_rom()
        self.add_flattening()
        self.cmds.append(StringYosysCommand("add -input stuttering_signal 1\n"))
        self.cmds.append(StringYosysCommand("stuttering {} stuttering_signal\n".format(module_name)))
        self.add_opt()
        self.export_to_verilog("{}/{}.v".format(outFolder, module_name), selected=True)
        
        script_file_path = "{}/{}_yosys.script".format(outFolder, suffix)
        self.run_from_script(script_file_path)

    @typechecked
    def flatten_with_extra_steps(self, folder: str, module: str):
        self.add_read_verilog_whole_folder(folder)
        self.set_top_of_hierarchy(module)
        if CONF.usePredictor:
            self.add_wire_lifting_pass(str(Path(CONF.wireLiftingPath).resolve()))

        self.add_proc_no_rom()
        self.add_flattening()
        self.add_select_pass(module)

    @typechecked
    def link_module(self, outFolder: str, module: str, obs_dict: PreparedObservationList|InitialStateConstraintList, aux_vars: AuxVarDict, suffix: str):
        file_name = "{}/{}_{}.v".format(outFolder, module, suffix)
        self.add_read_verilog_single_file(file_name)
        self.add_select_pass(module)
        self.add_proc_no_rom()
        
        self.add_module_pass(module, "{}_{}".format(module, suffix), suffix)
        
        vars = obs_dict.collect_vars_from_expressions()
        for v in vars:
            self.add_connect_port(suffix, v, aux_vars.get_aux_var(v).value)

        ports_to_expose = []
        for obs_atom in obs_dict.get_all_blocks():
            ports_to_expose.append("{}/{}".format(module , obs_atom.var))
        self.add_expose_pass(ports_to_expose)

    @typechecked
    def add_show_regs_mems_pass(self, out_folder: str, module: str):
        self.add_string_pass("show_regs_mems -o {} {}".format(out_folder, module))

    @typechecked
    def show_regs_mems_workflow(self, out_folder: str, module: str) -> tuple[List[RTLMemory], List[RTLVariable]]:
        self.add_read_verilog_whole_folder(out_folder)
        self.set_top_of_hierarchy(module)
        if CONF.usePredictor:
            relative_path = Path(CONF.wireLiftingPath)
            self.add_wire_lifting_pass(str(relative_path.resolve()))
        self.add_proc_no_rom()
        self.add_flattening()
        self.add_select_pass(module)
        self.add_show_regs_mems_pass(out_folder, module)
        script_name = "{}/show_yosys.script".format(out_folder)
        self.run_from_script(script_name)

        memories, variables = [], []
        f = open("{}/regs_mems.dat".format(out_folder))
        for line in f:
            parts = line.split(" ")
            # Memories: name width size filename
            if parts[0] == "Memories":
                id = parts[1]
                if id not in CONF.memoryList:
                    if (not id.count("$")) and (not (id.startswith("_") and id.endswith("_"))):
                        width = int(parts[2])
                        size = int(parts[3])
                        filename = (parts[4].replace("\n", "")).split("/")[-1]
                        memories.append(RTLMemory(id, width, size, filename))
            # create the invariants for registers 
            # Registers: name width
            elif parts[0] == "Variables":
                id = parts[1]
                width = int(parts[2])
                if (not id.count("$")) and (not (id.startswith("_") and id.endswith("_"))):
                    id = escape_id(id)
                    variables.append(RTLVariable(id, width))
            elif parts[0] == "Registers":
                # TODO: I don't understand, why this is not being processed. I think it should be useful in some way...
                pass
            else:
                assert False, "I don't expect anything else in that file, but I found: " + line
        f.close()

        return memories, variables