import json
import os
import shutil
from config import CONF
from subprocess import run, PIPE, STDOUT


ctr = 0

def log(msg):
    global ctr
    if CONF.verbose_verification:
        print(f">>> Verification {ctr}) {msg}")
        ctr += 1

def run_process(cmd, verbose = True):
    if verbose and CONF.verbose_external_processes:
        print("Execute {}".format(" ".join(cmd) ))
    o_ = run(cmd, stdout=PIPE, stderr=STDOUT)
    output  = o_.stdout.decode("utf-8")
    if verbose and CONF.verbose_external_processes:
        print(output )
    return output


def logfile(content):
    with open( CONF.outFolder + "/logfile", "a") as lf:
        lf.write(content)

def logtimefile(content):
    print("--------------------------")
    with open( CONF.outFolder + "/logtimefile", "a") as lf:
        lf.write(content)
        print("--------------------------")

def inv2str(invariant):
    if len(invariant) == 0:
        return ["empty"]
    else:
        inv_str = []
        for inv in invariant:
            if inv.get("attrs")[0].get("initval") == None or inv.get("attrs")[0].get("initval") == "none":
                inv_str.append("\t- {{ id: {0}, cond: {1}, attrs: [ {{ value: {2}, width: {3} }} ]}}\n"
                .format(inv.get("id"), str(inv.get("cond")), inv.get("attrs")[0].get("value"), str(inv.get("attrs")[0].get("width"))))
            else:
                inv_str.append("\t- {{ id: {0}, cond: {1}, attrs: [ {{ value: {2}, width: {3}, initval: {4} }} ]}}\n"
                .format(inv.get("id"), str(inv.get("cond")), inv.get("attrs")[0].get("value"), str(inv.get("attrs")[0].get("width")), str(inv.get("attrs")[0].get("initval"))))
        return inv_str



def parse_parts(prefix, line):
    if prefix in line:
        # remove the prefix
        start = line.find(prefix)
        rest = line[start + len(prefix):]

        # Extract the signal name
        name_end = rest.find('=')
        name = rest[:name_end].strip()
        # print("name =", name)

        # Extract the part after '=' and parse the binary constant
        assign_part = line.split('=')[1].strip().rstrip(';')

        # Split into width and binary value like "24'b0001..."
        width_part, binary_part = assign_part.split("'b")
        # print("binary_part = ", binary_part)
        bit_width = int(width_part)
        value = int(binary_part, 2)
        return name, value
    else:
        return None


exported_cnt = 0
def export_counter_example(tb_file):
    global exported_cnt

    counter_example_folder = CONF.outFolder + "/counterexamples/"
    if exported_cnt == 0:        
        if os.path.exists(counter_example_folder):
            shutil.rmtree(counter_example_folder)
        os.makedirs(counter_example_folder)

    log(f"Exporting counterexample with number {exported_cnt}")


    lefts, rights = [], []
    with open(tb_file, "r") as file:
        for line in file:
            prt = parse_parts("left.", line)
            if prt is not None:
                lefts.append(prt)

            prt = parse_parts("right.", line)
            if prt is not None:
                rights.append(prt)


    for (suffix, arr) in [("_left", lefts), ("_right", rights)]:
        file_name = counter_example_folder + str(exported_cnt) + suffix
        with open(file_name, "w") as file:
            data = dict(arr)
            json.dump(data, file, indent=4)

    exported_cnt += 1
