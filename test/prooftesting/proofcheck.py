from subprocess import call
import os
import sys

directory = sys.argv[1]
golem_exec = sys.argv[2]

for smt_file in os.listdir(directory):

    smt_file = directory + "/" + smt_file
    proof_file = smt_file + ".proof"
    
    if not smt_file.endswith(".smt2"):
        continue

    with open(proof_file,'w') as f:
        call([golem_exec, smt_file, "--print-witness", "--proof-format=alethe"], stdout = f)
        
    with open(proof_file,'r') as f:
        data = f.read().splitlines(True)

    with open(proof_file,'w') as f:
        f.writelines(data[1:])

    ret_code = call(["carcara", "check", proof_file, "--expand-let-bindings"])

    os.remove(proof_file)

    if ret_code != 0:
        print("Check not successful for", smt_file)

