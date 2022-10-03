#! /bin/python3

import os
import sys
import time
import subprocess
import re
import csv
from datetime import datetime

def displayHelp():
    print("Script runs sygus tests from selected folder")
    print("Usage = ./sygusTest.py path_to_tests")

def main():
    path_to_tests = sys.argv[1]
    if not path_to_tests.endswith("/"):
        path_to_tests = path_to_tests + "/"

    suffixlen = len("s_part.smt2")

    projDir = os.path.abspath( os.path.dirname( __file__ ) ) + "/.."
    tests_set = set()
    for fname in os.listdir(path_to_tests):
        if fname.endswith(".sl"):
            testName = path_to_tests + fname
            tests_set.add(testName)

    resTable = [["test", "stdout", "time"]]

    numTests = len(tests_set)
    i = 1
    for t in tests_set:
        print(f"Test {i}/{numTests}: ", t)
        result = [t]
        args = [projDir + "/build/tools/sygus/sygussolver", "--debug", "1", t]
        t1 = time.time()
        try:
            output = subprocess.run(args, timeout=30, stdout=subprocess.PIPE)
            output = output.stdout
            t2 = time.time()
            if output:
                output = output.decode("utf-8").strip()
            else:
                output = "emptyStdout"
            print(output)
            result.append(output)
            result.append(t2-t1)
        except Exception as e:
            result.append(e)
        i += 1
        resTable.append(result)

    now = datetime.now()
    current_time = now.strftime("%d.%m.%Y-%H:%M:%S")
    outName = "results_" + current_time + ".csv"
    with open(outName, 'w') as file:
        writer = csv.writer(file)
        writer.writerows(resTable)

if __name__ == "__main__":
    main()
