#! /usr/bin/env python

import os

libs = [
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "QF_AUFBV",
    "QF_AUFLIA",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_RDL",
    "QF_UF",
    "QF_UFBV32",
    "QF_UFIDL",
    "QF_UFLIA",
]


for lib in libs:
    command = "./run_tests.py -vc 'java -esa -Xss100M -jar lib/cvc3.jar' -t 1 -m 500 -l 5 -lang smtlib /media/data/CVC/BENCHMARKS/SMTLIB/" + lib + " > out." + lib
    print command
    os.system(command)
