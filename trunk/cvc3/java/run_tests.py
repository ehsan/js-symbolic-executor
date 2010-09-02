#!/usr/bin/env python

import sys, os, re, math, time
#, signal
#import resource

# Alexander Fuchs
# update of run_test:
# - works also under windows
# - measures cpu time, not wall clock time, per test case
# - works also for smtlib directories

# BROKEN:
# doesn't work as intended, due to problems on windows.
# so time measurement is actually not as accurate as hoped for.

# documentation taken from run_tests.py:

# Run regression tests of a given level (default: 0, meaning
# minimum amount of tests).  The higher the regression level, the more
# tests to run, and the harder they get.

# Each test may contain information about its regression level,
# expected outcome, expected runtime, whether it produces a proof,
# etc. in the format given below.  This script will scan the first 100
# lines of each test and try to collect this information.

# If some info is not found, defaults are assumed.  Default regression
# level is 0, expected runtime is unbounded, outcome is undefined
# (whatever it returns is OK), proof should be produced if outcome is
# Valid, and if it is produced, it'll be verified.

# Test info is given in the comments; here are examples
# 
# %%% Regression level = 2
# %%% Result = Valid  %% or Invalid, or Unknown
# %%% Runtime = 10   %% in seconds
# %%% Proof = yes    %% or 'no', if it doesn't produce a proof
# %%% Language = presentation %% or 'internal'

# The number of '%' and following spaces can vary, case is not
# important.  Any text after the value is ignored.  Any comments that
# are not recognized are also ignored.


### Constants

# :TODO: @TOP@ with configure, WIN

# general setup
#TEST_PATH = "/home/alexander/d/CVC/REPOSITORY/cvc3_fix/cvc3/testcases"
#RUN_PATH = "/home/alexander/d/CVC/REPOSITORY/FRESH/cvc3/bin"
#os.environ["PATH"] = RUN_PATH + ":" + os.environ["PATH"]


# max. number of lines to read from the testcase file
# when looking for info comments
MAX_INFO_LINES =  100
# for printing, the width of the label column
WIDTH = 24

PRINT_SUMMARY = 1

# valid problem file extensions
FILE_EXTENSIONS = ["cvc", "cvc3", "svc", "smt", "lisp", "lsp"]

# command line options
OPT_VERBOSE = "v"
OPT_QUIET = "q"
OPT_LEVEL = "l"
OPT_TIMEOUT = "t"
OPT_MEMOUT = "m"
OPT_CHECK_TIMEOUT = "rt"
OPT_LANG = "lang"
OPT_VC = "vc"

# test case options
PRO_LEVEL = "l"
PRO_LANG = "lang"
PRO_TIMEOUT = "t"
PRO_RESULT = "result"


#alarm_pipe = None
#alarm_raised = False

#def alarmHandler(signum, frame):
#    raise 'Timeout'
    #alarm_pipe.close()
    #alarm_raise = True

#signal.signal(signal.SIGALRM, alarmHandler)

# while 1:
#     try:
#         signal.alarm(5)
#         t = sys.stdin.readline()
#         signal.alarm(0)
#         print t
#     except 'Timeout':
#         print "too slow"

### helper functions

#def find

def forall (pred, seq):
    return reduce(lambda acc, x: acc and pred(x), seq, True)

def exists (pred, seq):
    return reduce(lambda acc, x: acc or pred(x), seq, False)

def find (pred, seq):
    for x in seq:
        if pred(x):
            return x    

### time

def cut_time (time):
    return math.floor ((time * 10) + 0.5) / 10
    
def get_children_time ():
    #print(os.times())
    (_, _, child_system_time, child_user_time, _) = os.times()
    return child_system_time + child_user_time

def get_start_time ():
    return get_children_time()

def get_used_time (start_time):
    end_time = get_children_time()
    return cut_time(end_time - start_time)
    


### configuration

   
# default values for options
optionsDefault = {
    OPT_VERBOSE : True,
    OPT_LEVEL : 0,
    OPT_TIMEOUT : 0,
    OPT_MEMOUT : 0,
    OPT_CHECK_TIMEOUT : False,
    OPT_LANG : "all",
    OPT_VC : "cvc3",
    }

# precedence order of options is:
# 1. defined as command line options
# 2. defined in problem file
# 3. defined as default in optionsDefault
# otherwise fail
class Config:
    def __init__ (self, options, prover_options):
        # configuration options for this script
        self.options = options
        # options to be passed to the prover
        self.prover_options = prover_options

    # option: name of option whose value is requested
    # optionsProblem: options specified in the current problem
    def get (self, option, optionsProblem = None):
        if self.options.has_key(option):
            return self.options[option]
        elif optionsProblem != None and optionsProblem.has_key(option):
            return optionsProblem[option]
        elif optionsDefault.has_key(option):
            return optionsDefault[option]
        else:
            raise ("unknown option: " + str(option))

    def getProverOptions (self):
        return self.prover_options




### evaluation of option settings per problem file


def match_line(key, line):
    match = re.search("^(;|\s|%|#)*" + key + "\s*=\s*(?P<value>\S+)", line)
    if match != None:
        return match.group("value").lower()

# Read the first 'maxInfoLines' of the problem specification
# and fetch information from the comments
def get_problem_opt (name):
    #print ("get_problem_opt" + " " + name);
    options = {}
    prover_options = []
    
    try:
        problem_file = open (name)
        lines = 0
        # readline will just return "\n" after EOF
        while (lines < MAX_INFO_LINES):
            lines += 1
            line = problem_file.readline()

            match = match_line("Regression level", line)
            if match != None:
                try:
                    options[PRO_LEVEL] = int(match)
                except ValueError:
                    sys.stderr.write("Regression level requires an integer argument, got : " + match + " in " + name + "\n")
                continue

            match = match_line("Result", line)
            if match != None:
                if match in ["valid", "invalid", "satisfiable", "unsatisfiable", "unknown"]:
                    options[PRO_RESULT] = match
                else:
                    sys.stderr.write("Result has invalid argument: " + match + " in " + name + "\n")
                    
                continue

            match = re.search("^\s*:status\s*(?P<value>\S+)", line)
            if match != None:
                match = match.group("value").lower()
                if match == "unsat":
                    options[PRO_RESULT] = "unsat"
                    #options[PRO_RESULT] = "unsatisfiable"
                elif match == "sat":
                    options[PRO_RESULT] = "sat"
                    #options[PRO_RESULT] = "satisfiable"
                elif match == "unknown":
                    options[PRO_RESULT] = "unknown"
                else:
                    sys.stderr.write("status has invalid argument: " + match + " in " + name + "\n")
            
            match = match_line("Runtime", line)
            if match != None:
                try:
                    options[PRO_TIMEOUT] = int(match)
                except ValueError:
                    sys.stderr.write("Runtime requires an integer argument, got : " + match + " in " + name + "\n")
                continue

            match = match_line("Language", line)
            if match != None:
                options[PRO_LANG] = match
                continue

            match = match_line("Program Options", line)
            if match != None:
                prover_options = match.split()
                continue

        problem_file.close ()

    except IOError, (error_nr, error_string):
        print ("Couldn't open " + name + " : " + error_string)
        return (options, prover_options)

    # If regression level is not set, make it 3. So, if a lower level
    # is requested, only explicitly marked tests will be run.
    if not options.has_key(PRO_LEVEL):
        options[PRO_LEVEL] = 3
        
    # If the input language is not defined, guess it by extension
    if not options.has_key(PRO_LANG):
        ext = find(lambda x: name.endswith(x), FILE_EXTENSIONS)
        if ext == None:
            sys.stderr.write("Couldn't determine language of " + name + "\n")
        elif ext == "cvc" or ext == "cvc3" or ext == "svc":
            options[PRO_LANG] = "presentation"
        elif ext == "smt":
            options[PRO_LANG] = "smtlib"
        elif ext == "lisp" or ext == "lsp":
            options[PRO_LANG] = "lisp"
        else:
            sys.stderr.write("unexpected extension " + ext + " in " + name + "\n")

    return (options, prover_options)






### command line parameters

optionsHelp = {
    "-h" : "Print this help and exit",
    "-" + OPT_VERBOSE : "Be verbose (default, opposite of -q)",
    "-" + OPT_QUIET : "Quiet mode (opposite of -v)",
    "-" + OPT_LEVEL + " n" : "Set regression level (default 0, the easiest level)",
    "-" + OPT_TIMEOUT + " secs" : "Run each executable for at most 'secs' seconds [0 = no limit]",
    "-" + OPT_MEMOUT + " MB" : "Abort if memory limit is exceeded [0 = no limit]",
    "+" + OPT_CHECK_TIMEOUT: "Check that each test finishes within the specified runtime",
    "-" + OPT_CHECK_TIMEOUT: "Do not check whether test finishes within the specified runtime (default)",
    "-" + OPT_LANG + " name" : "Use the named input language only (default=all)",
    "-" + OPT_VC + " prog" : "Use prog to run tests (default=cvc3)",
    }

usageString = \
'''run_tests.py [ options ] [ test1 test2 ... ] [ -- [ command line options ] ]"

Run regression tests.  Concrete test files or directories
with test files should be specified by name with a full path or
relative path to the current directory.  If none specified, all
subdirectories are searched for test files. Subdirectories
are searched recursively, but symbolic links do directories are
not followed.

Default running mode is overriden by test specs;
test specs are overriden by command line options."'''


### command line parameter evaluation


# conversion of an argument from string to int
def to_int(option, value):
    try:
        return int(value)
    except ValueError:
        sys.stderr.write("Option " + option + " requires an integer argument, got : " + value + " \n")
        sys.exit(1)

# increment the position in sys.argv
def next_argument(i, option):
    i += 1
    if i > sys.argv:
        sys.stderr.write("Option " + option + " requires an argument\n")
        sys.stderr.write("Run run_tests -h for help\n")
        sys.exit(1)
    return i

      
# evaluate sys.argv
def eval_arguments ():
    # results of argument evaluation:
    # options for this script
    options = {}
    # list of testcases to run
    testcases = []
    # prover options
    prover_options = []
    
    i = 1
    while i < len(sys.argv):
        # first we expect options for the script,
        # then after "--" options for the prover.
        if sys.argv[i] == "--":
            i += 1 
            prover_options = sys.argv[i:]
            break
        
        elif sys.argv[i] == "-h":
            print(usageString)
            for (option, help_string) in optionsHelp.iteritems():
                print(option.ljust(12) + help_string)
            sys.exit()

        elif sys.argv[i] == "+" + OPT_CHECK_TIMEOUT:
            options[OPT_CHECK_TIMEOUT] = True
        elif sys.argv[i] == "-" + OPT_CHECK_TIMEOUT:
            options[OPT_CHECK_TIMEOUT] = False
        elif sys.argv[i] == "-" + OPT_VERBOSE:
            options[OPT_VERBOSE] = True
        elif sys.argv[i] == "-" + OPT_QUIET:
            options[OPT_VERBOSE] = False
                
        elif sys.argv[i] == "-" + OPT_LANG:
            i = next_argument(i, sys.argv[i])
            options[OPT_LANG] = sys.argv[i]
        elif sys.argv[i] == "-" + OPT_LEVEL:
            i = next_argument(i, sys.argv[i])
            options[OPT_LEVEL] = to_int(OPT_LEVEL, sys.argv[i])
        elif sys.argv[i] == "-" + OPT_TIMEOUT:
            i = next_argument(i, sys.argv[i])
            options[OPT_TIMEOUT] = to_int(OPT_TIMEOUT, sys.argv[i])
        elif sys.argv[i] == "-" + OPT_MEMOUT:
            i = next_argument(i, sys.argv[i])
            options[OPT_MEMOUT] = to_int(OPT_MEMOUT, sys.argv[i])
        elif sys.argv[i] == "-" + OPT_VC:
            i = next_argument(i, sys.argv[i])
            options[OPT_VC] = sys.argv[i]

        # This must be a testcase name            
        else:
            testcases.append(sys.argv[i])
            
        i = i + 1

    return (options, testcases, prover_options)



### get test cases



# 'enumeration'
RES_TESTS, RES_TIME, RES_CORRECT, RES_PROBLEMATIC, RES_INCORRECT, \
RES_FAILED, RES_TIMEOUT, RES_MEMOUT, RES_ARITH, RES_TOO_LONG, RES_MUCH_TOO_LONG, RES_TOO_FAST, \
RES_MUCH_TOO_FAST, RES_LANG, RES_STRANGE = range(15)

def create_results ():
    results = {}
    results[RES_TESTS] = 0
    results[RES_TIME] = 0
    results[RES_CORRECT] = 0
    results[RES_PROBLEMATIC] = 0
    results[RES_INCORRECT] = []
    results[RES_FAILED] = []
    results[RES_TIMEOUT] = []
    results[RES_MEMOUT] = []
    results[RES_ARITH] = []
    results[RES_TOO_LONG] = []
    results[RES_MUCH_TOO_LONG] = []
    results[RES_TOO_FAST] = []
    results[RES_MUCH_TOO_FAST] = []
    results[RES_LANG] = []
    results[RES_STRANGE] = []
    return results

### run tests

# is file name a test case name?
def is_test_case(config, problem_options):
    # a test case
    if problem_options.has_key(PRO_LANG):
        # either all or this particular language must be ok
        return config.get(OPT_LANG) == "all" or config.get(OPT_LANG) == problem_options[PRO_LANG]

    # unknown file type
    else:
        return 0

def run_test (config, name, results, check_lang = False):
    (problem_options, problem_prover_options) = get_problem_opt(name)
    #
    if is_test_case(config, problem_options):
	# Check regression level
        if problem_options[PRO_LEVEL] > config.get(OPT_LEVEL):
	    # Regression level of this test is too high; skip it
	    return

	# Print the testcase name
        print("=" * WIDTH)
        print(name + " : ")
	# Print some testcase specific info
        print_test_info(config, problem_options, problem_prover_options)

        # setup prover arguments
        arguments = []
        arguments.append(config.get(OPT_VC))
        # we don't check for proofs anyway, so we disable them
        arguments.append("-proofs")
        # set language
        if problem_options[PRO_LANG] != "representation":
            arguments.append("-lang")
            arguments.append(problem_options[PRO_LANG])
        # add general prover options
        for arg in config.getProverOptions():
            arguments.append(arg)
        # add problem specific prover options
        for arg in problem_prover_options:
            arguments.append(arg)
        if config.get(OPT_TIMEOUT) > 0:
            arguments.append("-timeout");
            arguments.append(repr(config.get(OPT_TIMEOUT)))
        arguments.append(name)
        # redirect error to stdout
        arguments.append(" 2>&1")
        

        command = " ".join(arguments)
        #print("***")
        print("Running " + command)
        print
        #print("***");

        #reader, writer = os.pipe()
        #start_time = get_start_time()
        start_time = time.time()
        pipe = os.popen(command);
        #global alarm_pipe
        #global alarm_raised
        #if config.get(OPT_TIMEOUT) > 0:
            #alarm_pipe = pipe
            #alarm_raised = False
            #signal.alarm(config.get(OPT_TIMEOUT))
        #pid = os.fork()
#         if pid == 0:
#             try:
#                 # set_resource_limits
#                 #if config.get(OPT_TIMEOUT) > 0:
#                 #    resource.setrlimit (resource.RLIMIT_CPU, (config.get(OPT_TIMEOUT), config.get(OPT_TIMEOUT)))
#                 #if config.get(OPT_MEMOUT) > 0:
#                 #    MEMORY_LIMIT = config.get(OPT_MEMOUT) * 1024 * 1024
#                 #    resource.setrlimit (resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))

#                 # forward output to parent process
#                 os.close(reader)
#                 os.dup2(writer, sys.stdout.fileno ())
#                 os.dup2(writer, sys.stderr.fileno ())

#                 # run prover
#                 os.execvp(arguments[0], arguments)
#             except OSError, (error_nr, error_string):
#                 sys.stderr.write("Error in executing '" + command + "': " + error_string + "\n")
#                 sys.exit(error_nr)

#         else:
            #os.wait()
            #os.close(writer)
        results[RES_TESTS] += 1
        # run prover
        #os.execvp(config.get(OPT_VC), arguments)
        #pipe = os.popen(command)
        #pipe = os.fdopen(reader, 'r')

        # check output
        result = None
        resultError = None
        resultTimeout = False
        resultMemout = False
        resultArith = False
        #:TODO: select on pipe with timeout
        #try:
        if True:
            for line in pipe:
                print line,

                if line.startswith("*** Out of memory") \
                       or line.startswith("Out of memory") \
                       or line.startswith("terminate called after throwing an instance of 'std::bad_alloc'"):
                    resultMemout = True

                # cvc timout: cygwin/.net
                if line.startswith("Interrupted by signal 14 (self-timeout).") or line.startswith("self-timeout"):
                    resultTimeout = True

                if line.count("arithmetic overflow"):
                    resultArith = True
                    
                # get only first result
                if result == None:
                    chomped = line.rstrip().lower()
                    if chomped in ["valid.", "invalid.", "satisfiable.", "unsatisfiable.", "unknown.", "unsat.", "sat."]:
                        result = chomped[:-1]
                    elif chomped in ["unknown", "unsat", "sat"]:
                        result = chomped
        #except 'Timeout':
        #    resultTimeout = True
        #    pipe.close()
        #    exit_val = -1
                        
        #signal.alarm(0)
        #if alarm_raised:
        #    alarm_pipe = None
        #    alarm_raised = False
        #    resultTimeout = True
        #else:
        #if not resultTimeout:
        exit_val = pipe.close()
            
        #(_, exit_val) = os.wait ()
        #used_time = get_used_time(start_time)
        end_time = time.time()
        used_time = cut_time(end_time - start_time)

        # check run time
        print("Program Runtime: " + str(used_time) + " sec"),
        if result != None:
            results[RES_TIME] += used_time
        if config.get(OPT_CHECK_TIMEOUT) and problem_options.has_key(PRO_TIMEOUT):
            expected_time = problem_options[PRO_TIMEOUT]
            if used_time > expected_time:
                if used_time > 10 * expected_time:
                    results[RES_MUCH_TOO_LONG].append(name)                        
                    print(" MUCH")
                print(" LONGER than expected: " + str(expected_time) + " sec")
                results[RES_TOO_LONG].append(name)             
                results[RES_PROBLEMATIC] += 1

            elif ((problem_options[OPT_TIMEOUT] >= 4 and expected_time <= 4
                   and used_time < expected_time - 2)
                  or
                  (used_time > 15 and used_time <= (17 * expected_time) / 20)):
                if used_time <= expected_time / 2:
                    results[RES_MUCH_TOO_FAST].append(name)                        
                    print(" MUCH")
                print(" FASTER than expected: " + str(expected_time) + " sec")
                results[RES_TOO_LONG].append(name)                        
                results[RES_PROBLEMATIC] += 1
        print

        # check prover status
        # resource out: memory
        if resultMemout:
            results[RES_MEMOUT].append(name)
            resultError = RES_MEMOUT
            print("*** Out of memory ")
                    
        # resource out: arithmetic precision
        elif resultArith:
            results[RES_ARITH].append(name)
            resultError = RES_ARITH
            print("*** arithmetic overflow ")

        # resource out: time - at least on my linux version ... is this defined somewhere?
        elif resultTimeout or (exit_val == 9 and config.get(OPT_TIMEOUT) > 0 and used_time >= config.get(OPT_TIMEOUT)):
            results[RES_TIMEOUT].append(name)
            resultError = RES_TIMEOUT
            print("*** Timed out ")

        elif exit_val != None:
            if config.get(OPT_TIMEOUT) == 0 and config.get(OPT_MEMOUT) == 0:
                results[RES_FAILED].append(name)
                print("*** FAILED with exit code " + str(exit_val))
                sys.stderr.write("Warning, unexpected termination with exit code " + str(exit_val) + "\n")
                
            else:
                results[RES_FAILED].append(name)
                print("*** FAILED with exit code " + str(exit_val))
                sys.stderr.write("Warning, unexpected termination with exit code " + str(exit_val) + "\n")

        # check that computed result is the expected result
        elif problem_options.has_key(PRO_RESULT):
            if result == None:
                results[RES_FAILED].append(name)
                sys.stdout.write("FAILED (no result, expected " + problem_options[PRO_RESULT] + ")\n")
                sys.stderr.write("FAILED (no result, expected " + problem_options[PRO_RESULT] + ")\n")
            elif problem_options[PRO_RESULT] != result:
                if result == "unknown":
                    results[RES_STRANGE].append(name)
                    results[RES_PROBLEMATIC] += 1
                    sys.stdout.write("Warning, expected " + problem_options[PRO_RESULT] + " but got unknown\n")
                    sys.stderr.write("Warning, expected " + problem_options[PRO_RESULT] + " but got unknown\n")
                elif problem_options[PRO_RESULT] == "unknown":
                    results[RES_STRANGE].append(name)
                    results[RES_PROBLEMATIC] += 1
                    sys.stdout.write("Warning, expected unknown but got " + result + "\n")
                    sys.stderr.write("Warning, expected unknown but got " + result + "\n")
                else:
                    results[RES_INCORRECT].append(name)
                    resultError = RES_INCORRECT
                    sys.stdout.write("FAILED (incorrect result, expected " + problem_options[PRO_RESULT] + " but got " + result + ")\n")
                    sys.stderr.write("FAILED (incorrect result, expected " + problem_options[PRO_RESULT] + " but got " + result + ")\n")
            else:
                results[RES_CORRECT] += 1
                print("Result is correct")

        # any result is fine, as we don't know the correct result
        elif result != None:
            results[RES_CORRECT] += 1
            print("Result is correct")

        # no result
        else:
            results[RES_STRANGE].append(name)
            results[RES_PROBLEMATIC] += 1
            print("No result")
            
        if PRINT_SUMMARY:
            short_name = os.path.basename(name)
            if result != None:
                printResult = result
            elif resultError == RES_INCORRECT:
                printResult = "unsound:"
            elif resultError == RES_TIMEOUT:
                printResult = "timeout"
            elif resultError == RES_MEMOUT:
                printResult = "memout"
            elif resultError == RES_ARITH:
                printResult = "arith_overflow"
            else:
                printResult = "???"
                    
            print("SUMMARY: " + name)
            print((short_name + " ").ljust(40) + (printResult + " ").ljust(20) + str(used_time))

    elif check_lang:
        results[RES_LANG].append(name)
        results[RES_PROBLEMATIC] += 1

    else:
        print("IGNORE " + name)

    sys.stdout.flush()
        

# expects strings, potentially with number
def cmpStrNum(x, y):
    if x == y:
        return 0

    # find first different character
    xLength = len(x)
    yLength = len(y)
    index = 0
    while (index < xLength and index < yLength):
        if x[index] == y[index]:
            index += 1
        elif (not x[index].isdigit()) or (not y[index].isdigit()):
            return cmp(x[index], y[index])

        # compare as numbers
        else:
            # find start of number
            start = index
            while start >= 0 and x[start].isdigit():
                start -= 1
            start += 1

            xEnd = index
            while xEnd < xLength and x[xEnd].isdigit():
                xEnd += 1
            
            yEnd = index
            while yEnd < yLength and y[yEnd].isdigit():
                yEnd += 1

            xNum = int(x[start:xEnd])
            yNum = int(y[start:yEnd])
            return cmp(xNum, yNum)

    # one string is prefix of the other
    if index >= xLength:
        return -1
    if index >= yLength:
        return 1
    else:
        raise ("cmpStrNum: " + x + " " + y)
    
# find all test cases in directory
def find_test_case((config, results), dir_name, files_in_dir):
    files_in_dir.sort(cmpStrNum)
    for file_name in files_in_dir:
        file_path = os.path.join (dir_name, file_name)

        if os.path.isfile (file_path) and exists(lambda x: file_name.endswith(x), FILE_EXTENSIONS):
            run_test(config, file_path, results)

def run_tests(config, test_cases):
    #test_cases.sort()
    results = create_results()
    for test_case in test_cases:
        # if a file, try it
        if os.path.isfile(test_case):
            run_test(config, test_case, results, True)

        # else traverse subdirectories
        elif os.path.isdir(test_case):
            os.path.walk(test_case, find_test_case, (config, results))

        else:
            sys.stderr.write("*** WARNING: cannot find testcase "
                             + test_case + " : no such file or directory\n")
    return results



### printing

def print_setup(config):
    if config.get(OPT_VERBOSE):
        print("*" * WIDTH)
        # get prover to use (and remove eol)
        prover = os.popen("which " + config.get(OPT_VC)).readline()[:-1]
        print("Prover: ".ljust(WIDTH) + prover)
        print("Regression level: ".ljust(WIDTH) + repr(config.get(OPT_LEVEL)))
        print("Language: ".ljust(WIDTH) + config.get(OPT_LANG))
        if(config.get(OPT_TIMEOUT) > 0):
            print("Time limit per test: ".ljust(WIDTH) + str(config.get(OPT_TIMEOUT)) + " sec")
        if(config.get(OPT_MEMOUT) > 0):
            print("Memory limit per test: ".ljust(WIDTH) + str(config.get(OPT_MEMOUT)) + " MB")
        #print("PATH = ", $ENV{'PATH'})
        print("*" * WIDTH)


def print_test_info (config, problem_options, problem_prover_options):
    if config.get(OPT_VERBOSE):
        print("Language: " + problem_options[PRO_LANG])
        if config.get(OPT_CHECK_TIMEOUT) and problem_options.has_key(PRO_TIMEOUT):
            print("Expected runtime: " + problem_options[PRO_TIMEOUT] + " sec")
        
        if problem_options.has_key(PRO_RESULT):
            print("Expected result: " + problem_options[PRO_RESULT])

        print("Program options: " + " ".join(config.getProverOptions() + problem_prover_options))


def print_end (config, results):
    print
    print("Statistics:")
    print("Total tests run: " + repr(results[RES_TESTS]));
    print("Total running time: " + repr(results[RES_TIME]) + " sec")

    if config.get(OPT_VERBOSE) and results[RES_TESTS] > 0:
        print
        print("Detailed Statistics:")
        print("Correct results: ".ljust(WIDTH) + repr(results[RES_CORRECT]));
        print("Incorrect: ".ljust(WIDTH) + repr(len(results[RES_INCORRECT])));
        print("Problematic cases: ".ljust(WIDTH) + repr(results[RES_PROBLEMATIC]))
        print("Timed out: ".ljust(WIDTH) + repr(len(results[RES_TIMEOUT])));
        print("Out of memory: ".ljust(WIDTH) + repr(len(results[RES_MEMOUT])));
        print("Arithmetic overflow: ".ljust(WIDTH) + repr(len(results[RES_ARITH])));
        print("Failed: ".ljust(WIDTH) + repr(len(results[RES_FAILED])));
                
        test_cases = results[RES_FAILED]
        if len(test_cases) > 0:
            print("Failed tests: " + repr(len(test_cases)))
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_INCORRECT]
        if len(test_cases) > 0:
            print("Tests with wrong results [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_STRANGE]
        if len(test_cases) > 0:
            print("Strange results [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_TIMEOUT]
        if len(test_cases) > 0:
            print("Tests timed out [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_MEMOUT]
        if len(test_cases) > 0:
            print("Tests out of memory [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_ARITH]
        if len(test_cases) > 0:
            print("Arithmetic overflow [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_TOO_FAST]
        if len(test_cases) > 0:
            print("Tests running faster than expected [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_MUCH_TOO_FAST]
        if len(test_cases) > 0:
            print("...including tests running at least twice as fast as expected [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_TOO_LONG]
        if len(test_cases) > 0:
            print("Tests running longer [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_MUCH_TOO_LONG]
        if len(test_cases) > 0:
            print("...including tests running WAT too long [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)

        test_cases = results[RES_LANG]
        if len(test_cases) > 0:
            print("Tests with wrong input language [" + repr(len(test_cases)) + "]:")
            for test_case in test_cases:
                print("  " + test_case)




### main

def main ():
    # evaluate command line
    (options, test_cases, prover_options) = eval_arguments()
    config = Config(options, prover_options)

    # run the prover on all test cases
    print_setup(config)
    results = run_tests(config, test_cases)
    print_end(config, results)

main ()
