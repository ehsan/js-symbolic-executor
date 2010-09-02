/*****************************************************************************/
/*!
 * \file main.cpp
 * \brief Main program for cvc3
 * 
 * Author: Clark Barrett
 * 
 * Created: Wed Dec  4 17:21:10 2002
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/

#include <signal.h>
#include <fstream>
#include <iomanip>

#include "os.h"
#include "vc.h"
#include "parser.h"
#include "vc_cmd.h"
#include "command_line_flags.h"
#include "statistics.h"

#ifdef _MSC_VER
#include <windows.h>
#else
#include <unistd.h>
#endif


using namespace std;
using namespace CVC3;


static void parse_args(int argc, char **argv, CLFlags &flags,
		       string& fileName);
static void printUsage(const CLFlags& flags, bool followDisplay);

// Our own name 
static string programName;

static ValidityChecker* vc = NULL;
IF_DEBUG(static DebugTimer* pRuntime = NULL;)

#ifndef _MSC_VER
void sighandler(int signum) {
  cerr << "\nInterrupted by signal " << signum;
  if(signum == SIGALRM)
    cerr << " (self-timeout)";
  cerr << ".  " << programName << " is aborting.\n";
  // Print the debugging info
  IF_DEBUG(if (pRuntime != NULL) CVC3::debugger.setElapsed(*pRuntime);)
  IF_DEBUG(debugger.printAll();)
  if(vc != NULL && vc->getFlags()["stats"].getBool())
    cout << vc->getStatistics() << endl;
  abort();
}
#else
DWORD WINAPI thread_timeout(PVOID timeout) {
  Sleep((int)timeout * 1000);
  cerr << "(self-timeout)." << endl;
  ExitProcess(1);
}
#endif


int main(int argc, char **argv)
{
  CLFlags flags(ValidityChecker::createFlags());
  programName = string(argv[0]);
  IF_DEBUG(DebugTimer runtime(CVC3::debugger.timer("total runtime"));)
  IF_DEBUG(pRuntime = &runtime;)

#ifndef _MSC_VER
  signal(SIGINT, sighandler);
  signal(SIGTERM, sighandler);
  signal(SIGQUIT, sighandler);
  signal(SIGALRM, sighandler);
#endif
  
  string fileName("");

  try {
    parse_args(argc, argv, flags, fileName);
  } catch(Exception& e) {
    cerr << "*** " << e;
    cerr << "\n\nRun with -help option for usage information." << endl;
    exit(1);
  }

  // Set the timeout, if given in the command line options
  int timeout = flags["timeout"].getInt();
  if(timeout > 0) {
#ifndef _MSC_VER
    alarm(timeout);
#else
    // http://msdn2.microsoft.com/en-us/library/ms682453.aspx
    CreateThread(NULL, 0, thread_timeout, (PVOID)timeout, 0, NULL);
#endif
  }

  /*
   * Create and run the validity checker
   */ 

  // Debugging code may throw an exception
  try {
    vc = ValidityChecker::create(flags);
  } catch(Exception& e) {
    cerr << "*** Fatal exception: " << e << endl;
    exit(1);
  }

  // -h flag sets "help" to false (+h would make it true, but that's
  // not what the user normally types in).
  if(!vc->getFlags()["help"].getBool()) {
    printUsage(vc->getFlags(), true);
    return 0;
  }
  if(!vc->getFlags()["unsupported"].getBool()) {
    printUsage(vc->getFlags(), false);
    return 0;
  }
#ifndef VERSION
#define VERSION "unknown"
#endif
  // Similarly, -version sets the flag "version" to false
  if(!vc->getFlags()["version"].getBool()) {
    cout << "This is CVC3 version " << VERSION
      IF_DEBUG( << " (debug build)")
	 << "\n\n";
    cout <<
      "Copyright (C) 2003-2010 by the Board of Trustees of Leland Stanford Junior\n" 
      "University, New York University, and the University of Iowa.\n\n"
      "THIS SOFTWARE PROVIDED AS-IS, WITHOUT ANY WARRANTIES. "
      "USE IT AT YOUR OWN RISK.\n"
	 << endl;
    return 0;
  }

  try {
    // Test if the output language is correctly specified; if not, an
    // exception will be thrown
    vc->getEM()->getOutputLang();
    // Set the timer
    IF_DEBUG(CVC3::debugger.setCurrentTime(runtime);)
    // Read the input file
    vc->loadFile(fileName, vc->getEM()->getInputLang(),
                 flags["interactive"].getBool());
  } catch(Exception& e) {
    cerr << "*** Fatal exception: " << e << endl;
    exit(1);
  }

  IF_DEBUG(CVC3::debugger.setElapsed(runtime);)

  // Print the debugging info
  IF_DEBUG(debugger.printAll();)
  // Print statistics
  if(vc->getFlags()["stats"].getBool()) vc->printStatistics();
  // Destruct the system
  TRACE_MSG("delete", "Deleting ValidityChecker [last trace from main.cpp]");
  try {
    delete vc;
  } catch(Exception& e) {
    cerr << "*** Fatal exception: " << e << endl;
    exit(1);
  }

  return 0;
}

void printUsage(const CLFlags& flags, bool followDisplay) {
  cout << "Usage: " << programName << " [options]\n"
       << programName << " will read the input from STDIN and \n"
       << "print the result on STDOUT.\n"
       << "Boolean (b) options are set 'on' by +option and 'off' by -option\n"
       << "(for instance, +model or -model).\n"
       << "Integer (i), string (s) and vector (v) options \n"
       << "require a parameter, e.g. -width 80\n" 
       << "Also, (v) options can appear multiple times setting "
       << "args on and off,\n"
       << "as in +trace \"enable this\" -trace \"disable that\".\n"
       << "Option names can be abbreviated to the "
       << "shortest unambiguous prefix.\n\n"
       << "The options are:\n";
  vector<string> names;
  // Get all the names of options (they all match the empty string)
  flags.countFlags("", names);
  for(size_t i=0,iend=names.size(); i!=iend; ++i) {
    const CLFlag& f(flags[names[i]]);
    if (f.display() != followDisplay) continue;
    string tpStr; // Print type of the option
    string pref; // Print + or - in front of the option
    string name(names[i]); // Print name and optionally the value
    CLFlagType tp = f.getType();
    switch(tp) {
    case CLFLAG_NULL: tpStr = "(null)"; break;
    case CLFLAG_BOOL:
      tpStr = "(b)"; pref = (f.getBool())? "+" : "-";
      break;
    case CLFLAG_INT:
      tpStr = "(i)"; pref = "-"; name = name+" "+int2string(f.getInt());
      break;
    case CLFLAG_STRING:
      tpStr = "(s)"; pref = "-"; name = name+" "+f.getString();
      break;
    case CLFLAG_STRVEC:
      tpStr = "(v)"; pref = "-"; name = name;
      break;
    default:
      DebugAssert(false, "printUsage: unknown flag type");
    }
    cout << " " << tpStr << " " << pref << setw(25);
    cout.setf(ios::left);
    cout << name << " " << f.getHelp() << "\n";
  }
  cout << endl;
}
  

void parse_args(int argc, char **argv, CLFlags &flags, string& fileName) {
  /* skip 0'th argument */
  argv++;
  argc--;
  bool seenFileName(false);

  for( ; argc > 0; argc--, argv++) {
    if((*argv)[0] == '-' || (*argv)[0] == '+') {
      // A command-line option
      vector<string> names;
      bool val = ((*argv)[0] == '+');
      size_t n = flags.countFlags((*argv)+1, names);
      if(n == 0)
	throw CLException(string(*argv) + " does not match any known option");
      else if(n > 1) {
	ostringstream ss;
	ss << *argv << " is ambiguous.  Possible matches are:\n";
	for(size_t i=0,iend=names.size(); i!=iend; ++i) {
	  ss << "  " << names[i] << "\n";
	}
	throw CLException(ss.str());
      } else {
	string name = names[0];
	// Single match; process the option
	CLFlagType tp = flags[name].getType();
	switch(tp) {
	case CLFLAG_BOOL: flags.setFlag(name, val); break;
	case CLFLAG_INT:
	  argc--;
	  if(argc <= 0)
	    throw CLException(string(*argv)+" (-"+name
			      +") expects an integer argument.");
	  argv++;
	  // FIXME: test for *argv being an integer string
	  flags.setFlag(name, atoi(*argv));
	  break;
	case CLFLAG_STRING:
	  argc--;
	  if(argc <= 0)
	    throw CLException(string(*argv)+" (-"+name
			      +") expects a string argument.");
	  argv++;
	  flags.setFlag(name, *argv);
	  break;
	case CLFLAG_STRVEC:
	  argc--;
	  if(argc <= 0)
	    throw CLException(string(*argv)+" (-"+name
			      +") expects a string argument.");
	  argv++;
	  flags.setFlag(name, pair<string,bool>(*argv,val));
	  break;
	default:
	  DebugAssert(false, "parse_args: Bad flag type: "+int2string(tp));
	}
      }
    } else if(seenFileName) {
      throw CLException("More than one file name given: "+fileName
			+" and "+string(*argv));
    } else {
      fileName = string(*argv);
      seenFileName = true;
    }
  }
}
