/*****************************************************************************/
/*!
 * \file debug.cpp
 * \brief Description: Implementation of debugging facilities.
 *
 * Author: Sergey Berezin
 *
 * Created: Fri Jan 31 11:48:37 2003
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

#include <cstdlib>
#include <fstream>
#include <stdlib.h>

#include "debug.h"

using namespace std;

namespace CVC3 {

// Function for fatal exit.  It just exits with code 1, but is
// provided here for the debugger to set a breakpoint to.  For this
// reason, it is not inlined.
CVC_DLL void fatalError(const std::string& file, int line,
		const std::string& cond, const std::string& msg) {
  cerr <<  "\n**** Fatal error in " << file << ":" << line
       << " (" << cond << ")\n" << msg << endl << flush;
  exit(1);
}

} // end of namespace CVC3

#ifdef _CVC3_DEBUG_MODE

#include <ctime>
#include <iomanip>

namespace CVC3 {
// Similar to fatalError to raise an exception when DebugAssert fires.
// This does not necessarily cause the program to quit.
CVC_DLL void debugError(const std::string& file, int line,
		const std::string& cond, const std::string& msg) {
  ostringstream ss;
  ss << "in " << file << ":" << line << " (" << cond << ")\n" << msg;
  throw DebugException(ss.str());
}


class DebugTime {
public:
  clock_t d_clock;

  // Constructors
  DebugTime() {
    d_clock = 0;
  }
  DebugTime(const clock_t& clock): d_clock(clock) { }

  // Set time to zero
  void reset() {
    d_clock = 0;
  }

  // Incremental assignments
  DebugTime& operator+=(const DebugTime& t) {
    d_clock += t.d_clock;
    return *this;
  }
  DebugTime& operator-=(const DebugTime& t) {
    d_clock -= t.d_clock;
    return *this;
  }

  friend bool operator==(const DebugTime& t1, const DebugTime& t2);
  friend bool operator!=(const DebugTime& t1, const DebugTime& t2);

  friend bool operator<(const DebugTime& t1, const DebugTime& t2);
  friend bool operator>(const DebugTime& t1, const DebugTime& t2);
  friend bool operator<=(const DebugTime& t1, const DebugTime& t2);
  friend bool operator>=(const DebugTime& t1, const DebugTime& t2);

  friend ostream& operator<<(ostream& os, const DebugTime& t);
};

DebugTime operator+(const DebugTime& t1, const DebugTime& t2) {
  DebugTime res(t1);
  res += t2;
  return res;
}
DebugTime operator-(const DebugTime& t1, const DebugTime& t2) {
  DebugTime res(t1);
  res -= t2;
  return res;
}

bool operator==(const DebugTime& t1, const DebugTime& t2) {
  return t1.d_clock == t2.d_clock;
}

bool operator!=(const DebugTime& t1, const DebugTime& t2) {
  return !(t1 == t2);
}

bool operator<(const DebugTime& t1, const DebugTime& t2) {
  return t1.d_clock < t2.d_clock;
}

bool operator>(const DebugTime& t1, const DebugTime& t2) {
  return t1.d_clock > t2.d_clock;
}

bool operator<=(const DebugTime& t1, const DebugTime& t2) {
  return t1.d_clock <= t2.d_clock;
}

bool operator>=(const DebugTime& t1, const DebugTime& t2) {
  return t1.d_clock >= t2.d_clock;
}

////////////////////////////////////////////////////////////////////////
// Class DebugTimer
////////////////////////////////////////////////////////////////////////

// Destructor
DebugTimer::~DebugTimer() {
  if(d_clean_time)
    delete d_time;
}

void Debug::init(const std::vector<std::pair<std::string,bool> >* traceOptions,
                 const std::string* dumpName)
{
  d_traceOptions = traceOptions;
  d_dumpName = dumpName;
}

void Debug::finalize()
{
  d_traceOptions = NULL;
  d_dumpName = NULL;
}

DebugFlag
Debug::traceFlag(const char* name) { return traceFlag(std::string(name)); }

void
Debug::traceAll(bool enable) { traceFlag("ALL") = enable; }

// Copy constructor: copy the *pointer* from public timers, and
// value from private.  The reason is, when you modify a public
// timer, you want the changes to show in the central database and
// everywhere else, whereas private timers are used as independent
// temporary variables holding intermediate time values.
DebugTimer::DebugTimer(const DebugTimer& timer) {
  d_clean_time = timer.d_clean_time;
  if(d_clean_time) {
    // We are copying a private timer; make our own copy
    d_time = new DebugTime(*timer.d_time);
    d_clean_time = true;
  } else {
    // This is a public timer; just grab the pointer
    d_time = timer.d_time;
  }
}
// Assignment: same logistics as for the copy constructor, but need
// to take care of our own pointer
DebugTimer& DebugTimer::operator=(const DebugTimer& timer) {
  // Check for self-assignment
  if(&timer == this) return *this;

  if(timer.d_clean_time) {
    // We are copying a private timer
    if(d_clean_time) // We already have a private pointer, reuse it
      *d_time = *timer.d_time;
    else { // Create a new storage
      d_time = new DebugTime(*timer.d_time);
      d_clean_time = true;
    }
  } else {
    // This is a public timer
    if(d_clean_time) // We own our pointer, clean it up first
      delete d_time;
    d_time = timer.d_time;
    d_clean_time = false;
  }
  return *this;
}

void DebugTimer::reset() {
  d_time->reset();
}

DebugTimer& DebugTimer::operator+=(const DebugTimer& timer) {
  (*d_time) += *(timer.d_time);
  return *this;
}

DebugTimer& DebugTimer::operator-=(const DebugTimer& timer) {
  (*d_time) -= *(timer.d_time);
  return *this;
}

// These will produce new "private" timers
DebugTimer DebugTimer::operator+(const DebugTimer& timer) {
  return DebugTimer(new DebugTime((*d_time) + (*timer.d_time)),
		    true /* take the new DebugTime */);
}

DebugTimer DebugTimer::operator-(const DebugTimer& timer) {
  return DebugTimer(new DebugTime((*d_time) - (*timer.d_time)),
		    true /* take the new DebugTime */);
}

// Comparisons
bool operator==(const DebugTimer& t1, const DebugTimer& t2) {
  return(*t1.d_time == *t2.d_time);
}
bool operator!=(const DebugTimer& t1, const DebugTimer& t2) {
  return(*t1.d_time != *t2.d_time);
}
bool operator<(const DebugTimer& t1, const DebugTimer& t2) {
  return *t1.d_time < *t2.d_time;
}
bool operator>(const DebugTimer& t1, const DebugTimer& t2) {
  return *t1.d_time > *t2.d_time;
}
bool operator<=(const DebugTimer& t1, const DebugTimer& t2) {
  return *t1.d_time <= *t2.d_time;
}
bool operator>=(const DebugTimer& t1, const DebugTimer& t2) {
  return *t1.d_time >= *t2.d_time;
}

// Print the time and timer's values
ostream& operator<<(ostream& os, const DebugTime& t) {
  int seconds = (int)(t.d_clock / CLOCKS_PER_SEC);
  int milliseconds = 1000 * int((((double)(t.d_clock % CLOCKS_PER_SEC)) / CLOCKS_PER_SEC));
  os << seconds << "." << setfill('0') << setw(6) << milliseconds;
  return os;
}
ostream& operator<<(ostream& os, const DebugTimer& timer) {
  return(os << *timer.d_time);
}

////////////////////////////////////////////////////////////////////////
// Class Debug
////////////////////////////////////////////////////////////////////////

// Destructor: destroy all the pointers in d_timers
Debug::~Debug() {
  TimerMap::iterator i, iend;
  for(i = d_timers.begin(), iend = d_timers.end(); i != iend; ++i)
    delete (*i).second;
  if(d_osDumpTrace != NULL)
    delete d_osDumpTrace;
}

bool
Debug::trace(const string& name) {
  // First, check if this flag was set in the command line.  Walk the
  // vector backwards, so that the last +/-trace takes effect.
  if(d_traceOptions != NULL) {
    vector<pair<string,bool> >::const_reverse_iterator i, iend;
    for(i=d_traceOptions->rbegin(), iend=d_traceOptions->rend(); i!=iend; ++i)
      if((*i).first == name || (*i).first == "ALL") return (*i).second;
  }
  return traceFlag(name) || traceFlag("ALL");
}


DebugTimer Debug::timer(const string& name) {
  // See if we already have the timer
  if(d_timers.count(name) > 0) return(DebugTimer(d_timers[name]));
  else {
    // Create a new timer
    DebugTime *t = new DebugTime();
    d_timers[name] = t;
    return DebugTimer(t);
  }
}

DebugTimer Debug::newTimer() {
  return DebugTimer(new DebugTime(), true /* take the pointer */);
}

void Debug::setCurrentTime(DebugTimer& timer) {
  *timer.d_time = clock();
}

// Set the timer to the difference between current time and the
// time stored in the timer: timer = currentTime - timer.
// Intended to obtain the time interval since the last call to
// setCurrentTime() with that timer.
void Debug::setElapsed(DebugTimer& timer) {
  *timer.d_time -= DebugTime(clock());
}

/*! If the stream is not initialized, open the file
 * If the filename is empty or "-", then return
 * cout (but do not initialize the stream in this case).
 */

ostream& Debug::getOSDumpTrace() {
  if(d_osDumpTrace != NULL) return *d_osDumpTrace;
  // Check if the flag has a file name in it
  if(*d_dumpName == "" || *d_dumpName == "-") return cout;
  d_osDumpTrace = new ofstream(d_dumpName->c_str());
  return *d_osDumpTrace;
}


// Print an entry to the dump-sat file: free-form message
void Debug::dumpTrace(const std::string& title,
		      const std::vector<std::pair<std::string,std::string> >& fields) {
  ostream& os = getOSDumpTrace();
  os << "[" << title << "]\n";
  for(size_t i=0, iend=fields.size(); i<iend; ++i)
    os << fields[i].first << " = " << fields[i].second << "\n";
  os << endl;
}


// Print all the collected data if "DEBUG" flag is set
void Debug::printAll(ostream& os) {
  if(!trace("DEBUG")) return;
  // Flags
  os << endl
     << "********************************" << endl
     << "******* Debugging Info *********" << endl
     << "********************************" << endl;

  if(d_flags.size() > 0) {
    os << endl << "************ Flags *************" << endl << endl;
    for(FlagMap::iterator
	  i = d_flags.begin(), iend = d_flags.end(); i != iend; ++i)
      os << (*i).first << " = " << (*i).second << endl;
  }

  if(d_counters.size() > 0) {
    os << endl << "*********** Counters ***********" << endl << endl;
    for(CounterMap::iterator
	  i = d_counters.begin(), iend = d_counters.end(); i != iend; ++i)
      os << (*i).first << " = " << (*i).second << endl;
  }

  if(d_timers.size() > 0) {
    os << endl << "************ Timers ************" << endl << endl;
    for(TimerMap::iterator
	  i = d_timers.begin(), iend = d_timers.end(); i != iend; ++i)
      os << (*i).first << " = " << *((*i).second) << endl;
  }

  os << endl
     << "********************************" << endl
     << "**** End of Debugging Info *****" << endl
     << "********************************" << endl;
}

// Global debugger.  It must be initialized in main() through its
// init() method.
CVC_DLL Debug debugger;

} // end of namespace CVC3

#endif
