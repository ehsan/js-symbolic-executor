/*****************************************************************************/
/*!
 * \file statistics.cpp
 * \brief Description: Implementation of Statistics class
 * 
 * Author: Sergey Berezin
 * 
 * Created: Thu Jun  5 17:49:01 2003
 *
 * <hr>
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/

#include "statistics.h"

using namespace std;

namespace CVC3 {
  
////////////////////////////////////////////////////////////////////////
// Class Statistics
////////////////////////////////////////////////////////////////////////

// Print all the collected data
ostream& Statistics::printAll(ostream& os) const {
  // Flags
  os << endl
     << "********************************" << endl
     << "********* Statistics ***********" << endl
     << "********************************" << endl;

  StatFlagMap::const_iterator i = d_flags.begin(), iend = d_flags.end();
  if(i!=iend) {
    os << endl << "************ Flags *************" << endl << endl;
    for(; i != iend; ++i)
      os << (*i).first << " = " << (*i).second << endl;
  }
  StatCounterMap::const_iterator 
    j = d_counters.begin(), jend = d_counters.end();
  if(j!=jend) {
    os << endl << "*********** Counters ***********" << endl << endl;
    for(; j != jend; ++j)
      os << (*j).first << " = " << (*j).second << endl;
  }
  os << endl
     << "********************************" << endl
     << "****** End of Statistics *******" << endl
     << "********************************" << endl;
  return os;
}

} // end of namespace CVC3

