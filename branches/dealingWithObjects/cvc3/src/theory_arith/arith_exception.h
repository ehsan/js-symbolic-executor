/*****************************************************************************/
/*!
 * \file arith_exception.h
 * \brief An exception thrown by the arithmetic decision procedure.
 * 
 * Author: Sergey Berezin
 * 
 * Created: Fri May 23 15:42:21 2003
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

#ifndef _cvc3__theory_arith__arith_exception_h_
#define _cvc3__theory_arith__arith_exception_h_

#include <string>
#include <iostream>
#include "exception.h"

namespace CVC3 {

  class ArithException: public Exception {
//  protected:
//    std::string d_msg;
  public:
    // Constructors
    ArithException() { }
    ArithException(const std::string& msg): Exception(msg) { }
    ArithException(const char* msg): Exception(msg) { }
    // Destructor
    virtual ~ArithException() { }
    virtual std::string toString() const {
      return "Arithmetic error: " + d_msg;
    }
  }; // end of class ArithException
} // end of namespace CVC3 

#endif
