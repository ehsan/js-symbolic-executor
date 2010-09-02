/*****************************************************************************/
/*!
 * \file bitvector_exception.h
 * \brief An exception thrown by the bitvector decision procedure.
 * 
 * Author: Vijay Ganesh
 * 
 * Created: Wed May  5 16:23:45 PST 2004
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

#ifndef _cvc3__theory_bitvector__bitvector_exception_h_
#define _cvc3__theory_bitvector__bitvector_exception_h_

#include <string>
#include <iostream>
#include "exception.h"

namespace CVC3 {

  class BitvectorException: public Exception {
//  protected:
//    std::string d_msg;
  public:
    // Constructors
    BitvectorException() { }
    BitvectorException(const std::string& msg): Exception(msg) { }
    BitvectorException(char* msg): Exception(msg) { }
    // Destructor
    virtual ~BitvectorException() { }
    virtual std::string toString() const {
      return "Bitvector error: " + d_msg;
    }
  }; // end of class BitvectorException
} // end of namespace CVC3 

#endif
