/*****************************************************************************/
/*!
 * \file lang.h
 * \brief Definition of input and output languages to CVC3
 * 
 * Author: Mehul Trivedi
 * 
 * Created: Thu Jul 29 11:56:34 2004
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

#ifndef _cvc3__lang_h_
#define _cvc3__lang_h_

#include "debug.h"

namespace CVC3 {

  //! Different input languages
  typedef enum {
    //! Nice SAL-like language for manually written specs
    PRESENTATION_LANG,
    //! SMT-LIB format
    SMTLIB_LANG,
    //! Lisp-like format for automatically generated specs
    LISP_LANG,

    AST_LANG,	
    /* @brief AST is only for printing the Expr abstract syntax tree in lisp
       format; there is no such input language <em>per se</em> */

    //! for output into Simplify format
    SIMPLIFY_LANG,
    
    //! for output in TPTP format
    TPTP_LANG,
    
    //! for output in SPASS format
    SPASS_LANG,

    //! SMT-LIB v2 format
    SMTLIB_V2_LANG

  } InputLanguage;
  
  inline bool isPrefix(const std::string& prefix,
                       const std::string& str) {
    return str.rfind( prefix, 0 ) == 0;
  }

  inline InputLanguage getLanguage(const std::string& lang) {
    if (lang.size() > 0) {
      if(isPrefix(lang,"presentation")) {
        return PRESENTATION_LANG;
      }
      if(isPrefix(lang, "lisp")) {
        return LISP_LANG;
      }
      if(isPrefix(lang,"ast")) {
        return AST_LANG;
      }
      if(isPrefix(lang,"tptp")) {
        return TPTP_LANG;
      }
      /* Languages starting with 's' must have at least 2 letters,
         since there's more than one of them. */
      if(lang.size() > 1) {
        if(isPrefix(lang,"simplify")) {
          return SIMPLIFY_LANG;
        } 
        if(isPrefix(lang,"spass")) {
          return SPASS_LANG;
	} 
        if (lang[ lang.length() - 1 ] == '2' &&
            isPrefix(lang.substr(0,lang.length()-1),"smtlib")) { 
          return SMTLIB_V2_LANG;
	}
        if(isPrefix(lang,"smtlib")) {
          return SMTLIB_LANG;
        }
      }
      
    }

    throw Exception("Bad input language specified");
    return AST_LANG;
  }

} // end of namespace CVC3

#endif
