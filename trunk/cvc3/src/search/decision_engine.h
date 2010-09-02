/*****************************************************************************/
/*!
 * \file decision_engine.h
 * 
 * Author: Clark Barrett
 * 
 * Created: Fri Jul 11 13:04:25 2003
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

#ifndef _cvc3__search__decision_engine_h_
#define _cvc3__search__decision_engine_h_

#include "statistics.h"
#include "search_fast.h"

namespace CVC3 {

class DecisionEngine {

  /***************************************************************************/
  /*!
   *\defgroup DE Decision Engine
   *\brief Decision Engine, used by Search Engine
   *\ingroup SE
   *@{
   */
  /***************************************************************************/

protected:
  TheoryCore* d_core; //!< Pointer to core theory
  SearchImplBase* d_se; //!< Pointer to search engine

  //! List of currently active splitters
  CDList<Expr> d_splitters;

  //! Total number of splitters
  StatCounter d_splitterCount;

  ExprMap<Expr> d_bestByExpr;

  //! Visited cache for findSplitterRec traversal.  
  /*! Must be emptied in every findSplitter() call. */
  ExprMap<Expr> d_visited;

  Expr findSplitterRec(const Expr& e);
  virtual bool isBetter(const Expr& e1, const Expr& e2) = 0;

public:
  DecisionEngine(TheoryCore* core, SearchImplBase* se);
  virtual ~DecisionEngine() { }

  /*! @brief Finds a splitter inside a non const expression.
      The expression passed in must not be a boolean constant,
      otherwise a DebugAssert will occur.  \return Null Expr if passed
      in a Null Expr. */
  virtual Expr findSplitter(const Expr& e) = 0;

  //! Push context and record the splitter
  void pushDecision(Expr splitter, bool whichCase=true);
  //! Pop last decision (and context)
  void popDecision();
  //! Pop to given scope
  void popTo(int dl);

  //! Return the last known splitter.
  Expr lastSplitter();

  //! Search should call this when it derives 'false'
  virtual void goalSatisfied() = 0;

  /*@}*/ // End of DE group

};

}

#endif
