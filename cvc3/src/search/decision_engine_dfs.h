/*****************************************************************************/
/*!
 * \file decision_engine_dfs.h
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

#ifndef _cvc3__search__decision_engine_dfs_h_
#define _cvc3__search__decision_engine_dfs_h_

#include "decision_engine.h"

namespace CVC3 {

/*****************************************************************************/
/*!
 *\anchor de_dfs
 *\class DecisionEngineDFS
 *\brief Decision Engine for use with the Search Engine
 *\ingroup DE
 *
 * Author: Clark Barrett
 *
 * Created: Fri Jul 11 16:34:22 2003
 *
 */
/*****************************************************************************/
class DecisionEngineDFS : public DecisionEngine {

protected:
  virtual bool isBetter(const Expr& e1, const Expr& e2);

public:
  //! Constructor
  DecisionEngineDFS(TheoryCore* core, SearchImplBase* se);
  virtual ~DecisionEngineDFS() { }

  /*! @brief Find the next splitter.  \return Null Expr if no
    splitter is found. */
  virtual Expr findSplitter(const Expr& e);

  //! Search should call this when it derives 'false'
  virtual void goalSatisfied();

};

}

#endif
