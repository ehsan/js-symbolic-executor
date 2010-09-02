/*****************************************************************************/
/*!
 * \file decision_engine_dfs.cpp
 * \brief Decision Engine
 * 
 * Author: Clark Barrett
 * 
 * Created: Sun Jul 13 22:44:55 2003
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


#include "decision_engine_dfs.h"
#include "theory_core.h"
#include "search.h"


using namespace std;
using namespace CVC3;


bool DecisionEngineDFS::isBetter(const Expr& e1, const Expr& e2)
{
  return false;
}


/*****************************************************************************/
/*!
 * Function: DecisionEngineDFS::DecisionEngineDFS
 *
 * Author: Clark Barrett
 *
 * Created: Sun Jul 13 22:52:51 2003
 *
 * Constructor
 */
/*****************************************************************************/
DecisionEngineDFS::DecisionEngineDFS(TheoryCore* core, SearchImplBase* se)
  : DecisionEngine(core, se)
{
}


/*****************************************************************************/
/*!
 * Function: DecisionEngineDFS::findSplitter
 *
 * Author: Clark Barrett
 *
 * Created: Sun Jul 13 22:53:18 2003
 *
 * Main function to choose the next splitter.
 * \return NULL if all known splitters are assigned.
 */
/*****************************************************************************/
Expr DecisionEngineDFS::findSplitter(const Expr& e) {
  TRACE("splitters verbose", "findSplitter(", e, ") {");
  Expr splitter; // Null by default
  d_visited.clear();

  if (!e.isNull()) {
    splitter = findSplitterRec(e);
    // It's OK not to find a splitter, since e may contain only "bad"
    // splitters, according to d_se->isGoodSplitter(e)

//     DebugAssert(!splitter.isNull(),
// 		"findSplitter: can't find splitter in non-literal: "
// 		+ e.toString());
    IF_DEBUG(if(!splitter.isNull())
	     debugger.counter("splitters from decision engine")++;)
  }
  TRACE("splitters verbose", "findSplitter => ", splitter, " }");
  return splitter;
}


void DecisionEngineDFS::goalSatisfied()
{
}
