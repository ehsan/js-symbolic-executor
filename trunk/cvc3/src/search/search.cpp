/*****************************************************************************/
/*!
 * \file search.cpp
 *
 * Author: Clark Barrett, Vijay Ganesh (CNF Converter)
 *
 * Created: Fri Jan 17 14:19:54 2003
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


#include "search.h"
#include "search_rules.h"
#include "theory_core.h"
#include "eval_exception.h"
#include "theorem_manager.h"
#include "command_line_flags.h"


using namespace CVC3;
using namespace std;


//! Constructor
SearchEngine::SearchEngine(TheoryCore* core)
  : d_core(core),
    d_commonRules(core->getTM()->getRules())
{

  const CLFlags& flg  = (core->getTM()->getFlags());
  if (flg["lfsc-mode"].getInt()!= 0){
    d_rules = createRules(this);

  }
  else
    d_rules = createRules();

}


//! Destructor
SearchEngine::~SearchEngine()
{
  delete d_rules;
}

bool SearchEngine::tryModelGeneration(Theorem& thm) {

	if(!lastThm().isNull()) throw EvalException("Method tryModelGenereation() (or command COUNTERMODEL)\n must be called only after failed QUERY");

	// Save the scope level, to recover on errors
	push();
	d_core->collectBasicVars();
	bool success = d_core->refineCounterExample(thm);
	if (!success) {
		pop();
		return false;
	}

	QueryResult qres = checkValid(d_core->falseExpr(), thm);
	if(qres == VALID) {
		pop();
		return false;
	}

	success = d_core->buildModel(thm);
	if (!success) {
	    pop();
	    return false;
	}

	qres = checkValid(d_core->falseExpr(), thm);
	if(qres == VALID) {
	    pop();
	    return false;
	}

	return true;
}

void SearchEngine::getConcreteModel(ExprMap<Expr>& m)
{
  TRACE("model" ,  "Building a concrete model", "", "{");
  if(!lastThm().isNull())
    throw EvalException
      ("Method getConcreteModel() (or command COUNTERMODEL)\n"
       " must be called only after failed QUERY");
  // Save the scope level, to recover on errors
  push();
  d_core->collectBasicVars();
  try {
    d_core->refineCounterExample();
  } catch(Exception& e) {
    // Clean up and re-throw the exception
    pop();
    throw e;
  }
  Theorem thm;
  QueryResult qres = checkValid(d_core->falseExpr(), thm);
  if(qres == VALID) {
    vector<Expr> assump;
    getAssumptions(assump);
    d_core->inconsistentThm().getLeafAssumptions(assump);
    Expr a = Expr(RAW_LIST, assump, d_core->getEM());
    pop();
    throw Exception
      ("Model Creation failed after refining counterexample\n"
       "due to the following assumptions:\n "
       +a.toString()
       +"\n\nYou might be using an incomplete fragment of the theory");
  }
//   else if (qres != INVALID) {
//     throw EvalException
//       ("Unable to build concrete model");
//   }
  try {
    d_core->buildModel(m);
  } catch(Exception& e) {
    // Clean up and re-throw the exception
    pop();
    throw e;
  }
  qres = checkValid(d_core->falseExpr(), thm);
  if(qres == VALID) {
    vector<Expr> assump;
    getAssumptions(assump);
    Expr a = Expr(RAW_LIST, assump, d_core->getEM());
    pop();
    throw Exception
      ("Model Creation failed due to the following assumptions:\n"
       +a.toString()
       +"\n\nYou might be using an incomplete fragment of the theory");
  }
//   else if (qres != INVALID) {
//     throw EvalException
//       ("Unable to build concrete model");
//   }
  TRACE("model" ,  "Building a concrete model", "", "}");
}
