/*****************************************************************************/
/*!
 * \file decision_engine_caching.h
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

#ifndef _cvc3__search__decision_engine_caching_h_
#define _cvc3__search__decision_engine_caching_h_

#include "decision_engine.h"

namespace CVC3 {

class DecisionEngineCaching : public DecisionEngine {

  class CacheEntry
  {
  public:
    Expr d_expr;
    int d_rank;
    int d_trust;

    CacheEntry() : d_rank(0), d_trust(0) {}
  };

  int d_startLevel;
  int d_bottomLevel;
  int d_topLevel;
  bool d_topLevelLock;
  int d_height;

  std::vector<CacheEntry> d_cache;
  ExprMap<int> d_index;

protected:
  virtual bool isBetter(const Expr& e1, const Expr& e2);

public:
  DecisionEngineCaching(TheoryCore* core, SearchImplBase* se);
  virtual ~DecisionEngineCaching() { }

  virtual Expr findSplitter(const Expr& e);
  virtual void goalSatisfied();
};

}

#endif
