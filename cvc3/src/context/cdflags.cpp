/*****************************************************************************/
/*!
 *\file cdflags.cpp
 *\brief Implementation for CDFlags class
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan 26 16:53:28 2006
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


#include "cdflags.h"
#include "memory_manager_context.h"


using namespace CVC3;
using namespace std;


void CDFlags::update(unsigned mask, int scope, bool setMask)
{
  DebugAssert(mask && (mask & (mask-1)) == 0, "Expected single bit mask");
  if (scope < 0 || d_scope->level() <= scope) {
    makeCurrent(scope);
    if (setMask) d_flags = d_flags | mask;
    else d_flags = d_flags & ~mask;
  }
  else {
    // Kind of ugly: have to "change the past", but that's the price we pay for
    // keeping all the flags in one word for efficiency.
    IF_DEBUG(bool on = (d_flags & mask) != 0;)

    // Update current object
    if (setMask) d_flags = d_flags | mask;
    else d_flags = d_flags & ~mask;

    ContextObjChain** lastPtr = &d_restore;
    CDFlags* pastFlags;
    Scope* lastScope = d_scope;
    bool done = false;

    // Update past objects
    while (true) {
      pastFlags = (CDFlags*)((*lastPtr)->d_data);
      DebugAssert(pastFlags != NULL, "expected non-NULL data");
      if (pastFlags->d_scope->level() >= scope) {
        DebugAssert((on && (pastFlags->d_flags & mask))
        		 || (!on && !(pastFlags->d_flags & mask)),
                    "Expected no change in flag since scope");
        if (setMask) {
          pastFlags->d_flags = pastFlags->d_flags | mask;
        }
        else {
          pastFlags->d_flags = pastFlags->d_flags & ~mask;
        }
        if (pastFlags->d_scope->level() == scope) {
          done = true; break;
        }
        lastScope = pastFlags->d_scope;
      } else break;
      lastPtr = &((*lastPtr)->d_restore);
      DebugAssert(*lastPtr != NULL, "Should always be object at scope 0");
    }
    if (done) return;

    // No past object exists at the target scope: create one
    DebugAssert(lastScope != NULL &&
                lastScope->level() > scope,
                "Expected lastScope to be above target scope");
    while (lastScope->level() > scope) lastScope = lastScope->prevScope();

    ContextObj* data = pastFlags->makeCopy(lastScope->getCMM());

    pastFlags->d_scope = lastScope;

    ContextObjChain* obj = new(lastScope->getCMM())
      ContextObjChain(data, this, (*lastPtr)->d_restore);
    (*lastPtr)->d_restore = obj;
    lastScope->addToChain(obj);

    // Update newly created past object
    if (setMask) {
      pastFlags->d_flags = pastFlags->d_flags | mask;
    }
    else {
      pastFlags->d_flags = pastFlags->d_flags & ~mask;
    }
  }
}
