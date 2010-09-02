/*****************************************************************************/
/*!
 * \file theorem_manager.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 11 02:39:35 GMT 2003
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
// File: theorem_manager.cpp
//
// AUTHOR: Sergey Berezin, 07/05/02
//
// Defines some functions for class TheoremManager.  They are not
// inlined becaule they use ExprManager (expr_manager.h), which
// includes theorem_manager.h.
// 
///////////////////////////////////////////////////////////////////////////////


#include "theorem_value.h"
#include "memory_manager_chunks.h"
#include "memory_manager_malloc.h"
#include "command_line_flags.h"
#include "common_proof_rules.h"


using namespace std;
using namespace CVC3;


// ExprManager is not initialized in vcl yet when we are created; we
// use d_em as our local cache to fetch the EM when our getEM() is
// first called.

TheoremManager::TheoremManager(ContextManager* cm,
                               ExprManager* em,
                               const CLFlags& flags)
  : d_cm(cm), d_em(em), d_flags(flags),
    d_withProof(flags["proofs"].getBool()),
    d_withAssump(true), d_flag(1),
    d_active(true)
{
  d_em->newKind(PF_APPLY, "|-");
  d_em->newKind(PF_HOLE, "**");
  DebugAssert(!d_withProof || d_withAssump, 
	      "TheoremManager(): proofs without assumptions are not allowed");
  if (flags["mm"].getString() == "chunks") {
    d_mm = new MemoryManagerChunks(sizeof(RegTheoremValue));
    d_rwmm = new MemoryManagerChunks(sizeof(RWTheoremValue));
  } else {
    d_mm = new MemoryManagerMalloc();
    d_rwmm = new MemoryManagerMalloc();
  }
  d_rules = createProofRules();
}


TheoremManager::~TheoremManager()
{
  delete d_mm;
  delete d_rwmm;
}


void TheoremManager::clear() {
  delete d_rules;
  d_active=false;
}
