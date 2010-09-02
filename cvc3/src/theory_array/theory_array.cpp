/*****************************************************************************/
/*!
 * \file theory_array.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Thu Feb 27 00:38:55 2003
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


#include "theory_array.h"
#include "theory_bitvector.h"
#include "array_proof_rules.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "translator.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryArray Public Methods                                                //
///////////////////////////////////////////////////////////////////////////////


TheoryArray::TheoryArray(TheoryCore* core)
  : Theory(core, "Arrays"), d_reads(core->getCM()->getCurrentContext()),
    d_applicationsInModel(core->getFlags()["applications"].getBool()),
    d_liftReadIte(core->getFlags()["liftReadIte"].getBool()),
    d_sharedSubterms(core->getCM()->getCurrentContext()),
    d_sharedSubtermsList(core->getCM()->getCurrentContext()),
    d_index(core->getCM()->getCurrentContext(), 0, 0),
    d_sharedIdx1(core->getCM()->getCurrentContext(), 0, 0),
    d_sharedIdx2(core->getCM()->getCurrentContext(), 0, 0),
    d_inCheckSat(0)
{
  d_rules = createProofRules();

  // Register new local kinds with ExprManager
  getEM()->newKind(ARRAY, "_ARRAY", true);
  getEM()->newKind(READ, "_READ");
  getEM()->newKind(WRITE, "_WRITE");
  getEM()->newKind(ARRAY_LITERAL, "_ARRAY_LITERAL");

  vector<int> kinds;
  kinds.push_back(ARRAY);
  kinds.push_back(READ);
  kinds.push_back(WRITE);

  kinds.push_back(ARRAY_LITERAL);

  registerTheory(this, kinds);
}


// Destructor: delete the proof rules class if it's present
TheoryArray::~TheoryArray() {
  if(d_rules != NULL) delete d_rules;
}


void TheoryArray::addSharedTerm(const Expr& e)
{
  if (d_sharedSubterms.count(e) > 0) return;

  TRACE("arrAddSharedTerm", "TheoryArray::addSharedTerm(", e.toString(), ")");

  // Cache all shared terms
  d_sharedSubterms[e]=e;

  // Make sure we get notified if shared term is assigned to something else
  // We need this because we only check non-array-normalized (nan) shared terms,
  // so if a variable gets set to a nan term, we will need to know about it.
  e.addToNotify(this, Expr());

  if (isWrite(e) || (isRead(e) && isWrite(e[0]))) {

    // Children of shared terms better be shared so we can detect any failure of normalization
    for (int i = 0; i < e.arity(); ++i) addSharedTerm(e[i]);

    // Only check writes that are not normalized
    if (!isWrite(e) || e.notArrayNormalized()) {
      // Put in list to check during checkSat
      d_sharedSubtermsList.push_back(e);
    }
  }
}


void TheoryArray::assertFact(const Theorem& e)
{
  const Expr& expr = e.getExpr();
  TRACE("arrAssertFact", "TheoryArray::assertFact(", e.getExpr().toString(), ")");

  switch (expr.getOpKind()) {

    case NOT:
      DebugAssert(expr[0].isEq(), "Unexpected negation");

      if (isArray(getBaseType(expr[0][0]))) {
        // For disequalities between arrays, do the polite thing, and introduce witnesses
        enqueueFact(d_rules->arrayNotEq(e));
        break;
      }

      // We can use the shared term mechanism here:
      // In checksat we will ensure that all shared terms are in a normal form
      // so if two are known to be equal, we will discover it
      addSharedTerm(expr[0][0]);
      addSharedTerm(expr[0][1]);
      
      break;
      
    case EQ:
      DebugAssert(theoryCore()->inUpdate() ||
                  (d_inCheckSat > 0) ||
                  !isWrite(expr[0]), "Invariant violated");
      break;

    default:
      FatalAssert(false, "Unexpected case");
      break;
  }
}


Expr findAtom(Expr e) {
  DebugAssert(e.arity() != 0, "Invariant Violated");
  int i;
  for (i = 0; i < e.arity(); ++i) {
    if (!e[i].isAtomic()) break;
  }
  if (e[i].isAbsAtomicFormula()) return e[i];
  return findAtom(e[i]);
}


void TheoryArray::checkSat(bool fullEffort)
{
  if (fullEffort == true) {
    // Check that all non-array-normalized shared terms are normalized
    Theorem thm;
    for (; d_index < d_sharedSubtermsList.size(); d_index = d_index + 1) {
      Expr e = d_sharedSubtermsList[d_index];

      if (isRead(e)) {
        DebugAssert(isWrite(e[0]), "Expected read(write)");

        // This should be a signature without a find
        DebugAssert(!e.hasFind(), "Expected no find");

        // If this is no longer a valid signature, we can skip it
        if (!e.hasRep()) continue;

        // Check to see if we know whether indices are equal
        Expr ieq = e[0][1].eqExpr(e[1]);
        Theorem ieqSimp = simplify(ieq);
        if (!ieqSimp.getRHS().isBoolConst()) {
          // if not, split on equality of indices
          // TODO: really tricky optimization: maybe we can avoid this split
          // if both then and else are unknown terms?
          addSplitter(ieq);
          return;
        }

        // Get the representative for the signature
        Theorem repEqSig = e.getRep();
        DebugAssert(!repEqSig.isRefl(), "Expected non-self rep");

        // Apply the read over write rule
	thm = d_rules->rewriteReadWrite(e);

        // Carefully simplify
        thm = transitivityRule(thm, 
                               substitutivityRule(thm.getRHS(), 0, ieqSimp));
        thm = transitivityRule(thm, rewriteIte(thm.getRHS()));

        // Derive the new equality and simplify
        thm = transitivityRule(repEqSig, thm);
        thm = iffMP(thm, simplify(thm.getExpr()));
        Expr newExpr = thm.getExpr();
        if (newExpr.isTrue()) {
          // Fact is already known, continue
          continue;
        }
        else if (newExpr.isAbsAtomicFormula()) {
          enqueueFact(thm);
        }
        else {
          // expr is not atomic formula, so pick a splitter that will help make it atomic
          addSplitter(findAtom(newExpr));
        }
        return;
      }

      // OK, everything else should be a write
      DebugAssert(isWrite(e), "Expected Write");
      DebugAssert(e.notArrayNormalized(),
                  "Only non-normalized writes expected");

      // If write is not its own find, this means that the write
      // was normalized to something else already, so it's not relevant
      // any more
      if (find(e).getRHS() != e) continue;

      // First check for violation of redundantWrite1
      Expr store = e[0];
      while (isWrite(store)) store = store[0];
      DebugAssert(findExpr(e[2]) == e[2], "Expected own find");
      thm = simplify(Expr(READ, store, e[1]));
      if (thm.getRHS() == e[2]) {
        thm = d_rules->rewriteRedundantWrite1(thm, e);
      }

      // Then check for violation of redundantWrite2
      else if (isWrite(e[0]) && e[0][1] > e[1]) {
        thm = d_rules->interchangeIndices(e);
      }

      else {
        FatalAssert(false, "Unexpected expr");
        continue;
      }

      // Write needs to be normalized, see what its new normal form is:
      thm = transitivityRule(thm, simplify(thm.getRHS()));
      Expr newExpr = thm.getRHS();

      if (newExpr.isAtomic()) {
        // If the new normal form is atomic, go ahead and update the normal form directly
        ++d_inCheckSat;
        assertEqualities(thm);
        // To ensure updates are processed and checkSat gets called again
        enqueueFact(thm);
        --d_inCheckSat;
      }
      else {
        // normal form is not atomic, so pick a splitter that will help make it atomic
        addSplitter(findAtom(newExpr));
      }
      return;
    }

    // All the terms should be normalized now... Ok, lets split on the read
    // indices.
    TRACE("sharing", "checking shared terms, size = ", int2string(d_reads.size()), "");
    // Collect all the arrays and indices of interest
    ExprMap< hash_set<Expr> > reads_by_array;
    ExprMap< hash_set<Expr> > const_reads_by_array;
    for (unsigned i = 0; i < d_reads.size(); ++i) {
      Expr read = d_reads[i];
      if (read.getSig().isNull()) continue;
      if( d_sharedSubterms.find(read[1]) == d_sharedSubterms.end() ) continue;
      Expr read_array = getBaseArray(read[0]);
      if (read[1].getKind() != BVCONST) {
        hash_set<Expr>& reads = reads_by_array[read_array];
        reads.insert(read);
      } else {
        hash_set<Expr>& reads = const_reads_by_array[read_array];
        reads.insert(read);
      }
    }

    ExprMap< hash_set<Expr> >::iterator it = reads_by_array.begin();
    ExprMap< hash_set<Expr> >::iterator it_end = reads_by_array.end();
    for(; it != it_end; ++ it) {
      Expr array = it->first;
      hash_set<Expr>& reads_single_array = it->second;

      hash_set<Expr>::iterator read1_it = reads_single_array.begin();
      hash_set<Expr>::iterator read1_end = reads_single_array.end();
      for (; read1_it != read1_end; ++ read1_it) {
        Expr read1 = (*read1_it);
        Expr x_k = read1[1];
        Expr read1_find = find(read1).getRHS();
        // The non-const reads arrays
        hash_set<Expr>::iterator read2_it = reads_single_array.begin();
        for (; read2_it != read1_it; ++ read2_it) {
          Expr read2 = (*read2_it);
          Expr read2_find = find(read2).getRHS();
          if (read1_find != read2_find) {
            Theorem simpl = simplify(read1.eqExpr(read2));
            Expr y_k = read2[1];
            Expr eq = x_k.eqExpr(y_k);
            if( !simplify(eq).getRHS().isBoolConst() ) {
              if (simpl.getRHS().isFalse()) {
                enqueueFact(d_rules->propagateIndexDiseq(simpl));
              } else {
                TRACE("sharing", "from " + read2.toString(), "with find = ", find(read2).getRHS());
                TRACE("sharing", "from " + read1.toString(), "with find = ", find(read1).getRHS());
                TRACE("sharing", "splitting " + y_k.toString(), " and ", x_k.toString());
                addSplitter(eq);
              }
            }
          }
        }
        // The const reads arrays
        hash_set<Expr>& const_reads_single_array = const_reads_by_array[array];
        read2_it = const_reads_single_array.begin();
        hash_set<Expr>::iterator read2_it_end = const_reads_single_array.end();
        for (; read2_it != read2_it_end; ++ read2_it) {
          Expr read2 = (*read2_it);
          Expr read2_find = find(read2).getRHS();
          if (read1_find != read2_find) {
            Theorem simpl = simplify(read1.eqExpr(read2));
            Expr y_k = read2[1];
            Expr eq = x_k.eqExpr(y_k);
            if( !simplify(eq).getRHS().isBoolConst() ) {
              if (simpl.getRHS().isFalse()) {
                enqueueFact(d_rules->propagateIndexDiseq(simpl));
              } else {
                TRACE("sharing", "from " + read2.toString(), "with find = ", find(read2).getRHS());
                TRACE("sharing", "from " + read1.toString(), "with find = ", find(read1).getRHS());
                TRACE("sharing", "splitting " + y_k.toString(), " and ", x_k.toString());
                addSplitter(eq);
              }
            }
          }
        }
      }
    }
    TRACE("sharing", "checking shared terms, done", int2string(d_reads.size()), "");
  }
}


// w(...,i,v1,...,) => w(......,i,v1')
// Returns Null Theorem if index does not appear
Theorem TheoryArray::pullIndex(const Expr& e, const Expr& index)
{
  DebugAssert(isWrite(e), "Expected write");

  if (e[1] == index) return reflexivityRule(e);

  // Index does not appear
  if (!isWrite(e[0])) return Theorem();

  // Index is at next nesting level
  if (e[0][1] == index) {
    return d_rules->interchangeIndices(e);
  }

  // Index is (possibly) at deeper nesting level
  Theorem thm = pullIndex(e[0], index);
  if (thm.isNull()) return thm;
  thm = substitutivityRule(e, 0, thm);
  thm = transitivityRule(thm, d_rules->interchangeIndices(thm.getRHS()));
  return thm;
}


Theorem TheoryArray::rewrite(const Expr& e)
{
  Theorem thm;
  switch (e.getKind()) {
    case READ: {
      switch(e[0].getKind()) {
        case WRITE:
          thm = d_rules->rewriteReadWrite(e);
          return transitivityRule(thm, simplify(thm.getRHS()));
        case ARRAY_LITERAL: {
          IF_DEBUG(debugger.counter("Read array literals")++;)
            thm = d_rules->readArrayLiteral(e);
          return transitivityRule(thm, simplify(thm.getRHS()));
        }
        case ITE: {
          if (d_liftReadIte) {
            thm = d_rules->liftReadIte(e);
            return transitivityRule(thm, simplify(thm.getRHS()));
          }
          e.setRewriteNormal();
          return reflexivityRule(e);
        }
        default: {
          break;
        }
      }
      const Theorem& rep = e.getRep();
      if (rep.isNull()) return reflexivityRule(e);
      else return symmetryRule(rep);
    }
    case EQ:
      //      if (e[0].isAtomic() && e[1].isAtomic() && isWrite(e[0])) {
      if (isWrite(e[0])) {
        Expr left = e[0], right = e[1];
        int leftWrites = 1, rightWrites = 0;

        // Count nested writes
        Expr e1 = left[0];
        while (isWrite(e1)) { leftWrites++; e1 = e1[0]; }

        Expr e2 = right;
        while (isWrite(e2)) { rightWrites++; e2 = e2[0]; }

        if (rightWrites == 0) {
          if (e1 == e2) {
            thm = d_rules->rewriteSameStore(e, leftWrites);
            return transitivityRule(thm, simplify(thm.getRHS()));
          }
          else {
            e.setRewriteNormal();
            return reflexivityRule(e);
          }
        }
        if (leftWrites > rightWrites) {
          thm = getCommonRules()->rewriteUsingSymmetry(e);
          thm = transitivityRule(thm, d_rules->rewriteWriteWrite(thm.getRHS()));
        }
        else thm = d_rules->rewriteWriteWrite(e);
        return transitivityRule(thm, simplify(thm.getRHS()));
      }
      e.setRewriteNormal();
      return reflexivityRule(e);
    case NOT:
      e.setRewriteNormal();
      return reflexivityRule(e);
    case WRITE: {
//       if (!e.isAtomic()) {
//         e.setRewriteNormal();
//         return reflexivityRule(e);
//       }
      const Expr& store = e[0];
      // Enabling this slows stuff down a lot
      if (!isWrite(store)) {
        DebugAssert(findExpr(e[2]) == e[2], "Expected own find");
        if (isRead(e[2]) && e[2][0] == store && e[2][1] == e[1]) {
          thm = d_rules->rewriteRedundantWrite1(reflexivityRule(e[2]), e);
          return transitivityRule(thm, simplify(thm.getRHS()));
        }
        e.setRewriteNormal();
        return reflexivityRule(e);
      }
      else {
        //      if (isWrite(store)) {
        thm = pullIndex(store,e[1]);
        if (!thm.isNull()) {
          if (thm.isRefl()) {
            return d_rules->rewriteRedundantWrite2(e);
          }
          thm = substitutivityRule(e,0,thm);
          thm = transitivityRule(thm, 
                                 d_rules->rewriteRedundantWrite2(thm.getRHS()));
          return transitivityRule(thm, simplify(thm.getRHS()));
        }
        if (store[1] > e[1]) {
          // Only do this rewrite if the result is atomic
          // (avoid too many ITEs)
          thm = d_rules->interchangeIndices(e);
          thm = transitivityRule(thm, simplify(thm.getRHS()));
          if (thm.getRHS().isAtomic()) {
            return thm;
          }
          // not normal because might be possible to interchange later
          return reflexivityRule(e);
        }
      }
      e.setRewriteNormal();
      return reflexivityRule(e);
    }
    case ARRAY_LITERAL:
      e.setRewriteNormal();
      return reflexivityRule(e);
    default:
      DebugAssert(e.isVar() && isArray(getBaseType(e)),
                  "Unexpected default case");
      e.setRewriteNormal();
      return reflexivityRule(e);
  }
  FatalAssert(false, "should be unreachable");
  return reflexivityRule(e);
}


void TheoryArray::setup(const Expr& e)
{
  if (e.isNot() || e.isEq()) return;
  DebugAssert(e.isAtomic(), "e should be atomic");
  for (int k = 0; k < e.arity(); ++k) {
    e[k].addToNotify(this, e);
  }
  if (isRead(e)) {
    if (e.getType().card() != CARD_INFINITE) {
      addSharedTerm(e);
      theoryOf(e.getType())->addSharedTerm(e);
    }
    Theorem thm = reflexivityRule(e);
    e.setSig(thm);
    e.setRep(thm);
    e.setUsesCC();
    DebugAssert(!isWrite(e[0]), "expected no read of writes");
    // Record the read operator for concrete models
    TRACE("model", "TheoryArray: add array read ", e, "");
    d_reads.push_back(e);
  }
  else if (isWrite(e)) {
    Expr store = e[0];

    if (isWrite(store)) {
      // check interchangeIndices invariant
      if (store[1] > e[1]) {
        e.setNotArrayNormalized();
        if (d_sharedSubterms.count(e) > 0) {
          // write was identified as a shared term before it was setup: add it to list to check
          d_sharedSubtermsList.push_back(e);
        }
      }
      // redundantWrite2 invariant should hold
      DebugAssert(pullIndex(store, e[1]).isNull(),
                  "Unexpected non-array-normalized term in setup");
    }

    // check redundantWrite1 invariant
    // there is a hidden dependency of write(a,i,v) on read(a,i)
    while (isWrite(store)) store = store[0];
    // Need to simplify, not just take find: read could be a signature
    Expr r = simplifyExpr(Expr(READ, store, e[1]));
    theoryCore()->setupTerm(r, this, theoryCore()->getTheoremForTerm(e));
    DebugAssert(r.isAtomic(), "Should be atomic");
    DebugAssert(findExpr(e[2]) == e[2], "Expected own find");
    if (r == e[2] && !e.notArrayNormalized()) {
      e.setNotArrayNormalized();
      if (d_sharedSubterms.count(e) > 0) {
        // write was identified as a shared term before it was setup: add it to list to check
        d_sharedSubtermsList.push_back(e);
      }
    }
    else {
      r.addToNotify(this, e);
    }
  }
}


void TheoryArray::update(const Theorem& e, const Expr& d)
{
  if (inconsistent()) return;

  if (d.isNull()) {
    // d is a shared term
    // we want to mark the new find representative as a shared term too
    Expr lhs = e.getLHS();
    Expr rhs = e.getRHS();
    DebugAssert(d_sharedSubterms.find(lhs) != d_sharedSubterms.end(),
                "Expected lhs to be shared");
    CDMap<Expr,Expr>::iterator it = d_sharedSubterms.find(rhs);
    if (it == d_sharedSubterms.end()) {
      addSharedTerm(rhs);
    }
    return;
  }

  int k, ar(d.arity());

  if (isRead(d)) {
    const Theorem& dEQdsig = d.getSig();
    if (!dEQdsig.isNull()) {
      Expr dsig = dEQdsig.getRHS();
      Theorem thm = updateHelper(d);
      Expr sigNew = thm.getRHS();
      if (sigNew == dsig) return;
      dsig.setRep(Theorem());
      if (isWrite(sigNew[0])) {
        // This is the tricky case.
        // 
  	Theorem thm2 = d_rules->rewriteReadWrite(sigNew);
        thm2 = transitivityRule(thm2, simplify(thm2.getRHS()));
        if (thm2.getRHS().isAtomic()) {
          // If read over write simplifies, go ahead and assert the equality
          enqueueFact(transitivityRule(thm, thm2));
        }
        else {
          // Otherwise, delay processing until checkSat
          addSharedTerm(sigNew);
        }
        //        thm = d_rules->rewriteReadWrite2(sigNew);
        //	Theorem renameTheorem = renameExpr(d);
        //	enqueueFact(transitivityRule(symmetryRule(renameTheorem), thm));
        //	d.setSig(Theorem());
        // 	enqueueFact(thm);
        //	enqueueFact(renameTheorem);
      }
      //      else {

      // Update the signature in all cases
      Theorem repEQsigNew = sigNew.getRep();
	if (!repEQsigNew.isNull()) {
	  d.setSig(Theorem());
	  enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
	}
	else {
	  for (k = 0; k < ar; ++k) {
	    if (sigNew[k] != dsig[k]) {
	      sigNew[k].addToNotify(this, d);
	    }
	  }
	  d.setSig(thm);
	  sigNew.setRep(thm);
          getEM()->invalidateSimpCache();
	}
        //      }
    }
    return;
  }

  DebugAssert(isWrite(d), "Expected write: d = "+d.toString());
  if (find(d).getRHS() != d) return;

  Theorem thm = updateHelper(d);
  Expr sigNew = thm.getRHS();

  // TODO: better normalization in some cases
  Expr store = sigNew[0];
  if (!isWrite(store)) {
    Theorem thm2 = find(Expr(READ, store, sigNew[1]));
    if (thm2.getRHS() == sigNew[2]) {
      thm = transitivityRule(thm,
                             d_rules->rewriteRedundantWrite1(thm2, sigNew));
      sigNew = thm.getRHS();
    }
  }
  else {
    // TODO: this check is expensive, it seems
    Theorem thm2 = pullIndex(store,sigNew[1]);
    if (!thm2.isNull()) {
      if (thm2.isRefl()) {
        thm = transitivityRule(thm,
                               d_rules->rewriteRedundantWrite2(sigNew));
      }
      else {
        thm2 = substitutivityRule(sigNew,0,thm2);
        thm2 = transitivityRule(thm2,
                                d_rules->rewriteRedundantWrite2(thm2.getRHS()));
        thm = transitivityRule(thm, thm2);
      }
      sigNew = thm.getRHS();
      store = sigNew[0];
    }

    if (isWrite(store) && (store[1] > sigNew[1])) {
      thm2 = d_rules->interchangeIndices(sigNew);
      thm2 = transitivityRule(thm2, simplify(thm2.getRHS()));
      // Only update if result is atomic
      if (thm2.getRHS().isAtomic()) {
        thm = transitivityRule(thm, thm2);
        sigNew = thm.getRHS();
        // no need to update store because d == sigNew
        // case only happens if sigNew hasn't changed
      }
    }
  }

  if (d == sigNew) {
    // Hidden dependency must have changed
    while (isWrite(store)) store = store[0];
    Expr r = e.getRHS();
    if (r == d[2]) {
      // no need to update notify list as we are already on list of d[2]
      if (!d.notArrayNormalized()) {
        d.setNotArrayNormalized();
        if (d_sharedSubterms.count(d) > 0) {
          // write has become non-normalized: add it to list to check
          d_sharedSubtermsList.push_back(d);
        }
      }
    }
    else {
      // update the notify list
      r.addToNotify(this, d);
    }
    return;
  }

  DebugAssert(sigNew.isAtomic(), "Expected atomic formula");
  // Since we aren't doing a full normalization here, it's possible that sigNew is not normal
  // and so it might have a different find.  In that case, the find should be the new rhs.
  if (sigNew.hasFind()) {
    Theorem findThm = findRef(sigNew);
    if (!findThm.isRefl()) {
      thm = transitivityRule(thm, findThm);
    }
    assertEqualities(thm);
    return;
  }

  // If it doesn't have a find at all, it needs to be simplified
  Theorem simpThm = simplify(sigNew);
  thm = transitivityRule(thm, simpThm);
  sigNew = thm.getRHS();
  if (sigNew.isAtomic()) {
    assertEqualities(thm);
  }
  else {
    // Simplify could maybe? introduce case splits in the expression.  Handle this by renaminig
    Theorem renameTheorem = renameExpr(d);
    enqueueFact(transitivityRule(symmetryRule(renameTheorem), thm));
    assertEqualities(renameTheorem);
  }

}


Theorem TheoryArray::solve(const Theorem& eThm)
{
  const Expr& e = eThm.getExpr();
  DebugAssert(e.isEq(), "TheoryArray::solve("+e.toString()+")");
  if (isWrite(e[0])) {
    DebugAssert(!isWrite(e[1]), "Should have been rewritten: e = "
		+e.toString());
    return symmetryRule(eThm);
  }
  return eThm;
}


void TheoryArray::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case ARRAY: {
      if (e.arity() != 2) throw Exception
          ("ARRAY type should have two arguments");
      Type t1(e[0]);
      if (t1.isBool()) throw Exception
          ("Array index types must be non-Boolean");
      if (t1.isFunction()) throw Exception
          ("Array index types cannot be functions");
      Type t2(e[1]);
      if (t2.isBool()) throw Exception
          ("Array value types must be non-Boolean");
      if (t2.isFunction()) throw Exception
          ("Array value types cannot be functions");
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in TheoryArray::checkType"
                  +getEM()->getKindName(e.getKind()));
  }

}


Cardinality TheoryArray::finiteTypeInfo(Expr& e, Unsigned& n,
                                        bool enumerate, bool computeSize)
{
  Cardinality card = CARD_INFINITE;
  switch (e.getKind()) {
    case ARRAY: {
      Type typeIndex = Type(e[0]);
      Type typeElem = Type(e[1]);
      if (typeElem.card() == CARD_FINITE &&
          (typeIndex.card() == CARD_FINITE || typeElem.sizeFinite() == 1)) {

        card = CARD_FINITE;

        if (enumerate) {
          // Right now, we only enumerate the first element for finite arrays
          if (n == 0) {
            Expr ind(getEM()->newBoundVarExpr(Type(e[0])));
            e = arrayLiteral(ind, typeElem.enumerateFinite(0));
          }
          else e = Expr();
        }

        if (computeSize) {
          n = 0;
          Unsigned sizeElem = typeElem.sizeFinite();
          if (sizeElem == 1) {
            n = 1;
          }
          else if (sizeElem > 1) {
            Unsigned sizeIndex = typeIndex.sizeFinite();
            if (sizeIndex > 0) {
              n = sizeElem;
              while (--sizeIndex > 0) {
                n = n * sizeElem;
                if (n > 1000000) {
                  // if it starts getting too big, just return 0
                  n = 0;
                  break;
                }
              }
            }
          }
        }
      }
      break;
    }
    default:
      break;
  }
  return card;
}


void TheoryArray::computeType(const Expr& e)
{
  switch (e.getKind()) {
    case READ: {
      DebugAssert(e.arity() == 2,"");
      Type arrType = e[0].getType();
      if (!isArray(arrType)) {
        arrType = getBaseType(arrType);
      }
      if (!isArray(arrType))
	throw TypecheckException
	  ("Expected an ARRAY type in\n\n  "
	   +e[0].toString()+"\n\nBut received this:\n\n  "
	   +arrType.toString()+"\n\nIn the expression:\n\n  "
	   +e.toString());
      Type idxType = getBaseType(e[1]);
      if(getBaseType(arrType[0]) != idxType && idxType != Type::anyType(getEM())) {
	throw TypecheckException
	  ("The type of index expression:\n\n  "
	   +idxType.toString()
	   +"\n\nDoes not match the ARRAY index type:\n\n  "
	   +arrType[0].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      e.setType(arrType[1]);
      break;
    }
    case WRITE: {
      DebugAssert(e.arity() == 3,"");
      Type arrType = e[0].getType();
      if (!isArray(arrType)) {
        arrType = getBaseType(arrType);
      }
      Type idxType = getBaseType(e[1]);
      Type valType = getBaseType(e[2]);
      if (!isArray(arrType))
	throw TypecheckException
	  ("Expected an ARRAY type in\n\n  "
	   +e[0].toString()+"\n\nBut received this:\n\n  "
	   +arrType.toString()+"\n\nIn the expression:\n\n  "
	   +e.toString());
      bool idxCorrect = getBaseType(arrType[0]) == idxType || idxType == Type::anyType(getEM());
      bool valCorrect = getBaseType(arrType[1]) == valType || valType == Type::anyType(getEM());;
      if(!idxCorrect) {
	throw TypecheckException
	  ("The type of index expression:\n\n  "
	   +idxType.toString()
	   +"\n\nDoes not match the ARRAY's type index:\n\n  "
	   +arrType[0].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      if(!valCorrect) {
	throw TypecheckException
	  ("The type of value expression:\n\n  "
	   +valType.toString()
	   +"\n\nDoes not match the ARRAY's value type:\n\n  "
	   +arrType[1].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      e.setType(arrType);
      break;
    }
    case ARRAY_LITERAL: {
      DebugAssert(e.isClosure(), "TheoryArray::computeType("+e.toString()+")");
      DebugAssert(e.getVars().size()==1,
		  "TheoryArray::computeType("+e.toString()+")");
      Type ind(e.getVars()[0].getType());
      e.setType(arrayType(ind, e.getBody().getType()));
      break;
    }
    default:
      DebugAssert(false,"Unexpected type");
      break;
  }
}


Type TheoryArray::computeBaseType(const Type& t) {
  const Expr& e = t.getExpr();
  DebugAssert(e.getKind()==ARRAY && e.arity() == 2,
	      "TheoryArray::computeBaseType("+t.toString()+")");
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    kids.push_back(getBaseType(Type(*i)).getExpr());
  }
  return Type(Expr(e.getOp(), kids));
}


void TheoryArray::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  switch(e.getKind()) {
  case WRITE:
    // a WITH [i] := v -- report a, i and v as the model terms.
//     getModelTerm(e[1], v);
//     getModelTerm(e[2], v);
    v.push_back(e[0]);
    v.push_back(e[1]);
    v.push_back(e[2]);
    break;
  case READ:
    // For a[i], add the index i
    // getModelTerm(e[1], v);
    v.push_back(e[1]);
    // And continue to collect the reads a[i][j] (remember, e is of
    // ARRAY type)
  default:
    // For array terms, find all their reads
    if(e.getType().getExpr().getKind() == ARRAY) {
      for(CDList<Expr>::const_iterator i=d_reads.begin(), iend=d_reads.end();
	  i!=iend; ++i) {
	DebugAssert(isRead(*i) && (*i).arity()==2, "Bad array read: "
		    +(*i).toString());
	if((*i)[0] == e) {
	  // Add both the read operator a[i]
	  // getModelTerm(*i, v);
	  v.push_back(*i);
      // and the index 'i' to the model terms.  Reason: the index to
      // the array should better be a concrete value, and it might not
      // necessarily be in the current list of model terms.
	  // getModelTerm((*i)[1], v);
	  v.push_back((*i)[1]);
	}
      }
    }
    break;
  }
}


void TheoryArray::computeModel(const Expr& e, std::vector<Expr>& v) {
  static unsigned count(0); // For bound vars

  switch(e.getKind()) {
  case WRITE: {
    // We should already have a value for the original array
    Expr res(getModelValue(e[0]).getRHS());
    Expr ind(getEM()->newBoundVarExpr("arr_var", int2string(count++)));
    Type tp(e.getType());
    DebugAssert(isArray(tp) && tp.arity()==2,
		"TheoryArray::computeModel(WRITE)");
    ind.setType(tp[0]);
    res = rewrite(Expr(READ, res, ind)).getRHS();
    Expr indVal(getModelValue(e[1]).getRHS());
    Expr updVal(getModelValue(e[2]).getRHS());
    res = (ind.eqExpr(indVal)).iteExpr(updVal, res);
    res = arrayLiteral(ind, res);
    assignValue(e, res);
    v.push_back(e);
    break;
  }
//   case READ: {
//     // Get the assignment for the index
//     Expr idx(getModelValue(e[1]).getRHS());
//     // And the assignment for the 
//     var = read(idxThm.getRHS(), e[0]);
//   }
    // And continue to collect the reads a[i][j] (remember, e is of
    // ARRAY type)
  default: {
    // Assign 'e' a value later.
    v.push_back(e);
    // Map of e[i] to val for concrete values of i and val
    ExprHashMap<Expr> reads;
    // For array terms, find all their reads
    DebugAssert(getBaseType(e).getExpr().getKind() == ARRAY, "");

    for(CDList<Expr>::const_iterator i=d_reads.begin(), iend=d_reads.end();
	i!=iend; ++i) {
      TRACE("model", "TheoryArray::computeModel: read = ", *i, "");
      DebugAssert(isRead(*i) && (*i).arity()==2, "Bad array read: "
		  +(*i).toString());
      if((*i)[0] == e) {
	// Get the value of the index
	Theorem asst(getModelValue((*i)[1]));
	Expr var;
	if(asst.getLHS()!=asst.getRHS()) {
	  vector<Theorem> thms;
	  vector<unsigned> changed;
	  thms.push_back(asst);
	  changed.push_back(1);
	  Theorem subst(substitutivityRule(*i, changed, thms));
	  assignValue(transitivityRule(symmetryRule(subst),
				       getModelValue(*i)));
	  var = subst.getRHS();
	} else
	  var = *i;
	if(d_applicationsInModel) v.push_back(var);
	// Record it in the map
	Expr val(getModelValue(var).getRHS());
	DebugAssert(!val.isNull(), "TheoryArray::computeModel(): Variable "
		    +var.toString()+" has a Null value");
	reads[var] = val;
      }
    }
    // Create an array literal
    if(reads.size()==0) { // Leave the array uninterpreted
      assignValue(reflexivityRule(e));
    } else {
      // Bound var for the index
      Expr ind(getEM()->newBoundVarExpr("arr_var", int2string(count++)));
      Type tp(e.getType());
      DebugAssert(isArray(tp) && tp.arity()==2,
		  "TheoryArray::computeModel(WRITE)");
      ind.setType(tp[0]);
      ExprHashMap<Expr>::iterator i=reads.begin(), iend=reads.end();
      DebugAssert(i!=iend,
		  "TheoryArray::computeModel(): expected the reads "
		  "table be non-empty");
      // Use one of the concrete values as a default
      Expr res((*i).second);
      ++i;
      DebugAssert(!res.isNull(), "TheoryArray::computeModel()");
      for(; i!=iend; ++i) {
	// Optimization: if the current value is the same as that of the
	// next application, skip this case; i.e. keep 'res' instead of
	// building ite(cond, res, res).
	if((*i).second == res) continue;
	// ITE condition
	Expr cond = ind.eqExpr((*i).first[1]);
	res = cond.iteExpr((*i).second, res);
      }
      // Construct the array literal
      res = arrayLiteral(ind, res);
      assignValue(e, res);
    }
    break;
  }
  }
}


Expr TheoryArray::computeTCC(const Expr& e)
{
  Expr tcc(Theory::computeTCC(e));
  switch (e.getKind()) {
    case READ:
      DebugAssert(e.arity() == 2,"");
      return tcc.andExpr(getTypePred(e[0].getType()[0], e[1]));
    case WRITE: {
      DebugAssert(e.arity() == 3,"");
      Type arrType = e[0].getType();
      return rewriteAnd(getTypePred(arrType[0], e[1]).andExpr
                        (getTypePred(arrType[1], e[2])).andExpr(tcc)).getRHS();
    }
    case ARRAY_LITERAL: {
      return tcc;
    }
    default:
      DebugAssert(false,"TheoryArray::computeTCC: Unexpected expression: "
		  +e.toString());
      return tcc;
  }
}


///////////////////////////////////////////////////////////////////////////////
// Pretty-printing			                                     //
///////////////////////////////////////////////////////////////////////////////


bool debug_write = false;

ExprStream& TheoryArray::print(ExprStream& os, const Expr& e)
{
  d_theoryUsed = true;
  if (theoryCore()->getTranslator()->printArrayExpr(os, e)) return os;
  switch(os.lang()) {
  case PRESENTATION_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 1)
	os << "[" << push << e[0] << push << "]";
      else
	os << e[0] << "[" << push << e[1] << push << "]";
      break;
    case WRITE:
      IF_DEBUG(
        if (debug_write) {
          os << "w(" << push << e[0] << space << ", " 
             << push << e[1] << ", " << push << e[2] << push << ")";
          break;
        }
      )
      os << "(" << push << e[0] << space << "WITH [" 
	 << push << e[1] << "] := " << push << e[2] << push << ")";
      break;
    case ARRAY:
      os << "(ARRAY" << space << e[0] << space << "OF" << space << e[1] << ")";
      break;
    case ARRAY_LITERAL:
      if(e.isClosure()) {
	const vector<Expr>& vars = e.getVars();
	const Expr& body = e.getBody();
	os << "(" << push << "ARRAY" << space << "(" << push;
	bool first(true);
	for(size_t i=0; i<vars.size(); ++i) {
	  if(first) first=false;
	  else os << push << "," << pop << space;
	  os << vars[i];
	  if(vars[i].isVar())
	    os << ":" << space << pushdag << vars[i].getType() << popdag;
	}
	os << push << "):" << pop << pop << space << body << push << ")";
      } else
	e.printAST(os);
      break;
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case PRESENTATION_LANGUAGE
  case SMTLIB_LANG:
  case SMTLIB_V2_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 2)
	os << "(" << push << "select" << space << e[0]
	   << space << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case WRITE:
      if(e.arity() == 3)
	os << "(" << push << "store" << space << e[0]
	   << space << e[1] << space << e[2] << push << ")";
      else
	e.printAST(os);
      break;
    case ARRAY:
      throw SmtlibException("ARRAY should be handled by printArrayExpr");
      break;      
    case ARRAY_LITERAL:
      throw SmtlibException("SMT-LIB does not support ARRAY literals.\n"
                            "Suggestion: use command-line flag:\n"
                            "  -output-lang presentation");
      e.printAST(os);
    default:
      throw SmtlibException("TheoryArray::print: default not supported");
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case LISP_LANGUAGE
  case LISP_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 2)
	os << "(" << push << "READ" << space << e[0]
	   << space << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case WRITE:
      if(e.arity() == 3)
	os << "(" << push << "WRITE" << space << e[0]
	   << space << e[1] << space << e[2] << push << ")";
      else
	e.printAST(os);
      break;
    case ARRAY:
      os << "(" << push << "ARRAY" << space << e[0]
	 << space << e[1] << push << ")";
      break;      
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case LISP_LANGUAGE
  default:
    // Print the top node in the default LISP format, continue with
    // pretty-printing for children.
    e.printAST(os);
  }
  return os;
}

//////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryArray::parseExprOp(const Expr& e) {
  //  TRACE("parser", "TheoryArray::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryArray::parseExprOp:\n e = "+e.toString());
  
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
    case READ: 
      if(!(e.arity() == 3))
	throw ParserException("Bad array access expression: "+e.toString());
      return Expr(READ, parseExpr(e[1]), parseExpr(e[2]));
    case WRITE: 
      if(!(e.arity() == 4))
	throw ParserException("Bad array update expression: "+e.toString());
      return Expr(WRITE, parseExpr(e[1]), parseExpr(e[2]), parseExpr(e[3]));
    case ARRAY: { 
      vector<Expr> k;
      Expr::iterator i = e.begin(), iend=e.end();
      // Skip first element of the vector of kids in 'e'.
      // The first element is the operator.
      ++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) 
        k.push_back(parseExpr(*i));
      return Expr(kind, k, e.getEM());
      break;
    }
    case ARRAY_LITERAL: { // (ARRAY (v tp1) body)
      if(!(e.arity() == 3 && e[1].getKind() == RAW_LIST && e[1].arity() == 2))
	throw ParserException("Bad ARRAY literal expression: "+e.toString());
      const Expr& varPair = e[1];
      if(varPair.getKind() != RAW_LIST)
	throw ParserException("Bad variable declaration block in ARRAY "
			      "literal expression: "+varPair.toString()+
			      "\n e = "+e.toString());
      if(varPair[0].getKind() != ID)
	throw ParserException("Bad variable declaration in ARRAY"
			      "literal expression: "+varPair.toString()+
			      "\n e = "+e.toString());
      Type varTp(parseExpr(varPair[1]));
      vector<Expr> var;
      var.push_back(addBoundVar(varPair[0][0].getString(), varTp));
      Expr body(parseExpr(e[2]));
      // Build the resulting Expr as (LAMBDA (vars) body)
      return getEM()->newClosureExpr(ARRAY_LITERAL, var, body);
      break;
    }
    default:
      DebugAssert(false,
	  	  "TheoryArray::parseExprOp: wrong type: "
		  + e.toString());
    break;
  }
  return e;
}

Expr TheoryArray::getBaseArray(const Expr& e) const {
  if (e.getKind() == WRITE) return getBaseArray(e[0]);
  return e;
}

namespace CVC3 {

Expr arrayLiteral(const Expr& ind, const Expr& body) {
  vector<Expr> vars;
  vars.push_back(ind);
  return body.getEM()->newClosureExpr(ARRAY_LITERAL, vars, body);
}

} // end of namespace CVC3
