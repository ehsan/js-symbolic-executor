#ifndef LFSC_CONVERT_H_
#define LFSC_CONVERT_H_

#include "TReturn.h"

class LFSCConvert : public LFSCObj
{
private:
  //the converted LFSCProof
  RefPtr< LFSCProof > pfinal;
  // translations of proofs for cvc3_to_lfsc : if a proof has already been done,
  // return the TReturn store for it
  ExprMap<bool> d_th_trans;
  ExprMap<TReturn*> d_th_trans_map[2];
  // these are the current TReturns we need to make into lambdas
  std::map<TReturn*, bool> d_th_trans_lam[2];
  //counts for theory/non-theory
  int nodeCount;
  int nodeCountTh;
  int unodeCount;
  int unodeCountTh;
  //whether to ignore theory lemmas
  bool ignore_theory_lemmas;

  // other helper methods
  bool isTrivialTheoryAxiom(const Expr& expr, bool checkBody = false );
  bool isTrivialBooleanAxiom(const Expr& expr);
  bool isIgnoredRule(const Expr& expr);

  // main method to implement T transformation:
  // cvc3 proof syntax tree to lfsc proof syntax tree
  // beneath_lc is whether you are beneath a learned clause
  // rev_pol is whether you should prove ~psi2 V psi1 in the provesY = 2 case (reverse the implication)
  TReturn* cvc3_to_lfsc(const Expr& pf, bool beneath_lc = false, bool rev_pol=false);
  TReturn* cvc3_to_lfsc_h(const Expr& pf, bool beneath_lc = false, bool rev_pol=false);
  //do basic subst op procedure
  TReturn* do_bso( const Expr& pf, bool beneath_lc, bool rev_pol, TReturn* t1, TReturn* t2, ostringstream& ose );
  //get proof type
  int get_proof_pattern( const Expr& pf, Expr& modE );
  //make the let proof
  LFSCProof* make_let_proof( LFSCProof* p );
  //make trusted
  TReturn* make_trusted( const Expr& pf );

  virtual ~LFSCConvert(){}
public:
  LFSCConvert( int lfscm );
  //main conversion function
  void convert( const Expr& pf );
  //get the results
  LFSCProof* getLFSCProof() { return pfinal.get(); }
};

#endif
