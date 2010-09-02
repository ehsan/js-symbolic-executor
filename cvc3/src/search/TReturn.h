#ifndef TRETURN_H_
#define TRETURN_H_

#include "LFSCProof.h"

//////////////////////////////////////////
// TReturn = (p_lfsc, L, c)
// implements transformation
/////////////////////////////////////////

class TReturn : public LFSCObj
{
private:
  RefPtr< LFSCProof > d_lfsc_pf;
  // literals (we only store the indices) i corresponds to v_i and -i to  not v_i
  std::vector <int> d_L;
  // literals we use
  std::vector <int> d_L_used;
  // constant
  Rational d_c;
  bool d_hasRt;
  // constructor
  //flag for whether d_lfsc_pf is proving
  //0: psi,
  //1: Y(psi)               (arithmetic collapse)
  //2: Y2( psi )            (double implications are single implications)
  //3: clause( Y2( psi ) )
  int d_provesY;
  bool lcalced;
public:
  TReturn(LFSCProof* lfsc_pf, std::vector<int>& L, std::vector<int>& Lused, Rational r, bool hasR, int pvY);

  Rational mult_rational( TReturn* lhs );
  void getL( std::vector< int >& lget, std::vector< int >& lgetu );
  bool hasRational() { return d_hasRt; }
  Rational getRational() { return d_c; }
  LFSCProof* getLFSCProof(){ return d_lfsc_pf.get(); }
  int getProvesY() { return d_provesY; }
  bool hasFv() { return !d_L_used.empty(); }
#ifdef OPTIMIZE
  void calcL( std::vector< int >& lget, std::vector< int >& lgetu );
#endif

  // make it so that the two TReturns agree on what they are proving
  // t1 corresponds to the conversion of pf1, proving psi, Y( ps1 ), or Y2( ps1 )
  // t2 corresponds to the conversion of pf2, proving psi, Y( ps1 ), or Y2( ps1 )
  // on return, t1->d_proveY should equal t2->d_proveY
  // this will return the mode they normalized on, -1 means fail
  static int normalize_tret( const Expr& pf1, TReturn*& t1, const Expr& pf2, TReturn*& t2, bool rev_pol = false );
  //normalize TReturn to prove a certain type
  // this will return the mode it normalized on, -1 means fail
  static int normalize_tr( const Expr& pf1, TReturn*& t1, int y, bool rev_pol = false, bool printErr = true );
  //normalize from polynomial formula to term formula atom
  static void normalize_to_tf( const Expr& pf, TReturn*& t1, int y );
};

#endif
