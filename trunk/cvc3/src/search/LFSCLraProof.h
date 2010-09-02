#ifndef LFSC_LRA_PROOF_H_
#define LFSC_LRA_PROOF_H_

#include "LFSCProof.h"

// lra_add_~_~
class LFSCLraAdd: public LFSCProof{
private:
  RefPtr< LFSCProof > d_children[2];
  int d_op1, d_op2;

  LFSCLraAdd(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2): LFSCProof(),
    d_op1(op1),
    d_op2(op2){
    d_children[0] = pf1;
    d_children[1] = pf2;
  }
  virtual ~LFSCLraAdd(){}
  long int get_length(){
    return 20 + d_children[0]->get_string_length() + d_children[1]->get_string_length();
  }
public:
  virtual LFSCLraAdd* AsLFSCLraAdd(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  static LFSCProof* Make(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2);
  LFSCProof* clone() { return new LFSCLraAdd( d_children[0].get(), d_children[1].get(), d_op1, d_op2 ); }
  int getNumChildren() { return 2; }
  LFSCProof* getChild( int n ) { return d_children[n].get(); }
  int checkOp() { return get_knd_result( d_op1, d_op2 ); }
};


// lra_~_axiom

class LFSCLraAxiom: public LFSCProof{
private:
  static RefPtr< LFSCProof > eq;
  int d_op;
  Rational d_r;
  LFSCLraAxiom(int op ) : LFSCProof(), d_op(op){}
  LFSCLraAxiom(int op, Rational r): LFSCProof(),
    d_op(op),
    d_r(r){}
  virtual ~LFSCLraAxiom(){}
  long int get_length(){ return 15; }
public:
  virtual LFSCLraAxiom* AsLFSCLraAxiom(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  bool isTrivial() { return d_op==EQ; }
  static LFSCProof* MakeEq();
  static LFSCProof* Make( Rational r, int op ){ return new LFSCLraAxiom( op,r ); }
  LFSCProof* clone() { return new LFSCLraAxiom( d_op, d_r ); }
  int checkOp() { return d_op; }
};


// lra_mult_c
class LFSCLraMulC: public LFSCProof{
private:
  RefPtr< LFSCProof > d_pf;
  Rational d_r;
  int d_op; // = | > | >= | distinct
  LFSCLraMulC(LFSCProof* pf, Rational r, int op): LFSCProof(),
    d_pf(pf),
    d_r(r),
    d_op(op){
    d_op = pf->checkOp() != -1 ? pf->checkOp() : d_op;
  }
  virtual ~LFSCLraMulC(){}
  long int get_length(){ return 20 + d_pf->get_string_length(); }
public:
  virtual LFSCLraMulC* AsLFSCLraMulC(){ return this; }
  bool isLraMulC() { return true; }
  void print_pf( std::ostream& s, int ind = 0 );
  static LFSCProof* Make(LFSCProof* pf, Rational r, int op);
  LFSCProof* clone() { return new LFSCLraMulC( d_pf.get(), d_r, d_op ); }
  int getNumChildren() { return 1; }
  LFSCProof* getChild( int n ) { return d_pf.get(); }
  int checkOp() { return d_op; }
};


// lra_sub_~_~
class LFSCLraSub: public LFSCProof{
private:
  RefPtr< LFSCProof > d_children[2];
  int d_op1, d_op2;
  LFSCLraSub(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2): LFSCProof(),
    d_op1(op1),
    d_op2(op2){
    d_children[0] = pf1;
    d_children[1] = pf2;
    d_op1 = pf1->checkOp()!=-1 ? pf1->checkOp() : d_op1;
    d_op2 = pf2->checkOp()!=-1 ? pf2->checkOp() : d_op2;
  }
  virtual ~LFSCLraSub(){}
  long int get_length(){
    return 20 + d_children[0]->get_string_length() + d_children[1]->get_string_length();
  }
public:
  virtual LFSCLraSub* AsLFSCLraSub(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  static LFSCProof* Make(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2);
  LFSCProof* clone() { return new LFSCLraSub( d_children[0].get(), d_children[1].get(), d_op1, d_op2 ); }
  int getNumChildren() { return 2; }
  LFSCProof* getChild( int n ) { return d_children[n].get(); }
  int checkOp() { return get_knd_result( d_op1, d_op2 ); }
};

class LFSCLraPoly : public LFSCProof
{
private:
  RefPtr< LFSCProof > d_pf;
  int d_var;
  int d_op;
  LFSCLraPoly( LFSCProof* pf, int var, int op ) : LFSCProof(),
    d_pf( pf ),
    d_var( var ),
    d_op( op ){
    d_op = pf->checkOp() != -1 ? pf->checkOp() : d_op;
  }
  virtual ~LFSCLraPoly(){}
  long int get_length(){ return 15 + d_pf->get_string_length(); }
public:
  virtual LFSCLraPoly* AsLFSCLraPoly(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  static LFSCProof* Make( LFSCProof* pf, int var, int op ){
    return new LFSCLraPoly( pf, var, op );
  }
  static LFSCProof* Make( const Expr& e, LFSCProof* p );
  LFSCProof* clone() { return new LFSCLraPoly( d_pf.get(), d_var, d_op ); }
  int getNumChildren() { return 1; }
  LFSCProof* getChild( int n ) { return d_pf.get(); }
  int checkOp() {
    return get_normalized( d_op, d_var<0 );
  }

};

class LFSCLraContra : public LFSCProof
{
private:
  RefPtr< LFSCProof > d_pf;
  int d_op;
  LFSCLraContra( LFSCProof* pf, int op ) : LFSCProof(),
    d_pf( pf ),
    d_op( op ){
    d_op = pf->checkOp() != -1 ? pf->checkOp() : d_op;
  }
  virtual ~LFSCLraContra(){}
  long int get_length(){ return 15 + d_pf->get_string_length(); }
public:
  virtual LFSCLraContra* AsLFSCLraContra(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 ){
    s <<"(lra_contra_" << kind_to_str(d_op) << " _ ";
    d_pf->print( s, ind+1 );
    s << ")";
  }
  static LFSCProof* Make( LFSCProof* pf, int op ){
    return new LFSCLraContra( pf, op );
  }
  LFSCProof* clone() { return new LFSCLraContra( d_pf.get(), d_op ); }
  int getNumChildren() { return 1; }
  LFSCProof* getChild( int n ) { return d_pf.get(); }
  int checkOp() { return d_op; }
};


#endif
