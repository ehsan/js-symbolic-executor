#ifndef LFSC_BOOL_PROOF_H_
#define LFSC_BOOL_PROOF_H_

#include "LFSCProof.h"

class LFSCBoolRes : public LFSCProof
{
private:
  RefPtr< LFSCProof > d_children[2];
  int d_var;
  bool d_col;
  LFSCBoolRes(LFSCProof* pf1, LFSCProof* pf2, int v, bool col): LFSCProof(),
    d_var(v), d_col(col){
    d_children[0] = pf1;
    d_children[1] = pf2;
  }
  virtual ~LFSCBoolRes(){}
  long int get_length(){
    return 10 + d_children[0]->get_string_length() + d_children[1]->get_string_length();
  }
public:
  virtual LFSCBoolRes* AsLFSCBoolRes(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  void print_struct( std::ostream& s, int ind = 0 );
  //standard Make
  static LFSCProof* Make(LFSCProof* pf1, LFSCProof* pf2, int v, bool col);
  // make the boolean resolution proof, where p1 corresponds to pf1, p2 corresponds to pf2
  //res is the expression to resolve upon
  static LFSCProof* Make( LFSCProof* p1, LFSCProof* p2, const Expr& res, const Expr& pf, bool cascadeOr = false );
  //make the boolean resolution collection proof, where e is what to resolve
  static LFSCProof* MakeC( LFSCProof* p, const Expr& res );
  LFSCProof* clone() { return new LFSCBoolRes( d_children[0].get(), d_children[1].get(), d_var, d_col ); }
  int getNumChildren() { return 2; }
  LFSCProof* getChild( int n ) { return d_children[n].get(); }
  int checkBoolRes( std::vector< int >& clause );
};

class LFSCLem : public LFSCProof
{
private:
  int d_var;
  LFSCLem( int v ) : LFSCProof(),
    d_var( v ) {}
  virtual ~LFSCLem(){}
  long int get_length() { return 10; }
public:
  virtual LFSCLem* AsLFSCLem(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 ){ s << "(lem _ _ @a" << abs( d_var ) << ")"; }
  void print_struct( std::ostream& s, int ind = 0 ){ s << "(lem " << d_var << ")"; }
  static LFSCProof* Make(int v){ return new LFSCLem( v ); }
  bool IsTrivial() { return true; }
  LFSCProof* clone() { return new LFSCLem( d_var ); }
  int checkBoolRes( std::vector< int >& clause ){
    clause.push_back( -d_var );
    clause.push_back( d_var );
    return 0;
  }
};

class LFSCClausify : public LFSCProof
{
private:
  friend class LFSCPrinter;
  int d_var;
  RefPtr< LFSCProof > d_pf;
  LFSCClausify( int v, LFSCProof* pf ) : LFSCProof(), d_var( v ), d_pf( pf ){}
  virtual ~LFSCClausify(){}
  long int get_length() { return 10 + d_pf->get_string_length(); }
  //this should be called by Make
  static LFSCProof* Make_i( const Expr& e, LFSCProof* p, std::vector< Expr >& exprs, const Expr& end );
public:
  virtual LFSCClausify* AsLFSCClausify(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  void print_struct( std::ostream& s, int ind = 0 ){ s << "(clausify " << d_var << ")"; }
  //standard Make
  static LFSCProof* Make( int v, LFSCProof* pf ){ return new LFSCClausify( v, pf ); }
  // input : a formula e, and a proof of that formula p.
  static LFSCProof* Make( const Expr& e, LFSCProof* p, bool cascadeOr = false );
  //clone
  LFSCProof* clone() { return new LFSCClausify( d_var, d_pf.get() ); }
  int getNumChildren() { return 1; }
  LFSCProof* getChild( int n ) { return d_pf.get(); }
  int checkBoolRes( std::vector< int >& clause ){
    d_pf->checkBoolRes( clause );
    clause.push_back( d_var );
    return 0;
  }
};

class LFSCAssume : public LFSCProof {
private:
  int d_var;
  RefPtr< LFSCProof > d_pf;
  bool d_assm;
  int d_type;
  LFSCAssume( int v, LFSCProof* pf, bool assm, int type ) : LFSCProof(), d_var( v ), d_pf( pf ), d_assm( assm ), d_type( type ){}
  virtual ~LFSCAssume(){}
  long int get_length() { return 10 + d_pf->get_string_length(); }
public:
  virtual LFSCAssume* AsLFSCAssume(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  void print_struct( std::ostream& s, int ind = 0 );
  static LFSCProof* Make( int v, LFSCProof* pf, bool assm = true, int type=3 ){
    return new LFSCAssume( v, pf, assm, type );
  }
  LFSCProof* clone() { return new LFSCAssume( d_var, d_pf.get(), d_assm, d_type ); }
  int getNumChildren() { return 1; }
  LFSCProof* getChild( int n ) { return d_pf.get(); }

  int checkBoolRes( std::vector< int >& clause ){
    if( d_type==3 ){
      d_pf->checkBoolRes( clause );
      clause.push_back( -d_var );
    }
    return 0;
  }
};

#endif
