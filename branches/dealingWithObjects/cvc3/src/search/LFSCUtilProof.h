#ifndef LFSC_UTIL_PROOF_H_
#define LFSC_UTIL_PROOF_H_

#include "LFSCProof.h"

class LFSCProofExpr : public LFSCProof
{
  bool isHole;
  Expr d_e;
  LFSCProofExpr( const Expr& e, bool isH = false  );
  void initialize();
  virtual ~LFSCProofExpr(){}
  long int get_length() { return 10; }
public:
  virtual LFSCProofExpr* AsLFSCProofExpr(){ return this; }
  void print_pf( std::ostream& s, int ind );
  static LFSCProof* Make( const Expr& e, bool isH = false ) { return new LFSCProofExpr( e, isH ); }
  LFSCProof* clone() { return new LFSCProofExpr( d_e, isHole ); }

  void fillHoles() { isHole = false; }
};

class LFSCPfVar : public LFSCProof {
private:
  static std::map< int, RefPtr< LFSCProof > > vMap;
  string name;
  LFSCPfVar( string nm ) : LFSCProof(), name( nm ){}
  virtual ~LFSCPfVar(){}
  long int get_length() { return name.length(); }
public:
  virtual LFSCPfVar* AsLFSCPfVar(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 ){ s << name; }
  void print_struct( std::ostream& s, int ind = 0 ){ s << name; }
  static LFSCProof* Make( const char* c, int v );
  static LFSCProof* MakeV( int v );
  LFSCProof* clone() { return new LFSCPfVar( name ); }
};

class LFSCPfLambda : public LFSCProof {
private:
  RefPtr< LFSCPfVar > pfV;
  RefPtr< LFSCProof > body;
  //just a placeholder.  This is what the lambda abstracts.
  RefPtr< LFSCProof > abstVal;
  //constructor
  LFSCPfLambda( LFSCPfVar* v, LFSCProof* bd, LFSCProof* aVal = NULL ) : LFSCProof(),
    pfV( v ), body( bd ), abstVal( aVal ){}
  virtual ~LFSCPfLambda(){}
  long int get_length() { return 5 + pfV->get_string_length() + body->get_string_length(); }
public:
  virtual LFSCPfLambda* AsLFSCPfLambda(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  static LFSCProof* Make( LFSCPfVar* v, LFSCProof* bd, LFSCProof* aVal = NULL ){
    return new LFSCPfLambda( v, bd, aVal );
  }
  LFSCProof* clone() { return new LFSCPfLambda( pfV.get(), body.get(), abstVal.get() ); }
  int getNumChildren() { return 2; }
  LFSCProof* getChild( int n ) { return (n==0) ? (LFSCProof*)pfV.get() : body.get(); }
};
//
class LFSCProofGeneric : public LFSCProof{
private:
  vector< RefPtr< LFSCProof > > d_pf;
  vector< string > d_str;
  bool debug_str;
  //Proof in the form "S1.print(P1).S2.print(P2).....print(Pn).S{n+1}"
  LFSCProofGeneric( vector< RefPtr< LFSCProof > >& d_pfs, vector< string >& d_strs, bool db_str = false ) : LFSCProof(){
    for( int a=0; a<(int)d_pfs.size(); a++ )
      d_pf.push_back( d_pfs[a].get() );
    for( int a=0; a<(int)d_strs.size(); a++ )
      d_str.push_back( d_strs[a] );
    debug_str = db_str;
  }
  virtual ~LFSCProofGeneric(){}
  long int get_length();
public:
  virtual LFSCProofGeneric* AsLFSCProofGeneric(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  //Proof in the form "S1.print(P1).S2.print(P2).....print(Pn).S{n+1}"
  static LFSCProof* Make( vector< RefPtr< LFSCProof > >& d_pfs, std::vector< string >& d_strs, bool db_str = false ){
    return new LFSCProofGeneric( d_pfs, d_strs, db_str );
  }
  //proof printed in the form "S1.print(P1).S2"
  static LFSCProof* Make( string str_pre, LFSCProof* sub_pf, string str_post, bool db_str = false );
  //proof printed in the form "S1.print(P1).print(P2).S2"
  static LFSCProof* Make( string str_pre, LFSCProof* sub_pf1, LFSCProof* sub_pf2, string str_post, bool db_str = false );
  static LFSCProof* MakeStr( const char* c, bool db_str = false );
  static LFSCProof* MakeUnk(){ return MakeStr( "unk" ); }
  LFSCProof* clone(){ return new LFSCProofGeneric( d_pf, d_str, debug_str ); }
  int getNumChildren() { return (int)d_pf.size(); }
  LFSCProof* getChild( int n ) { return d_pf[n].get(); }
};


class LFSCPfLet : public LFSCProof{
private:
  RefPtr< LFSCProof > d_letPf;
  RefPtr< LFSCPfVar > d_pv;
  RefPtr< LFSCProof > d_body;
  //this should be equal to d_letPf, although it could be something else based on fv
  RefPtr< LFSCProof > d_letPfRpl;
  //this by default is d_pv, although it could be something else based on fv
  RefPtr< LFSCProof > d_pvRpl;
  bool d_isTh;
  LFSCPfLet( LFSCProof* letPf, LFSCPfVar* pv, LFSCProof* body,
             bool isTh, LFSCProof* letPfRpl, LFSCProof* pvRpl ) : LFSCProof(),
    d_letPf( letPf ),d_pv( pv ),d_body( body ),d_letPfRpl( letPfRpl ),d_pvRpl( pvRpl ),d_isTh( isTh ){}
  LFSCPfLet( LFSCProof* letPf, LFSCPfVar* pv, LFSCProof* body,
             bool isTh, std::vector< int >& fv );
  virtual ~LFSCPfLet(){}
  long int get_length() {
    return 10 + d_letPf->get_string_length() + d_pv->get_string_length() + d_body->get_string_length();
  }
public:
  virtual LFSCPfLet* AsLFSCPfLet(){ return this; }
  void print_pf( std::ostream& s, int ind = 0 );
  void print_struct( std::ostream& s, int ind = 0 );
  static LFSCProof* Make( LFSCProof* letPf, LFSCPfVar* pv, LFSCProof* body,
                          bool isTh, std::vector< int >& fv ){
    return new LFSCPfLet( letPf, pv, body, isTh, fv );
  }
  LFSCProof* clone() { return new LFSCPfLet( d_letPf.get(), d_pv.get(), d_body.get(),
                                             d_isTh, d_letPfRpl.get(), d_pvRpl.get() ); }
  //should not be part of the children structure.
};


#endif
