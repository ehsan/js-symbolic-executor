#ifndef LFSC_PROOF_H_
#define LFSC_PROOF_H_

#include "LFSCObject.h"

//////////////////////////////////
/// LFSC Proof Class & subclasses
//////////////////////////////////

class LFSCProofExpr;
class LFSCLraAdd;
class LFSCLraSub;
class LFSCLraMulC;
class LFSCLraAxiom;
class LFSCLraContra;
class LFSCLraPoly;
class LFSCBoolRes;
class LFSCLem;
class LFSCClausify;
class LFSCAssume;
class LFSCProofGeneric;
class LFSCPfVar;
class LFSCPfLambda;
class LFSCPfLet;

class LFSCProof : public LFSCObj{
protected:
  static int pf_counter;
  static std::map< LFSCProof*, int > lambdaMap;
  static std::map< LFSCProof*, LFSCProof* > lambdaPrintMap;
  int printCounter;
  LFSCProof* rplProof;
  static int lambdaCounter;
  long int strLen;
  int chOp;
  int assumeVar;
  int assumeVarUsed;

  std::vector< int > br;
  bool brComputed;

  LFSCProof();
  virtual long int get_length() { return 0; }
  virtual ~LFSCProof(){}
public:
  virtual LFSCProofExpr* AsLFSCProofExpr(){ return NULL; }
  virtual LFSCLraAdd* AsLFSCLraAdd(){ return NULL; }
  virtual LFSCLraSub* AsLFSCLraSub(){ return NULL; }
  virtual LFSCLraMulC* AsLFSCLraMulC(){ return NULL; }
  virtual LFSCLraAxiom* AsLFSCLraAxiom(){ return NULL; }
  virtual LFSCLraContra* AsLFSCLraContra(){ return NULL; }
  virtual LFSCLraPoly* AsLFSCLraPoly(){ return NULL; }
  virtual LFSCBoolRes* AsLFSCBoolRes(){ return NULL; }
  virtual LFSCLem* AsLFSCLem(){ return NULL; }
  virtual LFSCClausify* AsLFSCClausify(){ return NULL; }
  virtual LFSCAssume* AsLFSCAssume(){ return NULL; }
  virtual LFSCProofGeneric* AsLFSCProofGeneric(){ return NULL; }
  virtual LFSCPfVar* AsLFSCPfVar(){ return NULL; }
  virtual LFSCPfLambda* AsLFSCPfLambda(){ return NULL; }
  virtual LFSCPfLet* AsLFSCPfLet(){ return NULL; }

  virtual bool isLraMulC() { return false; }
  static int make_lambda( LFSCProof* p ){
    if( lambdaMap[p]==0 ){
      lambdaMap[p] = lambdaCounter;
      lambdaCounter++;
    }
    return lambdaMap[p];
  }
  void print( std::ostream& s, int ind = 0 );
  virtual void print_pf( std::ostream& s, int ind = 0 )=0;
  virtual bool isTrivial() { return false; }
  long int get_string_length() {
    if( strLen<0 ){
      strLen = get_length();
      //to prevent overflow
      for( int a=0; a<getNumChildren(); a++ ){
        if( strLen<getChild( a )->get_string_length() ){
          strLen = getChild( a )->get_string_length();
        }
      }
    }
    return strLen;
  }
  void print_structure( std::ostream& s, int ind = 0 );
  virtual void print_struct( std::ostream& s, int ind = 0 ){
    static int psCounter = 0;
    s << "P" << psCounter;
    psCounter++;
  }
  void setRplProof( LFSCProof* p ) { rplProof = p; }
  virtual void fillHoles();
#ifdef OPTIMIZE
  void calcL( std::vector< int >& lget, std::vector< int >& lgetu );
#endif

  friend class LFSCPrinter;

  virtual LFSCProof* clone() = 0;
  virtual int getNumChildren() { return 0; }
  virtual LFSCProof* getChild( int n ) { return NULL; }
  virtual int checkOp();
  int getChOp(){ return chOp; }
  void setChOp( int c ) { chOp = c; }
  virtual int checkBoolRes( std::vector< int >& clause ){ return 0; }

//proof making methods
public:
  static LFSCProof* Make_CNF( const Expr& form, const Expr& reason, int pos );
  static LFSCProof* Make_not_not_elim( const Expr& pf, LFSCProof* p );
  static LFSCProof* Make_mimic( const Expr& pf, LFSCProof* p, int numHoles );
  static LFSCProof* Make_and_elim( const Expr& form, LFSCProof* p, int n, const Expr& expected );

  static int get_proof_counter() { return pf_counter; }
};


#endif
