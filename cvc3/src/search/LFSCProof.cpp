#include "LFSCProof.h"

#include "LFSCBoolProof.h"
#include "LFSCUtilProof.h"

int LFSCProof::pf_counter = 0;
std::map< LFSCProof*, int > LFSCProof::lambdaMap;
std::map< LFSCProof*, LFSCProof* > LFSCProof::lambdaPrintMap;
int LFSCProof::lambdaCounter = 1;

LFSCProof::LFSCProof()
{
  pf_counter++;
  printCounter = 0;
  strLen = -1;
  rplProof = NULL;
  chOp = -1;
  brComputed = false;
  assumeVar = -1;
  assumeVarUsed = -1;
}

void LFSCProof::print( std::ostream& s, int ind ){
  LFSCProof* p = rplProof ? rplProof : lambdaPrintMap[this];
  if( p ){
    p->print( s, ind );
  }else{
    if( lambdaMap.find( this )!=lambdaMap.end() && printCounter>0 ){
      print_warning( "Warning: printing out lambda abstracted proof more than once");
#ifdef IGNORE_PRINT_MULTI_LAMBDA
      return;
#endif
    }
    //if( printCounter>0 ){
    //  return;
    //}
    printCounter++;
    indent( s, ind );
    print_pf( s, ind );
  }
}

void LFSCProof::print_structure( std::ostream& s, int ind ){
  LFSCProof* p = rplProof ? rplProof : lambdaPrintMap[this];
  if( p ){
    p->print( s, ind );
  }else{
    indent( s, ind );
    if( lambdaMap.find( this )!=lambdaMap.end() && printCounter>0 ){
      //just a warning, print it out in ose
      print_warning( "ERROR: printing out lambda abstracted proof more than once" );
#ifdef IGNORE_PRINT_MULTI_LAMBDA
      return;
#endif
    }
    printCounter++;
    print_struct( s, ind );
  }
}

void LFSCProof::fillHoles(){
  //if( !is_lambda() ){
    for( int a=0; a<getNumChildren(); a++ ){
      getChild( a )->fillHoles();
    }
  //}
}

#ifdef OPTIMIZE
void LFSCProof::calcL( std::vector< int >& lget, std::vector< int >& lgetu ){
  for( int a=0; a<getNumChildren(); a++ ){
    getChild( a )->calcL( lget, lgetu );
  }
  if( assumeVar!=-1 && std::find( lget.begin(), lget.end(), assumeVar )==lget.end() ){
    lget.push_back( assumeVar );
  }
  if( assumeVarUsed!=-1 && std::find( lgetu.begin(), lgetu.end(), assumeVarUsed )==lgetu.end() ){
    lgetu.push_back( assumeVarUsed );
  }
}
#endif

int LFSCProof::checkOp() {
  if( chOp!=-1 )
    return chOp;
  if( getNumChildren()==1 )
    return getChild( 0 )->checkOp();
  else{
    int ret = -1;
    for( int a=0; a<getNumChildren(); a++ ){
      int o = getChild( a )->checkOp();
      if( a!=-1 ){
        if( ret==-1 )
          ret = a;
        else
          return -1;
      }
    }
    //cout << "fail case " << getNumChildren() << std::endl;
    return ret;
  }
}

LFSCProof* LFSCProof::Make_CNF( const Expr& form, const Expr& reason, int pos )
{
  Expr ec = cascade_expr( form );
#ifdef PRINT_MAJOR_METHODS
  cout << ";[M] CNF " << reason << " " << pos << std::endl;
#endif
  int m = queryM( ec );
  if( m>0 )
  {
    ostringstream os1;
    ostringstream os2;
    RefPtr< LFSCProof > p;
    if( reason==d_or_final_s )
    {
#if 0
      //this is the version that cascades
      //make the proof for the or
      p = LFSCPfVar::Make( "@v", abs(m) );
      //clausify the or statement
      p = LFSCClausify::Make( ec, p.get(), true );
      //return
      return LFSCAssume::Make( m, p.get(), true );
#else
      //this is the version that does not expand the last
      ostringstream oss1, oss2;
      p = LFSCPfVar::Make( "@v", abs(m) );
      for( int a=(form.arity()-2); a>=0; a-- ){
        int m1 = queryM( form[a] );
        oss1 << "(or_elim_1 _ _ ";
        oss1 << ( m1<0 ? "(not_not_intro _ " : "" );
        oss1 << "@v" << abs( m1 );
        oss1 << ( m1<0 ? ") " : " " );
        oss2 << ")";
      }
      p = LFSCProofGeneric::Make( oss1.str(), p.get(), oss2.str() );
      //p = LFSCClausify::Make( form[form.arity()-1], p.get() );
      p = LFSCClausify::Make( queryM( form[form.arity()-1] ), p.get() );
      for( int a=0; a<(form.arity()-1); a++ ){
        p = LFSCAssume::Make( queryM( form[a] ), p.get(), false );
      }
      return LFSCAssume::Make( m, p.get() );
#endif
    }
    else if( reason==d_and_final_s )
    {
#if 1
      //this is the version that does not expand the last
      p = LFSCPfVar::Make( "@v", abs(m) );
      os1 << "(contra _ ";
      for( int a=0; a<form.arity(); a++ ){
        if( a<(form.arity()-1))
          os1 << "(and_intro _ _ ";
        os1 << "@v" << abs( queryM( form[a] ) );
        if( a<(form.arity()-1)){
          os1 << " ";
          os2 << ")";
        }
      }
      os2 << " @v" << abs(m) << ")";
      os1 << os2.str();
      p = LFSCProofGeneric::MakeStr( os1.str().c_str() );
      for( int a=0; a<form.arity(); a++ ){
        p = LFSCAssume::Make( queryM( form[a] ), p.get() );
      }
      return LFSCAssume::Make( m, p.get(), false );
#else
      //this is the version that cascades
      std::vector< Expr > assumes;
      Expr ce = cascade_expr( form );
      Expr curr = ce;
      os1 << "(contra _ ";
      while( curr.getKind()==AND ){
        os1 << "(and_intro _ _ ";
        os1 << "@v" << abs( queryM( curr[0] ) ) << " ";
        os2 << ")";
        assumes.push_back( curr[0] );
        curr = curr[1];
      }
      os2 << " @v" << abs(m) << ")";
      p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );
      for( int a=0; a<(int)assumes.size(); a++ ){
        p = LFSCAssume::Make( queryM( assumes[a] ), p.get() );
      }
      return LFSCAssume::Make( m, p.get(), false );
#endif
    }
    else if( reason==d_imp_s )
    {
      int m1 = queryM( ec[0] );
      int m2 = queryM( ec[1] );
      switch( pos )
      {
      case 0:

        break;
      case 1:

        break;
      case 2:
      {
        //make a proof of the RHS
        ostringstream os;
        os << "(impl_elim _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        //clausify the RHS
        p = LFSCClausify::Make( form[1], p.get() );     //cascadeOr?
        p = LFSCAssume::Make( queryM( ec[0] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get() );
      }
        break;
      }
    }
    else if( reason==d_ite_s )
    {
      int m1 = queryM( ec[0] );
      int m2 = queryM( ec[1] );
      switch( pos )
      {
      case 1:
      {
        ostringstream os;
        os << "(ite_elim_2" << (m1<0 ? "n" : "" );
        os << " _ _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        p = LFSCClausify::Make( form[2], p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get(), false );
        return LFSCAssume::Make( queryM( ec ), p.get() );
      }
        break;
      case 2:
      {
        ostringstream os;
        os << "(not_ite_elim_2 _ _ _ @v" << (m1<0 ? "n" : "" );
        os << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        Expr e = Expr( NOT, form[2] );
        p = LFSCClausify::Make( e, p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get(), false );
        return LFSCAssume::Make( queryM( ec ), p.get(), false );
      }
        break;
      case 3:
      {
        ostringstream os;
        os << "(not_ite_elim_1 _ _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        Expr e = Expr( NOT, form[1] );
        p = LFSCClausify::Make( e, p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get(), false );
      }
        break;
      case 4:
      {
        ostringstream os;
        os << "(ite_elim_1";// << (m1<0 ? "n" : "" );
        os << "  _ _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        p = LFSCClausify::Make( form[1], p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get() );
      }
        break;
      case 5:
      {
        ostringstream os;
        os << "(not_ite_elim_3 _ _ _ @v" << abs( m2 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        Expr e = Expr( NOT, form[2] );
        p = LFSCClausify::Make( e, p.get() );
        p = LFSCAssume::Make( queryM( ec[1] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get(), false );
      }
        break;
      case 6:
      {
        ostringstream os;
        os << "(ite_elim_3";// << (m1<0 ? "n" : "" );
        os << "  _ _ _ @v" << abs( m2 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        p = LFSCClausify::Make( form[2], p.get() );
        p = LFSCAssume::Make( queryM( ec[1] ), p.get(), false );
        return LFSCAssume::Make( queryM( ec ), p.get() );
      }
        break;
      }
    }
    else if( reason==d_iff_s )
    {
      int m1 = queryM( ec[0] );
      int m2 = queryM( ec[1] );
      switch( pos )
      {
      case 0:
      {
        ostringstream os;
        os << "(not_iff_elim_1 _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        p = LFSCClausify::Make( form[1], p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get(), false );
        return LFSCAssume::Make( queryM( ec ), p.get(), false );
      }
        break;
      case 1:
      {
        ostringstream os;
        os << "(not_iff_elim_2 _ _ @v" << abs( m1 ) << " @v" << abs( m ) << ")";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        p = LFSCClausify::Make( Expr( NOT, form[1] ), p.get() );
        p = LFSCAssume::Make( queryM( ec[0] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get(), false );
      }
        break;
      case 2:
      {
        ostringstream os;
        os << "(impl_elim _ _ @v" << abs( m1 ) << "(iff_elim_1 _ _ @v" << abs( m ) << "))";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        //clausify the RHS
        p = LFSCClausify::Make( form[1], p.get() );     //cascadeOr?
        p = LFSCAssume::Make( queryM( ec[0] ), p.get() );
        return LFSCAssume::Make( queryM( ec ), p.get() );
      }
        break;
      case 3:
      {
        ostringstream os;
        os << "(impl_elim _ _ @v" << abs( m2 ) << "(iff_elim_2 _ _ @v" << abs( m ) << "))";
        p = LFSCProofGeneric::MakeStr( os.str().c_str() );
        //clausify the RHS
        p = LFSCClausify::Make( form[0], p.get() );     //cascadeOr?
        p = LFSCAssume::Make( queryM( ec[1] ), p.get() );
        return LFSCAssume::Make( m, p.get() );
      }
        break;
      }
    }
    else if( reason==d_or_mid_s )
    {
      ostringstream os1, os2;
      if( form[pos].isNot() )
        os1 << "(not_not_elim _ ";
      os1 << "(or_elim" << ( (pos==form.arity()) ? "_end" : "" );
      os1 << " _ _ " << pos << " ";
      os2 << ")";
      if( form[pos].isNot() )
        os2 << ")";
      p = LFSCPfVar::Make( "@v", abs( m ) );
      p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );
      Expr ea = Expr( NOT, form[pos] );
      p = LFSCClausify::Make( ea, p.get() );
      return LFSCAssume::Make( m, p.get(), false );
    }
    else if( reason==d_and_mid_s )
    {
      //make a proof of the pos-th statement
      p = LFSCPfVar::Make( "@v", abs( m ) );
      p = LFSCProof::Make_and_elim( form, p.get(), pos, form[pos] );
      p = LFSCClausify::Make( form[pos], p.get() );
      return LFSCAssume::Make( m, p.get() );
    }
  }
  ostringstream ose;
  ose << "CNF, " << reason << " unknown position = " << pos << std::endl;
  print_error( ose.str().c_str(), cout );
  return NULL;
}

LFSCProof* LFSCProof::Make_not_not_elim( const Expr& pf, LFSCProof* p )
{
  if( pf.isNot() && pf[0].isNot() ){
    p = Make_not_not_elim( pf[0][0], p );
    ostringstream os1, os2;
    os1 << "(not_not_elim _ ";
    os2 << ")";
    p = LFSCProofGeneric::Make( os1.str(), p, os2.str() );
  }
  return p;
}

LFSCProof* LFSCProof::Make_mimic( const Expr& pf, LFSCProof* p, int numHoles )
{
  ostringstream os1, os2;
  os1 << "(";
  os1 << pf[0];
  for( int a=0; a<numHoles; a++ )
    os1 << " _";
  os1 << " ";
  os2 << ")";
  return LFSCProofGeneric::Make( os1.str(), p, os2.str() );
}

//input should be in non-cascaded form
LFSCProof* LFSCProof::Make_and_elim( const Expr& form, LFSCProof* p, int n,  const Expr& expected )
{
  Expr e = cascade_expr( form );
  for( int a=0; a<n; a++ ){
    if( e.arity()==2 ){
      e = e[1];
    }else{
      print_error( "WARNING: and elim out of range", cout );
    }
  }
  if( form.arity()>1 )
  {
    ostringstream os1, os2;
    os1 << "(and_elim";
    if( n==form.arity()-1 )
      os1 << "_end";
    os1 << " _ _ " << n << " ";
    os2 << ")";
    return LFSCProofGeneric::Make( os1.str(), p, os2.str() );
  }
  else
  {
    return p;
  }
}

