#include "LFSCUtilProof.h"

#include "LFSCPrinter.h"

//LFSCProofExpr ...

void LFSCProofExpr::initialize(){
  printer->set_print_expr( d_e );
}

void LFSCProofExpr::print_pf( std::ostream& s, int ind ){
  if( isHole )
    s << "_";
  else{
    //HACK (forces unary minus to be printed properly)
    //bool prev_cvc3_mimic = cvc3_mimic;
    //cvc3_mimic = true;
    printer->print_expr( d_e, s );
    //cvc3_mimic = prev_cvc3_mimic;
  }
}

LFSCProofExpr::LFSCProofExpr( const Expr& e, bool isH ){
  d_e = cascade_expr( e );
  initialize();
  isHole = isH;
}

//LFSCPfVar ...

std::map< int, RefPtr< LFSCProof > > LFSCPfVar::vMap;

LFSCProof* LFSCPfVar::Make( const char* c, int v )
{
  ostringstream os;
  os << c << v;
  return new LFSCPfVar( os.str() );
}

LFSCProof* LFSCPfVar::MakeV( int v )
{
  RefPtr< LFSCProof > pf = vMap[v];
  if( !pf.get() ){
    pf = Make( "@v", v );
    vMap[v] = pf.get();
  }
  return pf.get();
}

//LFSCPfLambda ...

void LFSCPfLambda::print_pf( std::ostream& s, int ind )
{
  if( abstVal.get() ){
    lambdaPrintMap[abstVal.get()] = pfV.get();
  }
  s << "(\\ ";
  pfV->print( s );
  //s << " _ (: bottom ";
  s << " ";
  body->print( s );
  s << ")";
  if( abstVal.get() ){
    lambdaPrintMap[abstVal.get()] = NULL;
  }
}

//LFSCProofGeneric ...

long int LFSCProofGeneric::get_length(){
  long int sum = 0;
  for( int a=0; a<(int)d_str.size(); a++ ){
    if( !debug_str )
      sum += d_str[a].length();     
    if( a<(int)d_pf.size() )
      sum += d_pf[a]->get_string_length();
  }
  return sum;
}

void LFSCProofGeneric::print_pf( std::ostream& s, int ind ){
  for( int a=0; a<(int)d_str.size(); a++ ){
    s << d_str[a];
    if( a<(int)d_pf.size() ){
      d_pf[a]->print( s, d_pf.size()<3 ? ind+1 : 0 );
    }
  }
}

LFSCProof* LFSCProofGeneric::Make( string str_pre, LFSCProof* sub_pf, string str_post, bool db_str )
{
  vector< RefPtr< LFSCProof > > d_pfs;
  d_pfs.push_back( sub_pf );
  vector< string > d_strs;
  d_strs.push_back( str_pre );
  d_strs.push_back( str_post );
  return new LFSCProofGeneric( d_pfs, d_strs, db_str );
}

LFSCProof* LFSCProofGeneric::Make( string str_pre, LFSCProof* sub_pf1, LFSCProof* sub_pf2, string str_post, bool db_str )
{
  vector< RefPtr< LFSCProof > > d_pfs;
  d_pfs.push_back( sub_pf1 );
  d_pfs.push_back( sub_pf2 );
  vector< string > d_strs;
  string str_empty(" ");
  d_strs.push_back( str_pre );
  d_strs.push_back( str_empty );
  d_strs.push_back( str_post );
  return new LFSCProofGeneric( d_pfs, d_strs, db_str );
}

LFSCProof* LFSCProofGeneric::MakeStr( const char* c, bool db_str)
{
  vector< RefPtr< LFSCProof > > d_pfs;
  vector< string > d_strs;
  string str( c );
  d_strs.push_back( str );
  return new LFSCProofGeneric( d_pfs, d_strs, db_str );
}

//LFSCPfLet

LFSCPfLet::LFSCPfLet( LFSCProof* letPf, LFSCPfVar* pv, LFSCProof* body,
                      bool isTh, std::vector< int >& fv ) : LFSCProof(), d_letPf( letPf ),
                                                            d_pv( pv ),d_body( body ),d_isTh( isTh ){
  d_letPfRpl = letPf;
  d_pvRpl = pv;
#ifndef IGNORE_LETPF_VARS
  //modify letPf and rpl based on fv
  for(int a=0; a<(int)fv.size(); a++ ){
    ostringstream os1, os2;
    //if( d_isTh ){
      os1 << "(impl_intro _ _ ";
      os2 << ")";
    //}else{
    //}
    RefPtr< LFSCProof > pv1 = LFSCPfVar::Make( "@@v", abs( fv[a] ) );
    RefPtr< LFSCProof > pv2 = LFSCPfVar::MakeV( abs( fv[a] ) );
    d_letPfRpl = LFSCPfLambda::Make( (LFSCPfVar*)pv1.get(), d_letPfRpl.get(), pv2.get() );
    d_letPfRpl = LFSCProofGeneric::Make( os1.str(), d_letPfRpl.get(), os2.str() );
  }
  for( int a=(int)fv.size()-1; a>=0; a-- ){
    ostringstream os1, os2;
    os1 << "(impl_elim _ _ ";
    os2 << ")";
    RefPtr< LFSCProof > pv2 = LFSCPfVar::MakeV( abs( fv[a] ) );
    d_pvRpl = LFSCProofGeneric::Make( os1.str(), pv2.get(), d_pvRpl.get(), os2.str() );
  }
#endif
}

void LFSCPfLet::print_pf( std::ostream& s, int ind ){
  //fill holes if this proof is already abstracted
  if( d_pvRpl.get()!=d_pv.get() ){
    d_letPfRpl->fillHoles();
  }
  s << "(" << (d_isTh ? "th_let_pf _ " : "satlem _ _ _ " );
  d_letPfRpl->print( s );
  s << "(\\ ";
  d_pv->print( s );
  s << " " << endl;
  lambdaPrintMap[d_letPf.get()]=d_pvRpl.get();
  d_body->print( s, ind );
  lambdaPrintMap[d_letPf.get()]=NULL;
  s << "))";
}

void LFSCPfLet::print_struct( std::ostream& s, int ind ){
  s << "(satlem ";
  d_letPf->print_structure( s, ind+1 );
  s << "(\\ ";
  d_pv->print_structure( s );
  s << " ";
  lambdaPrintMap[d_letPf.get()]=d_pv.get();
  d_body->print_structure( s, ind+1 );
  lambdaPrintMap[d_letPf.get()]=NULL;
  s << ")";
}
