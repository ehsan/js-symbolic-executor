#include "LFSCBoolProof.h"

#include "LFSCUtilProof.h"

//LFSCBoolRes ...

void LFSCBoolRes::print_pf( std::ostream& s, int ind ){
  if( d_col ){
    s << "(cRR _ _ _ _ @a" << abs( d_var );
    s << " ";
    d_children[0]->print(s, ind+1);
    s <<" ";
    d_children[1]->print(s, ind+1);
    s <<")";
  }else{
    s <<"(" << (d_var>0 ? "R" : "Q" ) << " _ _ ";
    d_children[0]->print(s, ind+1);
    s <<" ";
    d_children[1]->print(s, ind+1);
    s <<" @b" << abs( d_var ) << ")";
  }
}

void LFSCBoolRes::print_struct( std::ostream& s, int ind ){
  s << "(res " << d_var;
  d_children[0]->print_structure(s, ind+1);
  s <<" ";
  d_children[1]->print_structure(s, ind+1);
  s << ")";
}

LFSCProof* LFSCBoolRes::Make(LFSCProof* pf1, LFSCProof* pf2, int v, bool col){
  if( pf1->isTrivial() )
    return pf2;
  else if( pf2->isTrivial() )
    return pf1;
  else
    return new LFSCBoolRes( pf1, pf2, v, col );
}

int LFSCBoolRes::checkBoolRes( std::vector< int >& clause ){
  std::vector< int > c[2];
  for( int a=0; a<2; a++ ){
    d_children[a]->checkBoolRes( c[a] );
    bool success = false;
    for( int b=0; b<(int)c[a].size(); b++ ){
      if( c[a][b]==d_var ){
        c[a].erase( c[a].begin() + b, c[a].begin() + b + 1 );
        b--;
        success = true;
      }
    }
    if( ! success ){
      print_error( "A check-in failed ", cout );
      return -1;
    }
    for( int b=0; b<(int)c[a].size(); b++ ){
      if( std::find( clause.begin(), clause.end(), c[a][b] )==clause.end() ){
        clause.push_back( c[a][b] );
      }
    }
  }
  return 0;
}

LFSCProof* LFSCBoolRes::Make( LFSCProof* p1, LFSCProof* p2, const Expr& res,
                               const Expr& pf, bool cascadeOr )
{
  Expr cres = cascade_expr( res );
  if( cres.getKind()==OR && cascadeOr )
  {
    return Make( MakeC( p1, cres ), p2, queryM( cres ), true );
  }
  else if( cres.isNot() && cres[0].getKind()==OR && cascadeOr )
  {
    return Make( MakeC( p2, cres[0] ), p1, queryM( cres[0] ), true );
  }
  else if( cres.isNot() && cres[0].isNot() )
  {
    ostringstream ose;
    ose << "Error: Resolving on double negation" << cres;
    print_error( ose.str().c_str(), cout );
  }
  int m = queryM( cres );
  //if( abs( m )==13 ){
  //  cout << endl;
  //  debug_print_res_struct( pf, 0 );
  //}
  //cout << "res on " << cres << std::endl;
  return Make( p1, p2, m, false );
}

LFSCProof* LFSCBoolRes::MakeC( LFSCProof* p, const Expr& res ){
  if( res.isOr() ){
    ostringstream os1, os2;
    int m = queryM( res[0] );
    os1 << "(c" << (m>0 ? "R" : "Q" );
    os1 << " _ _ _ _ @a" << abs( m );
    os2 << ")";
    return LFSCProofGeneric::Make( os1.str(), MakeC( p, res[1] ), os2.str() );
  }else{
    ostringstream os1, os2;
    int m = queryM( res );
    os1 << "(c" << (m>0 ? "R" : "Q" );
    os1 << "0 _ _ _ @a" << abs( m );
    os2 << ")";
    return LFSCProofGeneric::Make( os1.str(), p, os2.str() );
  }
}


// LFSCClausify ...

void LFSCClausify::print_pf( std::ostream& s, int ind ){
  s << "(clausify_form" << (d_var<0 ? "_not" : "") << " _ _ @a" << abs( d_var ) << " ";
  d_pf->print( s );
  s << ")";
}

//p should prove e, return a proof that is the clausal form for e
LFSCProof* LFSCClausify::Make( const Expr& e, LFSCProof* p, bool cascadeOr )
{
  if( cascadeOr ){
    std::vector< Expr > exprs;
    Expr end;
    if( e.arity()>0 )
      end = cascade_expr( e[e.arity()-1] );
    return Make_i( cascade_expr( e ), p, exprs, end );
  }else{
    return Make( queryM( e ), p );
  }
}

LFSCProof* LFSCClausify::Make_i( const Expr& e, LFSCProof* p, std::vector< Expr >& exprs, const Expr& end )
{
  if( e.getKind()==OR && e!=end )
  {
    exprs.push_back( e[0] );
    return LFSCAssume::Make( queryM( e[0] ), Make_i( e[1], p, exprs, end ), false );
  }
  else
  {
    for( int a=0; a<(int)exprs.size(); a++ ){
      ostringstream os1, os2;
      os1 << "(or_elim_1 _ _ ";
      int m = queryM( exprs[a] );
      //introduce double negation to satisfy or_elim requirement
      os1 << ( m<0 ? "(not_not_intro _ " : "" );
      os1 << "@v" << abs( m );
      os1 << ( m<0 ? ")" : "" );
      os1 << " ";
      os2 << ")";
      p = LFSCProofGeneric::Make( os1.str(), p, os2.str() );
    }
    return Make( queryM( e ), p );
  }
}

// LFSCAssume ...

void LFSCAssume::print_pf( std::ostream& s, int ind ){
  int m = d_assm ? d_var : -d_var;
  if( d_type==3 )
    s << "(as" << (m>0 ? "t" : "f") << " _ _ _ @a" << abs( m );
  else
    s << "(th_as" << (m>0 ? "t" : "f") << " _ ";
  s << " (\\ @v" << abs( m ) << " ";
  d_pf->print( s );
  s << "))";
}

void LFSCAssume::print_struct( std::ostream& s, int ind ){
  s << "(as " << ( d_assm ? d_var : -d_var );
  d_pf->print_structure( s, ind+1 );
  s << ")";
}
