#include "TReturn.h"

#include "LFSCUtilProof.h"
#include "LFSCLraProof.h"
#include "LFSCBoolProof.h"
#include "LFSCPrinter.h"

TReturn::TReturn(LFSCProof* lfsc_pf, std::vector<int>& L, std::vector<int>& Lused, Rational r, bool hasR, int pvY):
                d_lfsc_pf(lfsc_pf), d_c( r ), d_provesY(pvY){
  d_hasRt = hasR;
  for( int a=0; a<(int)L.size(); a++ )
    d_L.push_back( L[a] );
  for( int a=0; a<(int)Lused.size(); a++ )
    d_L_used.push_back( Lused[a] );

#ifdef DEBUG_MEM_STATS
  static int counter = 0;
  counter++;
  cout << "make a tret " << counter << std::endl;
#endif
  lcalced = false;
}

Rational TReturn::mult_rational( TReturn* lhs )
{
  if( !hasRational() && lhs->hasRational() )
    return lhs->mult_rational( this );
  else if( hasRational() ){
    if( lhs->hasRational() )
      return d_c*lhs->d_c;
    else
      return d_c;
  }else
    return lhs->d_c;
}

void TReturn::getL( std::vector< int >& lget, std::vector< int >& lgetu ){
#ifndef OPTIMIZE
  std::vector< int >::iterator i;
  for( int a=0; a<(int)d_L.size(); a++ ){
    i = std::find( lget.begin(), lget.end(), d_L[a] );
    if( i==lget.end() ){
      lget.push_back( d_L[a] );
    }
  }
  for( int a=0; a<(int)d_L_used.size(); a++ ){
    i = std::find( lgetu.begin(), lgetu.end(), d_L_used[a] );
    if( i==lgetu.end() ){
      lgetu.push_back( d_L_used[a] );
    }
  }
#endif
}

#ifdef OPTIMIZE
void TReturn::calcL( std::vector< int >& lget, std::vector< int >& lgetu ){
  if( !lcalced ){
    d_L.clear();
    d_L_used.clear();
    d_lfsc_pf->calcL( d_L, d_L_used );
    lcalced = true;
  }
  std::vector< int >::iterator i;
  for( int a=0; a<(int)d_L.size(); a++ ){
    i = std::find( lget.begin(), lget.end(), d_L[a] );
    if( i==lget.end() ){
      lget.push_back( d_L[a] );
    }
  }
  for( int a=0; a<(int)d_L_used.size(); a++ ){
    i = std::find( lgetu.begin(), lgetu.end(), d_L_used[a] );
    if( i==lgetu.end() ){
      lgetu.push_back( d_L_used[a] );
    }
  }
}
#endif


// make it so that the two TReturns agree on what they are proving
// t1 proves pf1, Y( pf1 ), or Y2( pf1 )
// t2 proves pf2, Y( pf2 ), or Y2( pf2 )
// on return, t1->d_proveY should equal t2->d_proveY
int TReturn::normalize_tret( const Expr& pf1, TReturn*& t1, const Expr& pf2, TReturn*& t2, bool rev_pol )
{
  if( t1->getProvesY()!=t2->getProvesY() )
  {
    if( t1->getProvesY()>t2->getProvesY() )
      return normalize_tret( pf2, t2, pf1, t1, rev_pol );
    else
    {
      if( debug_conv )
        cout << "normalizing proofs " << t1->getProvesY() << " " << t2->getProvesY() << " " << rev_pol << std::endl;

      if( t1->getProvesY()==0 && t2->getProvesY()==2 )
        normalize_tr( pf1, t1, 2, rev_pol );
      if( t1->getProvesY()==1 && t2->getProvesY()==2 )
        normalize_tr( pf1, t1, 2, rev_pol );
      if( t1->getProvesY()==0 && t2->getProvesY()==1 ){
        if( normalize_tr( pf1, t1, 1, rev_pol, false )==-1 ){     //try to go 0 to 1 (optional)
          if( normalize_tr( pf2, t2, 0, rev_pol, false )==-1 ){   //try to go 1 to 0 immediately (optional)
            normalize_tr( pf1, t1, 2, rev_pol );
            normalize_tr( pf2, t2, 2, rev_pol );
          }
        }
      }
      if( t2->getProvesY()==3 ){
        normalize_tr( pf1, t1, 3, rev_pol );
      }

      if( t1->getProvesY()!=t2->getProvesY() ){
        ostringstream os;
        os << "ERROR:normalize_tret: Could not normalize proofs " << t1->getProvesY() << " " << t2->getProvesY() << std::endl;
        os << pf1[0] << " " << pf2[0] << std::endl;
        print_error( os.str().c_str(), cout );
        return -1;
      }else{
        return t1->getProvesY();
      }
    }
  }
  return t1->getProvesY();
}
 
int TReturn::normalize_tr( const Expr& pf1, TReturn*& t1, int y, bool rev_pol, bool printErr )
{
  TReturn* torig = t1;

  int chOp = t1->getLFSCProof()->getChOp();
  std::vector< int > emptyL;
  std::vector< int > emptyLUsed;
  t1->getL( emptyL, emptyLUsed );

  if( t1->getProvesY()!=y )
  {
    if( debug_conv ){
      cout << "normalizing tr " << t1->getProvesY() << " to " << y << " rev_pol = " << rev_pol << std::endl;
    }
    Expr e;
    if( what_is_proven( pf1, e ) )
    {
      e = queryElimNotNot( e );
      if( rev_pol ){
        if( e.isIff() ){
          //cout << "Warning: rev_pol called on IFF, 0 normalize to " << y << std::endl;
          e = Expr( IFF, e[1], e[0] );
        }else if( e.isImpl() ){
          e = Expr( IMPLIES, e[1], e[0] );
        }
      }
      Expr eb = queryAtomic( e, true );
      if( y==3 )
      {
        if( t1->getProvesY()!=2 ){
          if( normalize_tr( pf1, t1, 2, rev_pol )==-1 ){
            return -1;
          }
        }
        if( e.isIff() ){
          e = Expr( IMPLIES, e[0], e[1] );
        }
        //clausify what t1 is proving
        t1 = new TReturn( LFSCClausify::Make( e, t1->getLFSCProof() ), emptyL, emptyLUsed, nullRat, false, 3 );
      }
      else if( y==1 )
      {
        if( t1->getProvesY()==0 || t1->getProvesY()==2 ){
          if( can_pnorm( eb ) )
          {
            t1 = new TReturn( LFSCLraPoly::Make( e, t1->getLFSCProof() ), emptyL, emptyLUsed,
                              t1->getRational(), t1->hasRational(), 1 );
          }else{
            //cout << "nrt kind = " << kind_to_str( eb.getKind() ) << std::endl;
          }
        }
      }
      else if( y==0 )
      {
        if( is_eq_kind( eb.getKind() ) ){
          normalize_to_tf( e, t1, 0 );
        }else if( e[0]==e[1] ){
          ostringstream os1, os2;
          os1 << "(iff_refl ";
          RefPtr< LFSCProof > p = LFSCProofExpr::Make( e[0] );
          os2 << ")";
          t1 = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ),
                            emptyL, emptyLUsed, nullRat, false, 0 );
        }else{
          if( t1->getProvesY()==1 ){
#ifdef PRINT_MAJOR_METHODS
            cout << ";[M]: Normalize 1 to 0, iff" << std::endl;
#endif
            if( e[1].isFalse() )
            {
              Expr ea = Expr( NOT, e[0] );
              normalize_to_tf( ea, t1, 0 );
              ostringstream os1, os2;
              os1 << "(" << ( e[0].getKind()==NOT ? "not_to_iff" : "iff_not_false" );
              os1 << " _ ";
              os2 << ")";
              t1 = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), os2.str() ), 
                                emptyL, emptyLUsed, nullRat, false, 0 );
            }
            else if( e[1].isTrue() )
            {
              normalize_to_tf( e[0], t1, 0 );
              ostringstream os1, os2;
              os1 << "(iff_true _ ";
              os2 << ")";
              t1 = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), os2.str() ), 
                                emptyL, emptyLUsed, nullRat, false, 0 );
            }
            else if( printErr )
            {
              TReturn* torg = new TReturn( LFSCPfVar::Make( "@V", 0 ), emptyL, emptyLUsed,
                                          t1->getRational(), t1->hasRational(), t1->getProvesY() );
              TReturn *ti1, *ti2;
              TReturn* to = torg;
              if( normalize_tr( pf1, to, 2, rev_pol ) )
              {
                ti1 = to;
                to = torg;
                if( normalize_tr( pf1, to, 2, !rev_pol ) )
                {
                  ti2 = to;
                  ostringstream os1, os2, os3, os4;
                  os1 << "(impl_elim _ _ ";
                  os2 << "(impl_intro _ _ (\\ @V0 (iff_intro _ _ ";
                  os3 << " ";
                  os4 << "))))";
                  std::vector< RefPtr< LFSCProof > > pfs;
                  pfs.push_back( t1->getLFSCProof() );
                  pfs.push_back( ti1->getLFSCProof() );
                  pfs.push_back( ti2->getLFSCProof() );
                  std::vector< string > strs;
                  strs.push_back( os1.str() );
                  strs.push_back( os2.str() );
                  strs.push_back( os3.str() );
                  strs.push_back( os4.str() );
                  t1 = new TReturn( LFSCProofGeneric::Make( pfs, strs ), emptyL, emptyLUsed, nullRat, false, 0 );
                }
              }
            }
          }
        }
      }
      else if( y==2 )
      {
        if( t1->getProvesY()==0 )
        {
          RefPtr< LFSCProof > p;
          if( e.isIff() ){
            ostringstream os1, os2;
            os1 << "(iff_elim_1 _ _ ";
            os2 << ")";
            p = LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), os2.str() );
          }else{
            //cout << "actually I can just drop it " << e << std::endl;
            p = t1->getLFSCProof();
          }
          t1 = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 2 );
        }
        else if( t1->getProvesY()==1 )
        {
          if( is_eq_kind( eb.getKind() ) ){
            normalize_to_tf( e, t1, 2 );
          }else if( e.isIff() || e.isImpl() ){
            Expr eatom1 = queryAtomic( e[0] );
            Expr eatom2 = queryAtomic( e[1] );
            //Expr ebase1 = queryAtomic( eatom1, true );
            //Expr ebase2 = queryAtomic( eatom2, true );
            int val1 = queryM( e[0] );
            int val2 = queryM( e[1] );
            int k1 = eatom1.getKind();
            int k2 = eatom2.getKind();

            if( e[0]==e[1] ){
              ostringstream os;
              os << "(impl_refl_atom" << (val1<0 ? "_not" : "" );
              os << " _ _ @a" << abs( val1 ) << ")";
              //d_formulas_printed[queryAtomic( e[0], true )] = true;
              t1 = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str()),
                                emptyL, emptyLUsed, nullRat, false, 2 );
            }else if( eatom2.isFalse() || eatom2.isTrue() ){
              if( eatom1.getKind()==eatom2.getKind() )
              {
#ifdef PRINT_MAJOR_METHODS
                cout << ";[M]: Normalize 1 to 2, iff/impl double logical iff" << std::endl;
#endif
                if( e[0]!=e[1] ){
                  ostringstream ose;
                  ose << "Warning: normalize logical atoms, not equal ";
                  ose << e[0] << " " << e[1] << std::endl;
                  print_error( ose.str().c_str(), cout );
                }
                ostringstream os;
                os << "impl_refl_" << ( eatom2.isFalse() ? "false" : "true" );
                t1 = new TReturn( LFSCProofGeneric::MakeStr(os.str().c_str()),
                                  emptyL, emptyLUsed, nullRat, false, 2 );
              }
              else if( eatom2.isTrue() )
              {
                normalize_to_tf( e[0], t1, 2 );
                ostringstream oss1, oss2;
                oss1 << "(iff_true_impl _ ";
                oss2 << ")";
                t1 = new TReturn( LFSCProofGeneric::Make( oss1.str(), t1->getLFSCProof(), oss2.str() ),
                                  emptyL, emptyLUsed, nullRat, false, 2 );
              }
              else if( eatom2.isFalse() )
              {
#ifdef PRINT_MAJOR_METHODS
               // cout << ";[M]: Normalize 1 to 2, iff/impl logical iff" << std::endl;
#endif
                //make proof for assumption
                RefPtr< LFSCProof > p = LFSCPfVar::Make( "@v", abs( val1 ) );
                p = LFSCLraPoly::Make( e[0], p.get() );

                p = LFSCLraAdd::Make( p.get(), t1->getLFSCProof(),
                                      get_normalized( k1 ),
                                      get_normalized( k1, true ) );
                p = LFSCLraContra::Make( p.get(), is_comparison( k1 ) ? (int)GT : (int)DISTINCT );

                ostringstream oss1, oss2;
                //oss1 << std::endl << "this is a normalization proof of " << e[0] << "->" << e[1] << std::endl;
                //oss1 << "or a proof of " << eatom1 << " -> " << eatom2 << std::endl;
                oss1 << "(impl_intro"; // << ( eatom2.isTrue() ? "_not" : "" );
                oss1 << " _ _ (\\ @v" << abs( val1 ) << " ";
                oss1 << "(bottom_elim ";
                printer->print_formula( e[1], oss1 );
                oss1 << " ";

                oss2 << ")))";
                p = LFSCProofGeneric::Make( oss1.str(), p.get(), oss2.str() );
                //p = LFSCAssume::Make( val1, p.get(), false, 1 );

                t1 = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 2 );
              }
            }
            else if( is_eq_kind( k1 ) && is_eq_kind( k2 ) )
            {
#ifdef PRINT_MAJOR_METHODS
              //cout << ";[M]: Normalize 1 to 2, iff/impl" << std::endl;
#endif
              RefPtr< LFSCProof > p;
              //assume1
              ostringstream os1, os2;
              //os1 << "this is a normalization proof of " << e[0] << "->" << e[1] << std::endl;
              //os1 << "or a proof of " << eatom1 << " -> " << eatom2 << std::endl;
              os1 << "(impl_intro";
              os1 << " _ _ (\\ ";
              os1 << "@v" << abs( val1 ) << " ";
              os2 << "))";

              //make proof for assumption
              RefPtr< LFSCProof > p1 = LFSCPfVar::Make( "@v", abs( val1 ) );
              RefPtr< LFSCProof > p2 = LFSCPfVar::Make( "@v", abs( val2 ) );

              //convert to polynomial proofs
              p1 = LFSCLraPoly::Make( e[0], p1.get() );
              Expr ea2 = Expr( NOT, e[1] );
              p2 = LFSCLraPoly::Make( ea2, p2.get() );

              if( t1->hasRational() ){
                if( rev_pol )
                  p2 = LFSCLraMulC::Make( p2.get(), t1->getRational(), get_normalized( k2, true ) );
                else
                  p1 = LFSCLraMulC::Make( p1.get(), t1->getRational(), get_normalized( k1 ) );
              }

              p = LFSCLraAdd::Make( p1.get(), p2.get(),
                                    get_normalized( k1 ),
                                    get_normalized( k2, true ) );

              p = LFSCLraSub::Make( p.get(), t1->getLFSCProof(),
                                    is_comparison( k1 ) ? (int)GT : (int)DISTINCT, EQ );
              p = LFSCLraContra::Make( p.get(),
                                       is_comparison( k1 ) ? (int)GT : (int)DISTINCT );

              p = LFSCAssume::Make( val2, p.get(), false, 1 );   

              p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );

              t1 = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 2 );
            }
            else
            {
              ostringstream ose;
              ose << "NTret 12 could not handle " << eatom1 << " " << eatom2;
              print_error( ose.str().c_str(), cout );
            }
          }
        }
      }
    }
  }
  t1->getLFSCProof()->setChOp( chOp );
  if( t1->getProvesY()!=y )
  {
    if( printErr || debug_conv ){
      ostringstream ose;
      ose << "Failed normalize_tr " << t1->getProvesY() << " " << y << std::endl;
      Expr e;
      if( what_is_proven( pf1, e ) )
       ose << "proven_expr = " << e << std::endl;
      print_error( ose.str().c_str(), cout );
    }
    return -1;
  }
  else
  {
#ifdef IGNORE_NORMALIZE
  t1 = new TReturn( torig->getLFSCProof(), emptyL, emptyLUsed,
                    torig->getRational(), torig->hasRational(), y );
  t1->getLFSCProof()->setChOp( chOp );
  return t1->getProvesY();
#else
    return t1->getProvesY();
#endif
  }
}

void TReturn::normalize_to_tf( const Expr& e, TReturn*& t1, int y )
{
  int chOp = t1->getLFSCProof()->getChOp();
  if( t1->getProvesY()!=1 ){
    ostringstream ose;
    ose << "Bad mode for norm to tf " << t1->getProvesY() << std::endl;
    print_error( ose.str().c_str(), cout );
  }
  std::vector< int > emptyL;
  std::vector< int > emptyLUsed;
  t1->getL( emptyL, emptyLUsed );

  if( t1->getLFSCProof()->AsLFSCLraPoly() && false )
  {
#ifdef PRINT_MAJOR_METHODS
    cout << ";[M]: Normalize 1 to " << y << ", simplify case" << std::endl;
#endif
    t1 = new TReturn( t1->getLFSCProof()->getChild( 0 ), emptyL, emptyLUsed, nullRat, false, y );
  }
  else
  {

#ifdef PRINT_MAJOR_METHODS
    cout << ";[M]: Normalize 1 to " << y << ", iff/impl, atom" << std::endl;
#endif

    Expr eatom = queryAtomic( e );
    int val = queryM( e );
    int knd = eatom.getKind();

    //make proof for assumption
    RefPtr< LFSCProof > p = LFSCPfVar::Make( "@v", abs( val ) );
    //convert to polynomial proof
    Expr ea = Expr( NOT, e );
    p = LFSCLraPoly::Make( ea, p.get() );

    p = LFSCLraContra::Make(
          LFSCLraAdd::Make( p.get(), t1->getLFSCProof(),
                            get_normalized( knd, (val<0) ),
                            get_normalized( knd, !(val<0) ) ),
          is_comparison( knd ) ? (int)GT : (int)DISTINCT );

    p = LFSCAssume::Make( val, p.get(), false, 1 );

    //ostringstream os1, os2;
    //os1 << "This is the atomization of " << e << ":";
    //os2 << " ";
    //p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );

    //we have concluded e
    t1 = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, y );
  }
  t1->getLFSCProof()->setChOp( chOp );
}
