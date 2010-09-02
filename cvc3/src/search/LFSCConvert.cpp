#include "LFSCConvert.h"

#include "LFSCUtilProof.h"
#include "LFSCBoolProof.h"
#include "LFSCLraProof.h"

std::map< Expr, int > vMap;

LFSCConvert::LFSCConvert( int lfscm )
{
  nodeCount = 0;
  nodeCountTh = 0;
  unodeCount = 0;
  unodeCountTh = 0;
  ignore_theory_lemmas = lfsc_mode==22;
}

void LFSCConvert::convert( const Expr& pf ) 
{ 
  TReturn* tfinal = cvc3_to_lfsc( pf, false, false ); 
  pfinal = tfinal->getLFSCProof();

  //print out sat_lem if we are in clausal form
  if( tfinal->getProvesY()==3 ){
    ostringstream os1, os2;
    os1 << "(satlem _ _ _ ";
    os2 << "(\\ @done @done))" << endl;
    pfinal = LFSCProofGeneric::Make( os1.str(), pfinal.get(), os2.str() );
  }

  //print out all necessary proof let's
  pfinal = make_let_proof( pfinal.get() );

  //double ratio = (double)( nodeCountTh )/double( nodeCount + nodeCountTh );
  //cout << "Theory Node ratio : " << ratio << endl;
  //cout << "Node Count      : " << nodeCount << endl;
  //cout << "Th Node Count   : " << nodeCountTh << endl;
  //cout << "Total Count     : " << ( nodeCount + nodeCountTh ) << endl;
  //cout << (double)( nodeCountTh )/double( nodeCount + nodeCountTh ) << endl;
  //cout << "uNode Count     : " << unodeCount << endl;
  //cout << "Th uNode Count  : " << unodeCountTh << endl;
  //cout << "LFSC proof count: " << LFSCProof::get_proof_counter() << endl;
  //cout << "getNumNodes     : " << getNumNodes( pf, false ) << endl;
  //nnode_map.clear();
  //cout << "getNumNodes(rc) : " << getNumNodes( pf, true ) << endl;
  //cout << "map size 1      : " << (int)d_th_trans_map[1].size() << endl;
  //cout << "map size 2      : " << (int)d_th_trans_map[0].size() << endl;
  //std::map< Expr, int >::iterator vmIt = vMap.begin();
  //while( vmIt != vMap.end() ){
  //  cout << (*vmIt).first << ": " << (*vmIt).second << endl;
  //  ++vmIt;
  //}
  //exit( 0 );
}

// helper method to identify axioms of the form |- 0 = 0
bool LFSCConvert::isTrivialTheoryAxiom(const Expr& expr, bool checkBody){
  if( expr[0]==d_plus_predicate_str || expr[0]==d_right_minus_left_str ||
      expr[0]==d_minus_to_plus_str || expr[0]==d_mult_ineqn_str ||
      expr[0]==d_canon_mult_str || expr[0]==d_canon_plus_str ||
      expr[0]==d_flip_inequality_str || expr[0]==d_negated_inequality_str ||
      expr[0]==d_rewrite_eq_symm_str || expr[0]==d_refl_str ||
      expr[0]==d_mult_eqn_str || expr[0]==d_canon_invert_divide_str ||
      expr[0]==d_rewrite_eq_refl_str || expr[0]==d_uminus_to_mult_str ||
      expr[0]==d_rewrite_not_true_str || expr[0]==d_rewrite_not_false_str ||
      expr[0]==d_int_const_eq_str ){
    Expr pe;
    Expr yexpr;
    if( !checkBody || ( what_is_proven( expr, pe ) && getY( pe, yexpr ) ) ){
      return true;
    }else{
      //cout << "Trivial theory axiom with bad arguments : " << expr[0] << std::endl;
    }
  }
  return false;
  //FIXME: should rewrite_not_true be used in theory lemma?    expr==d_rewrite_not_true_str
}

bool LFSCConvert::isTrivialBooleanAxiom(const Expr& expr)
{
  return ( expr==d_rewrite_not_not_str );
}


// *****NOTE that these rules must have a subproof expr[2]
bool LFSCConvert::isIgnoredRule(const Expr& expr)
{
  return ( expr==d_iff_not_false_str || expr==d_iff_true_str ||
           expr==d_iff_false_elim_str || expr==d_iff_true_elim_str ||
           expr==d_not_not_elim_str || expr==d_not_to_iff_str );
}

TReturn* LFSCConvert::cvc3_to_lfsc(const Expr& pf, bool beneath_lc, bool rev_pol){
  if( beneath_lc )
    nodeCountTh++;
  else
    nodeCount++;
  if( lfsc_mode==5){
    cvc3_mimic = cvc3_mimic_input || !beneath_lc;
  }
  int cvcm = cvc3_mimic ? 1 : 0;
  TReturn* tRetVal = NULL;
  //if( !tRetVal && cvcm==0 ){
  //  tRetVal = d_th_trans_map[1][pf];
  //}
  if( d_th_trans_map[cvcm].find( pf )!=d_th_trans_map[cvcm].end() ){
    tRetVal = d_th_trans_map[cvcm][pf];
    if( d_th_trans_lam[cvcm].find( tRetVal )==d_th_trans_lam[cvcm].end() ){
      if( debug_conv )
        cout << "set th_trans" << std::endl;
      //set this TReturn to be lambda'ed into a let proof
      d_th_trans_lam[cvcm][tRetVal] = true;
    }
    return tRetVal;
  }

  if( beneath_lc )
    unodeCountTh++;
  else
    unodeCount++;

  //if( (unodeCountTh + unodeCount)%10000==0 )
  //  cout << unodeCount << " " << unodeCountTh << endl;
  //if( pf.isSelected() )
  //  std::cout << "already did this one?" << std::endl;

  if( vMap.find( pf[0] )==vMap.end() ){
    vMap[ pf[0] ] = 0;
  }
  vMap[ pf[0] ]++;


  std::vector< int > emptyL;
  std::vector< int > emptyLUsed;
  int yMode = -2;
  ostringstream ose;
  if( debug_conv ){
    cout << "handle ";
    pf[0].print();
  }
  Expr pfMod;
  int pfPat = get_proof_pattern( pf, pfMod );
  if( pfPat==0 )
  {
    if (pf[0] == d_CNF_str ){
      RefPtr< LFSCProof > p = LFSCProof::Make_CNF( pf[2], pf[1], pf[4].getRational().getNumerator().getInt() );
      if( p.get() )
      {
        tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
      }
    }
    else if( pf[0] == d_CNFITE_str ){
      if( pf[5].isRational() ){
        RefPtr< LFSCProof > p = LFSCProof::Make_CNF( pf[1], d_ite_s, pf[5].getRational().getNumerator().getInt() );
        if( p.get() ){
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
        }
      }
    }else if( pf[0] == d_cnf_add_unit_str ){
      TReturn* t = cvc3_to_lfsc( pf[2] );
      yMode = TReturn::normalize_tr( pf[2], t, 3 );
      if( yMode==3 ){
        tRetVal = t;
      }
    }
    else if( pf[0] == d_cnf_convert_str ){
      if( pf.arity()>3 ){
        if( ignore_theory_lemmas && pf[3][0]==d_learned_clause_str ){
          TReturn* t = make_trusted( pf );
          tRetVal = new TReturn( LFSCClausify::Make( pf[1], t->getLFSCProof(), true ), emptyL, emptyLUsed, nullRat, false, 3 );
        }else{
          TReturn* t = cvc3_to_lfsc( pf[3],beneath_lc, rev_pol);
          if( TReturn::normalize_tr( pf[3], t, 3, rev_pol )==3 ){
            RefPtr< LFSCProof > p = t->getLFSCProof();
            tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
          }
        }
      }
    }
    else if( pf[0] == d_bool_res_str ){
      //ajr_debug_print( pf );
      TReturn* t1 = cvc3_to_lfsc( pf[2],beneath_lc, rev_pol);
      TReturn* t2 = cvc3_to_lfsc( pf[3],beneath_lc, rev_pol);
      //t1->getL( emptyL, emptyLUsed );
      //t2->getL( emptyL, emptyLUsed );
      TReturn::normalize_tr( pf[2], t1, 3, rev_pol );
      TReturn::normalize_tr( pf[3], t2, 3, rev_pol );
      if( t1->getProvesY()==3 && t2->getProvesY()==3 ){
        tRetVal = new TReturn( LFSCBoolRes::Make( t1->getLFSCProof(), t2->getLFSCProof(), pf[1], pf ),
                            emptyL, emptyLUsed, nullRat, false, 3 );
      }
    }
    else if( pf[0] == d_minisat_proof_str ){
      tRetVal = cvc3_to_lfsc( pf[2] );
    }
    else if(pf[0]==d_assump_str){      //assumptions rule
      Expr ce = cascade_expr( pf[1] );
      int val = queryM( ce );
      RefPtr< LFSCProof > p;
      yMode = 0;
      if( d_assump_map.find( ce ) != d_assump_map.end() ){
        //cout << "This is an assumption: " << pf[1] << std::endl;
        p = LFSCPfVar::Make( "@F", abs( val ) );
        if( !cvc3_mimic ){
#ifndef LRA2_PRIME
          p = LFSCProof::Make_not_not_elim( pf[1], p.get() );
#endif
        }
      }else if( beneath_lc ){
        p = LFSCPfVar::MakeV( abs( val ) );
        if( cvc3_mimic ){
          //ostringstream os1, os2;
          //os1 << "(spec ";
          //RefPtr< LFSCProof > ps = LFSCProofExpr::Make( pf[1] );
          //os2 << ")";
          //p = LFSCProofGeneric::Make( os1.str(), p.get(), ps.get(), os2.str() );
          d_formulas_printed[queryAtomic( ce, true )] = true;
        }
#ifdef OPTIMIZE
        p->assumeVarUsed = val;
#else
        emptyLUsed.push_back( val );
#endif
      }else{
        ostringstream os;
        os << "WARNING: Assuming a trusted formula: " << ce << std::endl;
        print_error( os.str().c_str(), cout );
        int valT = queryM( ce, true, true );
        p = LFSCPfVar::Make( "@T", abs( valT ) );
      }
      if( beneath_lc ){
#ifdef OPTIMIZE
        p->assumeVar = val;
#else
        emptyL.push_back( val );
#endif
        if( !cvc3_mimic ){
          Expr ey;
          if( getY( ce, ey ) ){
            p = LFSCLraPoly::Make( ce, p.get() );
            yMode = 1;
          }else{
            ostringstream os;
            os << "WARNING: Beneath a learned clause and Y is not defined for assumption " << pf[1] << std::endl;
            print_error( os.str().c_str(), cout );
          }
        }
      }
      tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, yMode );
    }
    else if( pf[0] == d_iff_trans_str ){
      TReturn* t1 = cvc3_to_lfsc(pf[4],beneath_lc, rev_pol);
#ifdef LRA2_PRIME
      if( ( isTrivialBooleanAxiom( pf[5][0] ) || pf[5][0]==d_rewrite_not_true_str ) && !cvc3_mimic  && t1->getProvesY()==1 ){ 
#else
      if( ( isTrivialBooleanAxiom( pf[5][0] ) || pf[5][0]==d_rewrite_not_true_str ) && !cvc3_mimic  ){
#endif
        tRetVal = t1;
      }else{
        TReturn* t2 = cvc3_to_lfsc(pf[5],beneath_lc, rev_pol);
        t1->getL( emptyL, emptyLUsed );
        t2->getL( emptyL, emptyLUsed );
        yMode = TReturn::normalize_tret( pf[4], t1, pf[5], t2, rev_pol );
        //case for arithmetic simplification
        if( yMode==1 )
        {
          int knd2 = queryAtomic( pf[2] ).getKind();
          int knd3 = queryAtomic( pf[3] ).getKind();
          //if we have an equation on the RHS
          if( is_eq_kind( knd3 ) )
          {
            RefPtr< LFSCProof > lfsc_pf = t1->getLFSCProof();
            if( t2->hasRational() )
              lfsc_pf = LFSCLraMulC::Make(t1->getLFSCProof(), t2->getRational(), EQ);
            LFSCLraAdd::Make( lfsc_pf.get(), t2->getLFSCProof(), EQ, EQ);

            Rational newR = t1->mult_rational( t2 );
            tRetVal = new TReturn(lfsc_pf.get(), emptyL, emptyLUsed, t1->mult_rational( t2 ), t1->hasRational() || t2->hasRational(),1);
          }
          else if( knd3==FALSE_EXPR || knd3==TRUE_EXPR )
          {
#ifdef PRINT_MAJOR_METHODS
            cout << ";[M]: iff_trans, logical " << (knd3==TRUE_EXPR) << std::endl;
#endif
            RefPtr< LFSCProof > p;
            if ( knd3==TRUE_EXPR ){
              p = LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(), EQ, is_eq_kind( knd2 ) ? get_normalized( knd2, true ) : EQ );
            }else{
              p = LFSCLraSub::Make( t2->getLFSCProof(), t1->getLFSCProof(), is_eq_kind( knd2 ) ? get_normalized( knd2, true ) : EQ, EQ );
            }
            if( t1->hasRational() ){
              Rational r = 1/t1->getRational();
              p = LFSCLraMulC::Make( p.get(), r, is_eq_kind( knd2 ) ? get_normalized( knd2, true ) : EQ );
            }
            tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
          }
        }else if( yMode == 3 ){
//#ifdef PRINT_MAJOR_METHODS
//           cout << ";[M]: iff_trans, boolean " << std::endl;
//#endif
//          //resolving on the middle formula
//          RefPtr< LFSCProof > p;
//          if( rev_pol ){
//            p = LFSCBoolRes::Make( t2->getLFSCProof(), t1->getLFSCProof(), pf[2], pf );
//          }else{
//            p = LFSCBoolRes::Make( t1->getLFSCProof(), t2->getLFSCProof(), pf[2], pf );
//          }
          //tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, 1, 1, 3 );
        }else if( yMode == 0 || yMode==2 ){
          ostringstream os1;
          os1 << "(" << (yMode==0 ? "iff" : "impl" ) << "_trans _ _ _ ";
          //if( yMode==2 && t1->getLFSCProof()->get_string_length()<100 ){
          //  os1 << "[";
          //  t1->getLFSCProof()->print( os1, 0 );
          //  os1 << "]";
          //}
          ostringstream os2;
          os2 << ")";

          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ),
                              emptyL, emptyLUsed, nullRat, false, yMode );
        }
      }
    }
    else if (pf[0] == d_iff_mp_str ){   //iff_mp rule
      TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc);
#ifdef LRA2_PRIME
      if( isTrivialBooleanAxiom( pf[4][0] ) && !cvc3_mimic && t1->getProvesY()==1 ){ 
#else
      if( isTrivialBooleanAxiom( pf[4][0] ) && !cvc3_mimic ){
#endif
        tRetVal = t1;
      }else{
        TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc);
        t1->getL( emptyL, emptyLUsed );
        t2->getL( emptyL, emptyLUsed );
        if( t1->getProvesY()==1 && t2->getProvesY()==1 )
        {
          yMode = 1;
          int knd = queryAtomic( pf[1] ).getKind();
          int knd2 = queryAtomic( pf[2] ).getKind();
          if( is_eq_kind( knd2 ) )
          {
            RefPtr< LFSCProof > p = t1->getLFSCProof();
            if( t2->hasRational() )
              p = LFSCLraMulC::Make(p.get(), t2->getRational(), get_normalized( knd ));
            p = LFSCLraSub::Make( p.get(), t2->getLFSCProof(), get_normalized( knd ), EQ);
            tRetVal = new TReturn(p.get(), emptyL, emptyLUsed, t2->getRational(), t2->hasRational() , 1);
          }else if( knd2==FALSE_EXPR ){    //false case
#ifdef PRINT_MAJOR_METHODS
            //cout << ";[M]: iff_mp, false" << std::endl;
#endif
            //becomes a contradiction
            RefPtr< LFSCProof > p = t1->getLFSCProof();
            p = LFSCLraAdd::Make( p.get(), t2->getLFSCProof(),
                                  get_normalized( knd ),
                                  get_normalized( knd, true ) );
            p = LFSCLraContra::Make( p.get(), is_comparison( knd ) ? (int)GT : (int)DISTINCT );
            tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
          }
        }else if( t2->getProvesY()==3 || t1->getProvesY()==3 ){
//          yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2, rev_pol );
//          if( yMode==3 ){
//#ifdef PRINT_MAJOR_METHODS
//            cout << ";[M]: iff_mp, boolean" << std::endl;
//#endif
//            //do boolean resolution
//            tRetVal = new TReturn( LFSCBoolRes::Make( t1->getLFSCProof(), t2->getLFSCProof(), pf[1], pf ),
//                                emptyL, emptyLUsed, nullRat, false, 3 );
//          }
        }else{
          if( t2->getProvesY()!=1 || TReturn::normalize_tr( pf[4], t2, 2, rev_pol )!=-1 ){
            if( t1->getProvesY()!=1 || TReturn::normalize_tr( pf[3], t1, 2, rev_pol )!=-1 ){
              ostringstream os1;
              os1 << "(" << (t2->getProvesY()==0 ? "iff" : "impl" ) << "_mp _ _ ";
              ostringstream os2;
              os2 << ")";
              tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
            }
          }
        }
      }
    }
    else if(pf[0]==d_iff_symm_str )
    {
      TReturn* t = cvc3_to_lfsc( pf[3], beneath_lc, !rev_pol );
      yMode = t->getProvesY();
      t->getL( emptyL, emptyLUsed );
      if( yMode==1 )
      {
#ifdef PRINT_MAJOR_METHODS
        cout << ";[M]: iff_symm" << std::endl;
#endif
        if( t->hasRational() ){
          Rational r = 1/t->getRational();
          //adding this
          Rational rNeg = -1/t->getRational();
          RefPtr< LFSCProof > p = LFSCLraMulC::Make( t->getLFSCProof(), rNeg, EQ );
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, r, true, 1 );
        }else{
          Rational r = Rational( -1 );
          RefPtr< LFSCProof > p = LFSCLraMulC::Make( t->getLFSCProof(), r, EQ );
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
        }
      }
      else if( yMode==0 )
      {
        tRetVal = new TReturn( LFSCProof::Make_mimic( pf, t->getLFSCProof(), 2 ), emptyL, emptyLUsed, t->getRational(), t->hasRational(), 0 );
      }
    }
    else if(pf[0]==d_impl_mp_str){ // impl_mp rule
      // get subproofs
      TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc);
      TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc);
      t1->getL( emptyL, emptyLUsed );
      t2->getL( emptyL, emptyLUsed );
      yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2);
      if( yMode==1 ){
        int knd1 = get_normalized( queryAtomic( pf[1] ).getKind() );
        int knd2 = get_normalized( queryAtomic( pf[2] ).getKind() );
        if( is_eq_kind( knd2 ) )
        {
#ifdef PRINT_MAJOR_METHODS
          cout << ";[M]: impl_mp" << std::endl;
#endif
          RefPtr< LFSCProof > p1 = LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(), knd1, knd2 );
          // if non-homogenous case
          if( knd1 == GT && knd2 == GE ){
            ostringstream os1;
            os1 <<"(>0_to_>=0_Real _";
            ostringstream os2;
            os2 <<")";
            p1 = LFSCProofGeneric::Make(os1.str(), p1.get(), os2.str());
            p1->setChOp( GE );
          }
          tRetVal = new TReturn(p1.get(), emptyL, emptyLUsed, nullRat, false, 1);
        }else{
          cout << "Kind = " << kind_to_str( knd2 ) << std::endl;
        }
      }
      else
      {
        ostringstream os1, os2;
        os1 << "(impl_mp _ _ ";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0);
      }
    }
    else if( pf[0]==d_basic_subst_op_str || pf[0]==d_basic_subst_op1_str )
    {
      if( pf.arity()==5 ){
        // get subproofs
        bool prevCvc3Mimic = cvc3_mimic;
#ifdef LRA2_PRIME
        if( pf[1].getKind()==IFF || pf[1].getKind()==AND || pf[1].getKind()==OR && getNumNodes( pf )<=3 ){
#else
        if( pf[1].getKind()==IFF ){
#endif
          cvc3_mimic = true;
        }
#ifdef PRINT_MAJOR_METHODS
        cout << ";[M]: basic_subst_op1 " << kind_to_str( pf[1].getKind() ) << std::endl;
#endif
        //cvc3_mimic = (( pe1.getKind()==AND || pe1.getKind()==OR ) && getNumNodes( pf1 )<5 ) ? true : prevCvc3Mimic;
        TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc, rev_pol);
        //cvc3_mimic = (( pe1.getKind()==AND || pe1.getKind()==OR ) && getNumNodes( pf2 )<5 ) ? true : prevCvc3Mimic;
        TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc, rev_pol);
        cvc3_mimic = prevCvc3Mimic;

        tRetVal = do_bso( pf, beneath_lc, rev_pol, t1, t2, ose );
      }
    }
    else if( pf[0]==d_basic_subst_op0_str ){
      if( pf.arity()==4 ){
        TReturn* t = cvc3_to_lfsc(pf[3],beneath_lc, !rev_pol);
        yMode = t->getProvesY();
        t->getL( emptyL, emptyLUsed );
        if( yMode==1 ){
          if( pf[1].isNot() || pf[1].getKind()==UMINUS ){
            if( !pf[2][0].isFalse() && !pf[2][0].isTrue() ){
              RefPtr< LFSCProof > p = LFSCLraMulC::Make( t->getLFSCProof(), Rational( -1 ), EQ );
              tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, t->getRational(), t->hasRational(), 1 );
            }else{
              tRetVal = t;
            }
          }
        }else if( yMode==3 ){
        }else if( yMode==2 ){
          if( pf[1].isNot() )     //rev_pol should have switched things already
            tRetVal = t;
        }else if( yMode==0 ){
          ostringstream os1;
          os1 << "(basic_subst_op0_" << kind_to_str( pf[1].getKind() ) << " _ _ ";
          ostringstream os2;
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
        }
      }
      if( !tRetVal ){
        ose << "subst0 kind = " << kind_to_str( pf[1].getKind() ) << std::endl;
        ose << "subst0 arity = " << pf.arity() << std::endl;
      }
    }
    else if( pf[0]==d_optimized_subst_op_str )
    {
      if( pf[1].getKind()==ITE ){
#ifdef PRINT_MAJOR_METHODS
        cout << ";[M]: optimized_subst_op, ite " << std::endl;
#endif
        //make reflexive proof of proven statement
        RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1] );

        ostringstream os1, os2;
        if( isFormula( pf[1] ) ){
          os1 << "(iff_refl ";
        }else{
          os1 << "(refl Real ";
        }
        os2 << ")";
        p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );

        bool success = true;
        for( int a=3; a<pf.arity(); a++ ){
          if( success ){
            success = false;
            Expr pe;
            if( what_is_proven( pf[a], pe ) )
            {
              int type = -1;
              for( int b=0; b<3; b++ ){
                if( pe[0]==pf[1][b] )
                  type = b;
              }
              //set cvc3 mimic to true if we are proving an equivalence of the conditional formula
              bool prev_cvc3_mimic = cvc3_mimic;
              if( type==0 || isFormula( pf[1] ) )
                cvc3_mimic = true;

              TReturn* t = cvc3_to_lfsc(pf[a],beneath_lc);

              cvc3_mimic = prev_cvc3_mimic;

              t->getL( emptyL, emptyLUsed );
              if( TReturn::normalize_tr( pf[a], t, 0 )==0 ){
                if( type!=-1 ){
                  ostringstream os1, os2;
                  os1 << "(optimized_subst_op_";
                  if( isFormula( pf[1] ) )
                    os1 << "ifte";
                  else
                    os1 << "ite";
                  if( type==1 )
                    os1 << "_t1";
                  else if( type==2 )
                    os1 << "_t2";
                  os1 << " _ _ _ _ _ _ _ ";
                  os2 << ")";
                  p = LFSCProofGeneric::Make( os1.str(), p.get(), t->getLFSCProof(), os2.str() );
                  success = true;
                }
              }
            }
          }
        }
        if( success ){
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 0 );
        }
      }else if( pf[1].getKind()==PLUS ){
        //cout << ";[M]: optimized_subst_op, plus " << std::endl;
        TReturn* t = cvc3_to_lfsc(pf[3],beneath_lc);
        yMode = t->getProvesY();
        t->getL( emptyL, emptyLUsed );
        if( t->getProvesY()==1 ){
          tRetVal = t;
        }else{
          //tRetVal = make_trusted( pf );
          Expr pe;
          if( what_is_proven( pf[3], pe ) )
          {
            if( pe.getKind()==EQ )
            {
              ostringstream os1, os2;
              os1 << "(canonize_conv _ _ _ _ _ _ ";
              int pnt1 = queryMt( Expr( MINUS, pe[0], pe[1] ) );
              int pnt2 = queryMt( Expr( MINUS, pf[1], pf[2] ) );
              os1 << "@pnt" << pnt1 << " @pnt" << pnt2 << " ";
              os2 << ")";
              pntNeeded[ pnt1 ] = true;
              pntNeeded[ pnt2 ] = true;
              tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t->getLFSCProof(), os2.str() ),
                                  emptyL, emptyLUsed, t->getRational(), t->hasRational(), 0 );
            }else{
              cout << "proving kind " << kind_to_str( pe.getKind() ) << std::endl;
              cout << pf[3][0] << " " << pe << std::endl;
            }
          }
        }
      }else{
        //tRetVal = make_trusted( pf );
        if( pf[1].arity()==pf.arity()-3 ){
#ifdef PRINT_MAJOR_METHODS
          cout << ";[M]: optimized_subst_op, cascade " << kind_to_str( pf[1].getKind() ) << std::endl;
#endif
          Expr pfn = pf[pf.arity()-1];
          Expr cf1 = pf[1][pf.arity()-4];
          Expr cf2 = pf[2][pf.arity()-4];
          tRetVal = cvc3_to_lfsc( pf[pf.arity()-1], beneath_lc, rev_pol );
          for( int a=(int)pf.arity()-2; a>=3; a-- ){
            cf1 = Expr( pf[1].getKind(), pf[1][a-3], cf1 );
            cf2 = Expr( pf[2].getKind(), pf[2][a-3], cf2 );
            std::vector < Expr > exprs;
            exprs.push_back( d_basic_subst_op1_str );
            exprs.push_back( cf1 );
            exprs.push_back( cf2 );
            exprs.push_back( pf[a] );
            exprs.push_back( pfn );
            //cascade it, turn it into a different proof
            pfn = Expr(PF_APPLY, exprs );
            TReturn* tc = cvc3_to_lfsc( pf[a], beneath_lc, rev_pol );
            tRetVal = do_bso( pfn, beneath_lc, rev_pol, tc, tRetVal, ose );
          }
        }else{
          ose << "opt_subst_op arity pv1 = " << pf[1].arity() << " " << pf.arity()-3 << std::endl;
          ose << "opt_subst_op arity pv2 = " << pf[2].arity() << " " << pf.arity()-3 << std::endl;
        }
      }
      if( !tRetVal ){
        for( int a=0; a<pf.arity(); a++ ){
          if( a>=3 && pf[a].arity()>0 ){
            ose << a << ": ";
            ose << pf[a][0] << std::endl;
            Expr pre;
            what_is_proven( pf[a], pre );
            ose << "wip: " << pre << std::endl;
          }else{
            ose << a << ": " << pf[a] << std::endl;
          }
        }
        //RefPtr< LFSCProof > p;
        //TReturn* curr = NULL;
        //for( int a=(int)(pf.arity()-1); a>=4; a-- ){
        //  TReturn* t = cvc3_to_lfsc(pf[a],beneath_lc);
        //  if( curr ){
        //    int cyMode = TReturn::normalize_tret(
        //    if( pf[1].getKind()==AND || pf[1].getKind()==OR ){
        //      ostringstream os1, os2;
        //      os1 << "(optimized_subst_op_";
        //      if( yMode==2 )
        //        os1 << "impl_";
        //      os1 << kind_to_str( pf[1].getKind() );
        //      os1 << " _ _ _ _ ";
        //      os2 << ")";
        //      p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );
        //  }else{
        //    curr = t;
        //  }
        //  tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, t->getProvesY() );
        //}
        ose << "opt_subst_op kind = " << kind_to_str( pf[1].getKind() ) << std::endl;
        ose << "opt_subst_op arity = " << pf.arity() << std::endl;
      }
    }
    else if( pf[0]==d_eq_trans_str ){
      // get subproofs
      TReturn* t1 = cvc3_to_lfsc(pf[5],beneath_lc);
      TReturn* t2 = cvc3_to_lfsc(pf[6],beneath_lc);
      t1->getL( emptyL, emptyLUsed );
      t2->getL( emptyL, emptyLUsed );
      yMode = TReturn::normalize_tret( pf[5], t1, pf[6], t2 );
      if( yMode==1 ){
        // merge literals
        tRetVal = new TReturn( LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(),
                                              EQ, EQ ), emptyL, emptyLUsed, nullRat, false, 1 );
      }else if( yMode==0 ){
        std::vector< RefPtr< LFSCProof > > pfs;
        std::vector< string > strs;
        ostringstream os1, os2, os3;
        os1 << "(trans Real ";
        os2 << " ";
        os3 << ")";
        pfs.push_back( LFSCProofExpr::Make( pf[2] ) );
        pfs.push_back( LFSCProofExpr::Make( pf[3] ) );
        pfs.push_back( LFSCProofExpr::Make( pf[4] ) );
        pfs.push_back( t1->getLFSCProof() );
        pfs.push_back( t2->getLFSCProof() );
        strs.push_back( os1.str() );
        strs.push_back( os2.str() );
        strs.push_back( os2.str() );
        strs.push_back( os2.str() );
        strs.push_back( os2.str() );
        strs.push_back( os3.str() );
        tRetVal = new TReturn( LFSCProofGeneric::Make( pfs, strs ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if(pf[0] == d_eq_symm_str){ // eq_symm rule
      TReturn* t = cvc3_to_lfsc(pf[4],beneath_lc);
      t->getL( emptyL, emptyLUsed );
      if( t->getProvesY()==1 )
      {
        tRetVal = new TReturn(LFSCLraMulC::Make(t->getLFSCProof(), Rational( -1 ), EQ), emptyL, emptyLUsed, nullRat, false, 1);
      }
      else if( t->getProvesY()==0 )
      {
        ostringstream os1, os2;
        os1 << "(symm Real _ _ ";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0);
      }
    }
    else if( pf[0]==d_real_shadow_str )
    {
      // get subproofs
      TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc);
      TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc);
      t1->getL( emptyL, emptyLUsed );
      t2->getL( emptyL, emptyLUsed );
      yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2 );
      if( yMode==1 )
      {
        int op1 = get_normalized( queryAtomic( pf[1] ).getKind() );
        int op2 = get_normalized( queryAtomic( pf[2] ).getKind() );
        tRetVal = new TReturn( LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(), op1, op2 ), emptyL, emptyLUsed, nullRat, false, 1 );
      }
      else if( yMode==0 )
      {
        ostringstream os1, os2;
        os1 << "(real_shadow_" << kind_to_str( pf[1].getKind() );
        os1 << "_" << kind_to_str( pf[2].getKind() );
        os1 << " _ _ _ ";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ),
                            emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_addInequalities_str )
    {
      // get subproofs
      TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc);
      TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc);
      t1->getL( emptyL, emptyLUsed );
      t2->getL( emptyL, emptyLUsed );
      yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2 );
      if( yMode==1 )
      {
        tRetVal = new TReturn( LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(),
                                              pf[1].getKind(), pf[2].getKind() ), emptyL, emptyLUsed, nullRat, false, 1 );
      }
      else if( yMode==0 )
      {
        ostringstream os1, os2;
        os1 << "(add_inequalities_" << kind_to_str( pf[1].getKind() );
        os1 << "_" << kind_to_str( pf[2].getKind() );
        os1 << " _ _ _ _ ";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ),
                            emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0] == d_real_shadow_eq_str){
      TReturn* t1 = cvc3_to_lfsc(pf[3], beneath_lc);
      TReturn* t2 = cvc3_to_lfsc(pf[4], beneath_lc);
      t1->getL( emptyL, emptyLUsed );
      t2->getL( emptyL, emptyLUsed );
      yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2 );
      if( yMode==1 ){
        ostringstream os1, os2;
        os1 << "(lra_>=_>=_to_= _ _ ";
        os2 << ")";
        RefPtr< LFSCProof > p = LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() );
        p->setChOp( EQ );
        tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
      }else if( yMode==0 || yMode==2 ){
        ostringstream os1, os2;
        os1 << "(real_shadow_eq _ _";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ),
                            emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_cycle_conflict_str )
    {
      // get subproofs
      bool isErr = false;
      int n = ( pf.arity() - 1 )/2 + 1;
      std::vector < TReturn* > trets;
      for( int a=n; a<pf.arity(); a++ ){
        if( !isErr ){
          TReturn* t = cvc3_to_lfsc(pf[a],beneath_lc);
          if( TReturn::normalize_tr( pf[a], t, 1 )!=1 ){
            isErr = true;
          }else{
            trets.push_back( t );
            t->getL( emptyL, emptyLUsed );
          }
        }
      }
      //add them together
      if( !isErr ){
        int currOp = get_normalized( pf[1].getKind() );
        RefPtr< LFSCProof > p1 = trets[0]->getLFSCProof();
        for( int a=1; a<(int)trets.size(); a++ ){
          int op = get_normalized( pf[a+1].getKind() );
          p1 = LFSCLraAdd::Make( trets[a]->getLFSCProof(), p1.get(), op, currOp );
          if( op==GT ){
            currOp = GT;
          }else if( op==GE ){
            currOp = currOp==GT ? GT : GE;
          }
        }
        tRetVal = new TReturn( LFSCLraContra::Make( p1.get(), GT ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_learned_clause_str )
    {
      if( pf.arity()==2 )
      {
        TReturn* t = cvc3_to_lfsc(pf[1],true);
        t->getL( emptyL, emptyLUsed );
        RefPtr< LFSCProof > p = t->getLFSCProof();

        Expr pe;
        what_is_proven( pf[1], pe );
        bool success = true;
        if( !pe.isFalse() ){
          success = false;
          if( TReturn::normalize_tr( pf[1], t, 3, false )==3 )
          {
            p = t->getLFSCProof();
            success = true;
          }
#ifdef PRINT_MAJOR_METHODS
          cout << ";[M]: learned clause, not proven false" << std::endl;
#endif
        }
        else if( cvc3_mimic && pf[1][0]!=d_cycle_conflict_str )
        {
          ostringstream os1, os2;
          os1 << "(clausify_false ";
          os2 << ")";
          p = LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() );
        }
        if( success ){
          //ostringstream os1, os2;
          //if( debug_var )
          //  os1 << "LC:";
          //we must close all proof-lets that contain free variables
          //p = make_let_proof( p.get(), emptyL, false );
#ifdef OPTIMIZE
          std::vector< int > assumes, assumesUsed;
          t->calcL( assumes, assumesUsed );
          for( int a=0; a<(int)assumes.size(); a++ ){
            p = LFSCAssume::Make( assumes[a], p.get(), true );
          }
#else
          for( int a=0; a<(int)emptyL.size(); a++ ){
            p = LFSCAssume::Make( emptyL[a], p.get(), true );
          }
#endif
          emptyL.clear();
          emptyLUsed.clear();
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
        }
      }
    }
    else if( pf[0]==d_andE_str )
    {
      TReturn* t = cvc3_to_lfsc(pf[3],beneath_lc);
      t->getL( emptyL, emptyLUsed );
      if( t->getProvesY()==0 )
      {
        int pos = pf[1].getRational().getNumerator().getInt();
        RefPtr< LFSCProof > p = LFSCProof::Make_and_elim( pf[2], t->getLFSCProof(), pos, pf[2][pos] );
        tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, t->getRational(), t->hasRational(), 0 );
      }
      else if( t->getProvesY()==3 )
      {
        //need to use and CNF rules
        RefPtr< LFSCProof > p = LFSCProof::Make_CNF( pf[2], d_and_mid_s,
                                                pf[1].getRational().getNumerator().getInt() );
        p = LFSCBoolRes::Make( t->getLFSCProof(), p.get(), pf[2], pf );
        tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
      }
    }
    else if( pf[0]==d_rewrite_implies_str )
    {
      if( !cvc3_mimic )
      {
        Expr ei = Expr( IMPLIES, pf[1], pf[2] );
        RefPtr< LFSCProof > p = LFSCProof::Make_CNF( ei, d_imp_s, 3 );
        if( p.get() )
        {
          tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 3 );
        }
      }
      else
      {
        //tRetVal = new TReturn( LFSCProofGeneric::MakeStr( "(rewrite_implies _ _)" ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_rewrite_ite_same_str )
    {
      ostringstream os1, os2;
      os1 << "(rewrite_ite_same ";
      RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[2] );
      RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[3] );
      os2 << ")";
      tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ),
                          emptyL, emptyLUsed, nullRat, false, 0 );
    }
    else if( pf[0]==d_rewrite_and_str || pf[0]==d_rewrite_or_str )
    {
      //Expr e = Expr( IFF, pf[1], pf[2] );
      bool isAnd = pf[0]==d_rewrite_and_str;
      if( pf[1].arity()==2 && pf[1][0]==pf[1][1] ){   //try to apply binary redundant rule
        ostringstream os1, os2 ;
        os1 << "(" << ( isAnd ? "and" : "or" ) << "_redundant ";
        RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1][0] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }else if( isFlat( pf[2] ) ){        //try to do the normalize
        Expr e1 = cascade_expr( pf[1] );
        Expr e2 = cascade_expr( pf[2] );
        Expr pe;
        make_flatten_expr( e1, pe, pf[1].getKind() );
        //cout << "we have an and normalize " << e1 << std::endl;
        //cout << "making and normalize for " << pe << std::endl;
        //cout << "this should be equal to  " << e2 << std::endl;
        //cout << (pe==e2) << std::endl;
        if( pe==e2 ){     //standard and normalize
          ostringstream os1, os2;
          os1 << "(" << ( isAnd ? "and" : "or" ) << "_normalize _ ";
          os2 << ")";
          RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1] );
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
        }
        //else if( pf[1].arity()==2 ){    //try to normalize the symm version 
        //  Expr e1s = cascade_expr( Expr( pf[1].getKind(), pf[1][1], pf[1][0] ) );
        //  make_flatten_expr( e1s, pe, pf[1].getKind() );
        //  if( pe==e2 ){
        //    ostringstream oss1, oss2, oss3, oss4;
        //    oss1 << "(iff_trans _ _ (" << ( isAnd ? "and" : "or" );
        //    oss1 << "_symm ";
        //    RefPtr< LFSCProof > pex1 = LFSCProofExpr::Make( pf[1][0] );
        //    oss2 << " ";
        //    RefPtr< LFSCProof > pex2 = LFSCProofExpr::Make( pf[1][1] );
        //    oss3 << ") " << "(" << ( isAnd ? "and" : "or" ) << "_normalize _ ";
        //    RefPtr< LFSCProof > ps = LFSCProofExpr::Make( e1s );
        //    oss4 << "))";
        //    std::vector< RefPtr< LFSCProof > > pfs;
        //    pfs.push_back( pex1.get() );
        //    pfs.push_back( pex2.get() );
        //    pfs.push_back( ps.get() );
        //    std::vector< string > strs;
        //    strs.push_back( oss1.str() );
        //    strs.push_back( oss2.str() );
        //    strs.push_back( oss3.str() );
        //    strs.push_back( oss4.str() );
        //    tRetVal = new TReturn( LFSCProofGeneric::Make( pfs, strs ), emptyL, emptyLUsed, nullRat, false, 0 );
        //  }
        //}
      }
      if( !tRetVal ){
        //going to have to trust it
        TReturn* t = make_trusted( pf );
        //this code runs the normalize side condition, but ignores it (for consistency with proof checking times)
        ostringstream os1, os2;
        os1 << "(" << (isAnd ? "and" : "or" ) << "_nd _ _ _ ";
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_rewrite_iff_symm_str )
    {
      ostringstream os1, os2;
      os1 << "(rewrite_iff_symm ";
      RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
      RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[2] );
      os2 << ")";
      tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
    }
    else if( pf[0]== d_implyEqualities_str){

      if( pf.arity()==5 ){
        TReturn* t1 = cvc3_to_lfsc(pf[3],beneath_lc);
        TReturn* t2 = cvc3_to_lfsc(pf[4],beneath_lc);
        t1->getL( emptyL, emptyLUsed );
        t2->getL( emptyL, emptyLUsed );
        if( TReturn::normalize_tr( pf[3], t1, 0 )==0 && TReturn::normalize_tr( pf[4], t2, 0 )==0 )
        {
          Expr e1, e2;
          if( what_is_proven( pf[3], e1 ) && what_is_proven( pf[4], e2 ) )
          {
            int m1 = queryMt( Expr( MINUS, e1[1], e1[0] ) );
            int m2 = queryMt( Expr( MINUS, e2[1], e2[0] ) );

            ostringstream os1, os2;
            os1<<"(imply_equalities _ _ _ _ _ _ ";
            os1 << "@pnt" << abs( m1 ) << " @pnt" << abs( m2 ) << " ";
            os2 << ")";
            tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t1->getLFSCProof(), t2->getLFSCProof(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
          }
        }
      }
    }
    else if( pf[0]==d_implyWeakerInequality_str )
    {
#ifdef PRINT_MAJOR_METHODS
      //cout << ";[M]: imply weaker equality " << pf[1] << std::endl;
#endif
      if( !cvc3_mimic ){
        if( pf[1].arity()==2 && pf[2].arity()==2 && pf[1][1][0].isRational() && pf[2][1][0].isRational() )
        {
          //Rational r = pf[1][1][0].getRational() - pf[2][1][0].getRational();
          //tRetVal = new TReturn( LFSCLraAxiom::Make( r, GT ), emptyL, emptyLUsed, nullRat, false, 1 );
          tRetVal = new TReturn( LFSCLraAxiom::MakeEq(), emptyL, emptyLUsed, nullRat, false, 1 );
        }
      }else{
        Rational r1, r2;
        ostringstream os1, os2;
        getRat(pf[1][1][0], r1);
        getRat(pf[2][1][0], r2);
        RefPtr <LFSCProof> p;

        os1 <<"(imply_weaker_inequality_" << kind_to_str( pf[1].getKind() ) << "_" << kind_to_str( pf[2].getKind() );
        if(pf[1][1].arity() > 2)
        {
          vector<Expr> t1_children;
          int start_i = 1;
          int end_i = pf[1][1].arity();
          for(int i = start_i; i < end_i; i ++) {
            const Expr& term = pf[1][1][i];
            t1_children.push_back(term);
          }
          p = LFSCProofExpr::Make(Expr(pf[1][1].getKind(), t1_children));
        }
        else
        {
          p = LFSCProofExpr::Make(pf[1][1][1]);
        }
        os2<<" ";
        print_rational(r1, os2);
        os2 << " ";
        print_rational(r2, os2);
        os2<<")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ),
                            emptyL, emptyLUsed, nullRat, false, 0 );
      }
    }
    else if( pf[0]==d_implyNegatedInequality_str )
    {
#ifdef PRINT_MAJOR_METHODS
      //cout << ";[M]: imply negated equality " << pf[1] << std::endl;
#endif
      if( !cvc3_mimic ){
        if( pf[1].arity()==2 && pf[2].arity()==2 && pf[1][1][0].isRational() && pf[2][1][0].isRational() )
        {
          //Rational r = -( pf[1][1][0].getRational() + pf[2][1][0].getRational() );
          //tRetVal = new TReturn( LFSCLraAxiom::Make( r, GT ), emptyL, emptyLUsed, nullRat, false, 1 );
          tRetVal = new TReturn( LFSCLraAxiom::MakeEq(), emptyL, emptyLUsed, nullRat, false, 1 );
        }
      }else{
        Rational r1, r2;
        if( getRat( pf[1][1][0], r1 ) && getRat(pf[2][1][0], r2) ){
          Expr ep = pf[1][1][1];
          Rational negOne = Rational( -1 );
          bool isNeg = false;
          if ( pf[1][1][1].getKind()==MULT && pf[1][1][1][0].isRational() && pf[1][1][1][0].getRational()==negOne ){
            isNeg = true;
            if(pf[1][1].arity() > 2)
            {
              vector<Expr> t1_children;
              int start_i = 1;
              int end_i = pf[1][1].arity();
              for(int i = start_i; i < end_i; i ++) {
                const Expr& term = pf[1][1][i];
                t1_children.push_back(term);
              }
              ep = Expr(pf[1][1].getKind(), t1_children);
            }
            else
            {
              ep = pf[1][1][1][1];
            }

          }
          if(r1 == r2) {
            ostringstream os1, os2;
            os1 << "(imply_negated_inequality_<" << (isNeg ? "n" : "" );
            os1 << " ";
            RefPtr< LFSCProof > p = LFSCProofExpr::Make( ep );
            os2 << " ";
            print_rational( r1, os2 );
            os2 << ")";
            tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ),
                                emptyL, emptyLUsed, nullRat, false, 0 );
          }else{
            ostringstream os1, os2;
            os1 << "(imply_negated_inequality_";
            os1 << kind_to_str(pf[1].getKind()) << "_"<<kind_to_str(pf[2].getKind()) << (isNeg ? "n" : "" );
            os1 << " ";
            RefPtr< LFSCProof > p = LFSCProofExpr::Make( ep );
            os2 << " ";
            print_rational( r1, os2 );
            os2 << " ";
            print_rational( r2, os2 );
            os2 << ")";
            tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ),
                                emptyL, emptyLUsed, nullRat, false, 0 );
          }
        }
      }
    }
    else if( pf[0]==d_rewrite_iff_str){
      ostringstream os1, os2;

      // then it's just the iff_refl rule
      if(pf[1] == pf[2]){
        os1 << "(iff_refl ";
        os2 << ")";
        RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1] );
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed,
                            nullRat, false, 0 );
      }
      if(pf[1] == d_pf_expr.getEM()->trueExpr()){
        os1 << "(rewrite_iff_true_l ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[2] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if(pf[1] == d_pf_expr.getEM()->falseExpr()){
        os1 << "(rewrite_iff_false_l ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[2] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if(pf[2] == d_pf_expr.getEM()->trueExpr()){
        os1 << "(rewrite_iff_true_r ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if(pf[2] == d_pf_expr.getEM()->falseExpr()){
        os1 << "(rewrite_iff_false_r ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if(pf[1].isNot() && pf[1][0] == pf[2]){
        os1 << "(rewrite_iff_not_l ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1][0] );

        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if(pf[2].isNot() && pf[2][0] == pf[1]){
        os1 << "(rewrite_iff_not_r ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[2][0] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      // just flips them
      if(pf[1] < pf[2]){
        os1 << "(rewrite_iff_symm ";
        RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
        RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[2] );
        os2 << ")";
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed, nullRat, false, 0 );
      }
      if( !tRetVal ){
        os1 << "(iff_refl ";
        os2 << ")";
        RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1].iffExpr(pf[2]) );
        tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed,
                            nullRat, false, 0 );
      }
    }
    else if( isIgnoredRule( pf[0] ) )
    {
      TReturn* t = cvc3_to_lfsc(pf[2],beneath_lc);
      yMode = t->getProvesY();
      t->getL( emptyL, emptyLUsed );
      if( !cvc3_mimic )
      {
        if( yMode==1 ){
          tRetVal = t;
        }
      }
      else
      {
        if( yMode==0 || yMode==2 )
        {
          ostringstream os1, os2;
          os1 << "(" << pf[0] << (yMode==2 ? "_impl" : "" ) << " _ ";
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), t->getLFSCProof(), os2.str() ), emptyL, emptyLUsed,
                              t->getRational(), t->hasRational(), 0 );
        }
      }
    }
    else if( isTrivialTheoryAxiom( pf ) )
    {
      //find the rational multiplier for the axiom
      Rational r;
      bool hasRat = false;
      if( pf[0]==d_mult_ineqn_str || pf[0]==d_mult_eqn_str || pf[0]==d_rewrite_eq_symm_str || pf[0]==d_int_const_eq_str ){
        if( pf[0]==d_mult_ineqn_str && pf[2].arity()==2 && pf[2][1].arity()==2 ){
          if( pf[2][1][1].isRational() ){
            r = pf[2][1][1].getRational();
            hasRat = true;
          }else if( pf[2][1][0].isRational() ){
            r = pf[2][1][0].getRational();
            hasRat = true;
          }
        }else if( pf[0]==d_mult_eqn_str && pf[3].isRational() ){
          r = pf[3].getRational();
          hasRat = true;
        }else if( pf[0]==d_rewrite_eq_symm_str ){
          r = -1;
          hasRat = true;
        }else if( pf[0]==d_int_const_eq_str ){
          if( pf[1].getKind()==EQ && !pf[2].isFalse() ){
            if( pf[1][1].getKind()==MULT && getRat( pf[1][1][0], r ) ){
              r = -r;
            }else if( pf[1][1].getKind()==PLUS && pf[1][1][1].getKind()==MULT && getRat( pf[1][1][1][0], r ) ){
              r = -r;
            }else{
              r = -1;
            }
            hasRat = true;
          }
        }
        if( !hasRat )
        {
          ose << pf[0] << ", Warning: Can't find rational multiplier " << std::endl;
          ose << pf[2] << std::endl;
        }
      }
      //handle the axiom  -  only do it if the term is polynomial normalizable
      if( !cvc3_mimic && isTrivialTheoryAxiom( pf, true ) )
      {
        //ignore it if cvc3_mimic is false
        if( hasRat && r<0 && pf[0]==d_mult_ineqn_str ){
          r = -r;
        }
        //if( debug_conv && !beneath_lc ){
        //  cout << "WARNING: Trivial theory axiom used, not underneath learned clause: " << pf[0] << std::endl;
        //}
        tRetVal = new TReturn( LFSCLraAxiom::MakeEq(), emptyL, emptyLUsed, r, hasRat, 1 );
      }else{
        //int val = queryM( pf[1] );
        if( pf[0] == d_refl_str )
        {
          if( isFormula( pf[1] ) ){
            ostringstream os1, os2;
            os1 << "(iff_refl ";
            os2 << ")";
            RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1] );
            tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed,
                                nullRat, false, 0 );
          }else{
            ostringstream os1, os2;
            os1 << "(refl Real ";
            os2 << ")";
            RefPtr< LFSCProof > p = LFSCProofExpr::Make( pf[1] );
            tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p.get(), os2.str() ), emptyL, emptyLUsed,
                                nullRat, false, 0 );
          }
        }
        else if( pf[0] == d_flip_inequality_str )
        {
          ostringstream os1, os2;
          os1 << "(flip_inequality_" << kind_to_str( pf[1].getKind() );
          os1 << "_" << kind_to_str( pf[2].getKind() ) << " ";
          os2 << ")";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1][0] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[1][1] );
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_right_minus_left_str )
        {
          ostringstream os1, os2;
          os1 << "(right_minus_left_" << kind_to_str( pf[1].getKind() ) << " ";
          os2 << ")";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1][0] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[1][1] );
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_minus_to_plus_str )
        {
          ostringstream os1, os2;
          os1 << "(minus_to_plus ";
          os2 << ")";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[2] );
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_plus_predicate_str )
        {
          ostringstream os1, os2;
          os1 << "(plus_predicate_" << kind_to_str( pf[1].getKind() ) << " ";
          std::vector< string > strs;
          std::vector< RefPtr< LFSCProof > > pfs;
          pfs.push_back( LFSCProofExpr::Make( pf[1][0] ) );
          pfs.push_back( LFSCProofExpr::Make( pf[1][1] ) );
          pfs.push_back( LFSCProofExpr::Make( pf[2][0][1] ) );
          os2 << ")";
          std::string spc( " " );
          strs.push_back( os1.str() );
          strs.push_back( spc );
          strs.push_back( spc );
          strs.push_back( os2.str() );
          tRetVal = new TReturn( LFSCProofGeneric::Make( pfs, strs ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_canon_plus_str || pf[0]==d_canon_mult_str )
        {
          int m = queryMt( Expr( MINUS, pf[1], pf[2] ) );
          ostringstream os;
          os << "(canonize_= _ _ _ ";
          os << "@pnt" << m << ")";
          pntNeeded[ m ] = true;
          tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_canon_invert_divide_str )
        {
          Rational r1 = Rational( 1 );
          Expr er1 = d_pf_expr.getEM()->newRatExpr( pf[1][0].getRational() );
          Expr er2 = d_pf_expr.getEM()->newRatExpr( r1/pf[1][1].getRational() );
          //cout << "we have made " << er1 << " " << er2 << std::endl;
          int m = queryMt( Expr( MINUS, pf[1], Expr( MULT, er1, er2 )) );
          ostringstream os;
          os << "(canonize_= _ _ _ ";
          os << "@pnt" << m << ")";
          pntNeeded[ m ] = true;
          tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_mult_ineqn_str && hasRat )
        {
          ostringstream os1, os2;
          os1 << "(mult_ineqn_" << (r<0 ? "neg_" : "");
          os1 << kind_to_str( pf[1].getKind() ) << " ";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1][0] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[1][1] );
          os2 << " ";
          print_rational( r, os2 );
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_mult_eqn_str && hasRat )
        {
          ostringstream os1, os2;
          os1 << "(mult_eqn ";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[2] );
          os2 << " ";
          print_rational( r, os2 );
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_negated_inequality_str )
        {
          Expr e1 = queryAtomic( pf[1], true );

          ostringstream os1, os2;
          os1 << "(negated_inequality_" << kind_to_str( e1.getKind() );
          os1 << "_" << kind_to_str( get_not( e1.getKind() ) ) << " ";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[1][0][0] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[1][0][1] );
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_rewrite_eq_symm_str )
        {
          ostringstream os1, os2;
          os1 << "(rewrite_eq_symm ";
          RefPtr< LFSCProof > p1 = LFSCProofExpr::Make( pf[2] );
          RefPtr< LFSCProof > p2 = LFSCProofExpr::Make( pf[3] );
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), p1.get(), p2.get(), os2.str() ), emptyL, emptyLUsed,
                              nullRat, false, 0 );
        }
        else if( pf[0] == d_rewrite_eq_refl_str )
        {
          ostringstream os1, os2;
          os1 << "(rewrite_eq_refl ";
          os2 << ")";
          tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), LFSCProofExpr::Make( pf[2] ), os2.str() ),
                                                      emptyL, emptyLUsed, nullRat, false, 0 );
        }
        else if( pf[0] == d_uminus_to_mult_str )
        {
          if( pf[1].isRational() )
          {
            ostringstream os;
            os << "(uminus_to_mult ";
            print_rational( pf[1].getRational(), os );
            os << ")";
            tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str() ), emptyL, emptyLUsed,
                                nullRat, false, 0 );
          }
        }
        else if( pf[0] == d_rewrite_not_true_str )
        {
          tRetVal = new TReturn( LFSCProofGeneric::MakeStr( "rewrite_not_true" ), emptyL, emptyLUsed, nullRat, false, 0 );
        }
        else if( pf[0] == d_rewrite_not_false_str )
        {
          tRetVal = new TReturn( LFSCProofGeneric::MakeStr( "rewrite_not_false" ), emptyL, emptyLUsed, nullRat, false, 0 );
        }
        else if( pf[0] == d_int_const_eq_str )
        {
          int m1 = queryMt( Expr( MINUS, pf[1][0], pf[1][1] ) );
          int m2 = queryMt( Expr( MINUS, pf[2][0], pf[2][1] ) );
          ostringstream os;
          os << "(canonize_iff _ _ _ _ _ _ @pnt" << m1 << " @pnt" << m2 << ")";
          pntNeeded[ m1 ] = true;
          pntNeeded[ m2 ] = true;
          tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str() ), emptyL, emptyLUsed, nullRat, false, 0 );
        }
      }
    }
    else if( pf[0]==d_lessThan_To_LE_rhs_rwr_str )
    {
      //FIXME: this introduces weirdness into the logic of completeness of the proof conversion
      //why is integer reasoning used in CVC3 QF_LRA proofs?
      if( !cvc3_mimic )
        tRetVal = new TReturn( LFSCLraAxiom::MakeEq(), emptyL, emptyLUsed, nullRat, false, 1 );
      else{
        tRetVal = make_trusted( pf );
      }
    }
    else if( pf[0]==d_rewrite_not_not_str )
    {
      //note that "not not" is already taken care of  FIXME
#ifdef LRA2_PRIME
      tRetVal = new TReturn( LFSCProofGeneric::MakeStr("(rewrite_not_not _)"), emptyL, emptyLUsed, nullRat, false, 0 );
#else
      if( !cvc3_mimic ){
        tRetVal = new TReturn( LFSCProofGeneric::MakeStr("(iff_refl _)"), emptyL, emptyLUsed, nullRat, false, 0 );
      }else{
        tRetVal = new TReturn( LFSCProofGeneric::MakeStr("(rewrite_not_not _)"), emptyL, emptyLUsed, nullRat, false, 0 );
      }
#endif
    }
    else if( isTrivialBooleanAxiom( pf[0] ) )
    {
      if( !cvc3_mimic ){
        tRetVal = new TReturn( LFSCLem::Make( queryM( pf[1] ) ), emptyL, emptyLUsed, nullRat, false, 3 );
      }else{

      }
    }
    else if( pf[0]==d_const_predicate_str )
    {
      if( is_eq_kind( pf[1].getKind() ) )
      {
        Rational r1, r2;
        //int knd = pf[2].isFalse() ? get_not( pf[1].getKind() ) : pf[1].getKind();
        RefPtr< LFSCProof > p;
        if( getRat( pf[1][0], r1 ) && getRat( pf[1][1], r2 ) ){
#ifdef PRINT_MAJOR_METHODS
          cout << ";[M]: const_pred " << kind_to_str( pf[1].getKind() );
          cout << " " << pf[2].isFalse();
          cout << ", rp=" << rev_pol << ", cvc=" << cvc3_mimic << std::endl;
#endif
          if( !cvc3_mimic ){
            //if( rev_pol ){
            //  ostringstream ose1;
            //  ose1 << "Warning: Const predicate, rev pol true" << std::endl;
            //  print_warning( ose1.str().c_str() ); 
            //  knd = get_not( knd );
            //}
            if( pf[1].getKind()==EQ ){
              p = LFSCLraAxiom::MakeEq();
            }else{
              //Rational r = is_opposite( knd ) ? r2 - r1 : r1 - r2;
              //if( knd==GT )
              //  r = Rational( 1, 1000000 );
              //if( knd==GE
              //  r = Rational( 0 );
              //p = LFSCLraAxiom::Make( r, get_normalized( knd ) );
              p = LFSCLraAxiom::MakeEq();
            }
            if( p.get() ){
              tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
            }
          }
          else
          {
            ostringstream os;
            os << "(const_predicate_" << kind_to_str( pf[1].getKind() );
            if( pf[2].getKind()==TRUE_EXPR )
              os << "_t";
            os << " ";
            print_rational( r1, os );
            os << " ";
            print_rational( r2, os );
            os << ")";
            tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os.str().c_str() ),
                                emptyL, emptyLUsed, nullRat, false, 0 );
          }
        }else{
          ose << "ERROR: Could not find rational for const predicate" << std::endl;
        }
      }
      if( !tRetVal )
        ose << "kind = " << kind_to_str( pf[1].getKind() );
    }
  }
  else
  {
    //use Expr pfMod
    //switch( pfPat )
    //{
    //}
    if( pfPat==1 )
    {
      ostringstream os1, os2, os3;
      os1 << "(ite_axiom ";
      os2 << " ";
      os3 << ")";
      std::vector< string > strs;
      std::vector< RefPtr< LFSCProof > > pfs;

      strs.push_back( os1.str() );
      pfs.push_back( LFSCProofExpr::Make( pf[1][0] ) );
      strs.push_back( os2.str() );
      pfs.push_back( LFSCProofExpr::Make( pf[1][1][1] ) );
      strs.push_back( os2.str() );
      pfs.push_back( LFSCProofExpr::Make( pf[1][2][1] ) );
      strs.push_back( os3.str() );
      RefPtr< LFSCProof > p = LFSCProofGeneric::Make( pfs, strs );

      tRetVal = new TReturn( LFSCClausify::Make( pf[1], p.get() ), emptyL, emptyLUsed,
                          nullRat, false, 3 );
    }else{
      ostringstream ose;
      ose << "WARNING: Unknown proof pattern [" << pfPat << "]";
      print_error( ose.str().c_str(), cout );
      //ostringstream os1;
      //os1 << "PROOF_PAT_" << pfPat;
      //tRetVal = new TReturn( LFSCProofGeneric::MakeStr( os1.str().c_str() ), emptyL, emptyLUsed, nullRat, false, 3 );
    }
  }
  if( !tRetVal ){
    static bool firstTime = true;
    if(pf.arity()>0 && (yMode!=-1 || firstTime ) ){
      firstTime = false;
      ose << "Unknown proof rule (" << d_rules[pf[0]] << ") " << pf[0] << endl;
      ose << "YMode : ";
      if( yMode==-2 )
        ose << "unknown";
      else if( yMode==-1 )
        ose << "fail";
      else
        ose << yMode;
      ose << std::endl;
      if( rev_pol )
        ose << "rev_pol = true" << std::endl;
      if( pfPat!=0 )
      {
        ose << "proof pattern = " << pfPat << std::endl;
      }
      print_error( ose.str().c_str(), cout );
    }
    tRetVal = new TReturn( LFSCProofGeneric::MakeUnk(), emptyL, emptyLUsed, nullRat, false, -1 );
  }


  if( debug_conv ){
    //cout << "print length = " << tRetVal->getLFSCProof()->get_string_length() << std::endl;
    cout << "...done " << pf[0] << " " << tRetVal->getProvesY() << std::endl;
  }
  if( debug_var ){
    ostringstream os1, os2;
    os1 << "[" << pf[0];
    if( pf[0]==d_basic_subst_op1_str || pf[0]==d_optimized_subst_op_str || pf[0]==d_basic_subst_op0_str || pf[0]==d_const_predicate_str || pf[0]==d_basic_subst_op_str )
      os1 << "_" << kind_to_str( pf[1].getKind() );
    if( pf[0]==d_const_predicate_str )
      os1 << "_" << pf[2];
    os1 << " ";
    os2 << "]";
    std::vector< int > lv, lvUsed;
    tRetVal->getL( lv, lvUsed );
    tRetVal = new TReturn( LFSCProofGeneric::Make( os1.str(), tRetVal->getLFSCProof(), os2.str(), true ),
                           lv, lvUsed, tRetVal->getRational(), tRetVal->hasRational(), tRetVal->getProvesY() );
  }
  //dont bother making small proofs into lambdas (length less than 30), or they are trivial
  if( !tRetVal->getLFSCProof()->isTrivial() && tRetVal->getLFSCProof()->get_string_length()>30 )
  {
    d_th_trans[pf] = true;
    //if( !d_th_trans_map[cvcm][pf] && pf.isSelected() ){
    //  std::cout << "already selected" << std::endl;
    //}
    d_th_trans_map[cvcm][pf] = tRetVal;
    //pf.setSelected();
  }
  //else if( tRetVal->getLFSCProof()->get_string_length()<=30 && getNumNodes( pf )>10 ){
  //  std::cout << "strange proof " << pf[0] << " " << getNumNodes( pf ) << std::endl;
  //  tRetVal->getLFSCProof()->print( cout );
  //  cout << endl;
  //}
  //if( cvc3_mimic && ( tRetVal->getProvesY()==1 || tRetVal->getProvesY()==2 ) ){
  //  ostringstream ose;
  //  ose << "Warning: After " << pf[0] << ", cvc_mimic, Ymode = " << tRetVal->getProvesY() << std::endl;
  //  print_warning( ose.str().c_str() );
  //}
  //if( tRetVal->getProvesY()==1 ){
  //  if( tRetVal->getLFSCProof()->checkOp()==-1 ){
  //    ostringstream ose;
  //    ose << "Error: After " << pf[0] << ", check op failed. " << tRetVal->getLFSCProof()->getNumChildren() << std::endl;
  //    ose << pf << std::endl;
  //    tRetVal->getLFSCProof()->print_pf( ose );
  //    print_warning( ose.str().c_str() );
  //  }
  //}
  //if( tRetVal->getProvesY()==1 ){
  //  Expr pe;
  //  Expr yexpr;
  //  if( !what_is_proven( pf, pe ) || !getY( pe, yexpr ) ){
  //    ostringstream ose;
  //    ose << "Warning: Bad yMode 1 formula after " << pf[0] << std::endl;
  //    if( pe.isInitialized() )
  //      ose << pe << std::endl;
  //    ose << pf << std::endl;
  //    print_error( ose.str().c_str(), cout );
  //  }
  //}
  return tRetVal;
}

//look at the pattern of the proof, return relevant information in modE
int LFSCConvert::get_proof_pattern( const Expr& pf, Expr& modE )
{
  if( pf[0]==d_cnf_add_unit_str )
  {
    if( pf[2][0]==d_iff_mp_str )
    {
      if( pf[2][3][0]==d_eq_symm_str && pf[2][4][0]==d_if_lift_rule_str )
      {
        if( pf[2][3][4][0]==d_iff_mp_str )
        {
          if( pf[2][3][4][3][0]==d_var_intro_str &&
              pf[2][3][4][4][0]==d_assump_str )
          {
            return 1;
          }
        }
      }
    }
  }
  return 0;
}

LFSCProof* LFSCConvert::make_let_proof( LFSCProof* p )
{
  if( debug_conv )
    cout << "make let proof..." <<  std::endl;
  //std::map< TReturn*, bool >::iterator t_lbend = d_th_trans_lam.begin(), t_lb = d_th_trans_lam.end();
  //--t_lb;
  if( !d_th_trans.empty() ){
    //ExprMap< TReturn* >::iterator t_lb = d_th_trans.begin(), t_lbend = d_th_trans.end();
    ExprMap< bool >::iterator t_lbend = d_th_trans.begin(), t_lb = d_th_trans.end();
    --t_lb;
    while(t_lb != t_lbend){
      for( int cvcm=0; cvcm<2; cvcm++ ){
        if( d_th_trans_map[cvcm].find( (*t_lb).first )!= d_th_trans_map[cvcm].end() )
        {
          TReturn* t = d_th_trans_map[cvcm][(*t_lb).first];
          if( t ){
            std::vector< int > lv;
            std::vector< int > lvUsed;
#ifdef OPTIMIZE
            t->calcL( lv, lvUsed );
#else
            t->getL( lv, lvUsed );
#endif
            if( d_th_trans_lam[cvcm][t] ){
              d_th_trans_lam[cvcm][t] = false;
              int lmt1 = LFSCProof::make_lambda( t->getLFSCProof() );
              RefPtr< LFSCProof > pfV = LFSCPfVar::Make( "@l", lmt1 );
              p = LFSCPfLet::Make( t->getLFSCProof(), (LFSCPfVar*)pfV.get(), p,
                                  t->getProvesY()!=3, lvUsed );
            }
          }
        }
      }
      --t_lb;
      //t_lb++;
    }
  }
  if( debug_conv )
    cout << "...done " << std::endl;
  return p;
}

TReturn* LFSCConvert::make_trusted( const Expr& pf )
{
  Expr e;
  std::vector< int > emptyL;
  std::vector< int > emptyLUsed;
  if( what_is_proven( pf, e ) ){
    int valT = queryM( e, true, true );
    return new TReturn( LFSCPfVar::Make( "@T", valT ), emptyL, emptyLUsed, nullRat, false, 0 );
  }else{
    return new TReturn( LFSCProofGeneric::MakeStr( "@T-unk" ), emptyL, emptyLUsed, nullRat, false, 0 );
  }
}

TReturn* LFSCConvert::do_bso( const Expr& pf, bool beneath_lc, bool rev_pol, 
                              TReturn* t1, TReturn* t2, ostringstream& ose )
{
  std::vector< int > emptyL;
  std::vector< int > emptyLUsed;
  int yMode = -2;
  TReturn* tRetVal = NULL;
  // merge literals
  t1->getL( emptyL, emptyLUsed );
  t2->getL( emptyL, emptyLUsed );
  bool isErr = false;
  if( pf[1].getKind()==PLUS || pf[1].getKind()==MINUS ||
      pf[1].getKind()==MULT || is_eq_kind( pf[1].getKind() ) )
  {
    yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2, rev_pol );
    if( yMode==1 )
    {
      if( pf[1].getKind()==PLUS )
        tRetVal = new TReturn( LFSCLraAdd::Make( t1->getLFSCProof(), t2->getLFSCProof(), EQ, EQ ),
                            emptyL, emptyLUsed, nullRat, false, 1 );
      else if( pf[1].getKind()==MINUS )
        tRetVal = new TReturn( LFSCLraSub::Make( t1->getLFSCProof(), t2->getLFSCProof(), EQ, EQ ),
                            emptyL, emptyLUsed, nullRat, false, 1 );
      else if( pf[1].getKind()==MULT ){
#ifdef PRINT_MAJOR_METHODS
        cout << ";[M]: basic_subst_op1_* " << std::endl;
#endif
        Rational r;
        if( getRat( pf[1][0], r ) ){
          tRetVal = new TReturn( LFSCLraMulC::Make( t2->getLFSCProof(), r, EQ ),
                              emptyL, emptyLUsed, nullRat, false, 1 );
        }else if( getRat( pf[1][1], r ) ){
          tRetVal = new TReturn( LFSCLraMulC::Make( t1->getLFSCProof(), r, EQ ),
                              emptyL, emptyLUsed, nullRat, false, 1 );
        }else{
          print_error( "Could not find rational mult in basic_subst_op1", cout );
          isErr = true;
        }
      }else if( is_eq_kind( pf[1].getKind() ) ){
        RefPtr< LFSCProof > p;
        if( is_opposite( pf[1].getKind() ) ){
          p = LFSCLraSub::Make( t2->getLFSCProof(), t1->getLFSCProof(), EQ, EQ );
        }else{
          p = LFSCLraSub::Make( t1->getLFSCProof(), t2->getLFSCProof(), EQ, EQ );
        }
        tRetVal = new TReturn( p.get(), emptyL, emptyLUsed, nullRat, false, 1 );
      }
      if( !tRetVal && debug_conv ){
        cout << "basic_subst_op1: abort, have to normalize to 2, for " << kind_to_str( pf[1].getKind() ) << std::endl;
      }
    }
  }
  if( !tRetVal ){
    if( !isErr ){
      if( t1->getProvesY()==1 ){
        TReturn::normalize_tr( pf[3], t1, 2, rev_pol );
      }
      if( t2->getProvesY()==1 ){
        TReturn::normalize_tr( pf[4], t2, 2, rev_pol );
      }
    }
    yMode = TReturn::normalize_tret( pf[3], t1, pf[4], t2, rev_pol );
    if( yMode==0 || yMode==2 )
    {
      if( pf[1].getKind()==OR || pf[1].getKind()==AND ||
          pf[1].getKind()==IFF || pf[1].getKind()==PLUS ||
          is_eq_kind( pf[1].getKind() ) || pf[1].getKind()==MULT || pf[1].getKind()==MINUS ){

        ostringstream os1, os2, os3;
        os1 << "(basic_subst_op1_";
        if( yMode==2 )
          os1 << "impl_";
        os1 << kind_to_str( pf[1].getKind() ) << " ";
        os3 << " ";
        os2 << ")";
        std::vector< string > strs;
        std::vector< RefPtr< LFSCProof > > pfs;
        strs.push_back( os1.str() );
        pfs.push_back( LFSCProofExpr::Make( cascade_expr( pf[1][0] ), true ) );
        strs.push_back( os3.str() );
        pfs.push_back( LFSCProofExpr::Make( cascade_expr( pf[2][0] ), true ) );
        strs.push_back( os3.str() );
        pfs.push_back( LFSCProofExpr::Make( cascade_expr( pf[1][1] ), true ) );
        strs.push_back( os3.str() );
        pfs.push_back( LFSCProofExpr::Make( cascade_expr( pf[2][1] ), true ) );
        strs.push_back( os3.str() );
        pfs.push_back( t1->getLFSCProof() );
        strs.push_back( os3.str() );
        pfs.push_back( t2->getLFSCProof() );
        strs.push_back( os2.str() );
        tRetVal = new TReturn( LFSCProofGeneric::Make( pfs, strs ), emptyL, emptyLUsed, nullRat, false, yMode );
      }
    }
  }
  if( !tRetVal ){
    ose << pf[0] << endl;
    for( int a=0; a<pf.arity(); a++ ){
      if( a>=3 ){
        ose << a << ": " << pf[a][0] << std::endl;
        Expr pre;
        what_is_proven( pf[a], pre );
        ose << "wip: " << pre << std::endl;
      }else{
        ose << a << ": " << pf[a] << std::endl;
      }
    }
    ose << "subst kind = " << kind_to_str( pf[1].getKind() ) << std::endl;
    ose << "subst arity = " << pf.arity() << std::endl;
  }
  return tRetVal;
}
