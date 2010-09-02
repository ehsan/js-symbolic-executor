#include "LFSCObject.h"

LFSCPrinter* LFSCObj::printer;
int LFSCObj::formula_i = 1;
int LFSCObj::term_i = 1;
int LFSCObj::trusted_i = 1;
int LFSCObj::tnorm_i = 1;
bool LFSCObj::debug_conv;
bool LFSCObj::debug_var;
bool LFSCObj::cvc3_mimic;
bool LFSCObj::cvc3_mimic_input;
int LFSCObj::lfsc_mode;
Rational LFSCObj::nullRat;
ExprMap< int > LFSCObj::nnode_map;
ExprMap< Expr > LFSCObj::cas_map;
ExprMap< Expr > LFSCObj::skolem_vars;
ExprMap< bool > LFSCObj::temp_visited;
ExprMap<int> LFSCObj::d_formulas;
ExprMap<int> LFSCObj::d_trusted;
ExprMap<int> LFSCObj::d_pn;
ExprMap<int> LFSCObj::d_pn_form;
ExprMap< int > LFSCObj::d_terms;
ExprMap<bool> LFSCObj::input_vars;
ExprMap<bool> LFSCObj::input_preds;
std::map< int, bool > LFSCObj::pntNeeded;
ExprMap<bool> LFSCObj::d_formulas_printed;
Expr LFSCObj::d_pf_expr;
ExprMap<bool> LFSCObj::d_assump_map;
//differentiate between variables and rules
ExprMap<bool> LFSCObj::d_rules;
//boolean resultion rules
Expr LFSCObj::d_bool_res_str;
Expr LFSCObj::d_assump_str;
Expr LFSCObj::d_iff_mp_str;
Expr LFSCObj::d_impl_mp_str;
Expr LFSCObj::d_iff_trans_str;
Expr LFSCObj::d_real_shadow_str;
Expr LFSCObj::d_cycle_conflict_str;
Expr LFSCObj::d_real_shadow_eq_str;
Expr LFSCObj::d_basic_subst_op_str;
Expr LFSCObj::d_mult_ineqn_str;
Expr LFSCObj::d_right_minus_left_str;
Expr LFSCObj::d_eq_trans_str;
Expr LFSCObj::d_eq_symm_str;
Expr LFSCObj::d_canon_plus_str;
Expr LFSCObj::d_refl_str;
Expr LFSCObj::d_cnf_convert_str;
Expr LFSCObj::d_learned_clause_str;
Expr LFSCObj::d_minus_to_plus_str;
Expr LFSCObj::d_plus_predicate_str;
Expr LFSCObj::d_negated_inequality_str;
Expr LFSCObj::d_flip_inequality_str;
Expr LFSCObj::d_optimized_subst_op_str;
Expr LFSCObj::d_iff_true_elim_str;
Expr LFSCObj::d_basic_subst_op1_str;
Expr LFSCObj::d_basic_subst_op0_str;
Expr LFSCObj::d_canon_mult_str;
Expr LFSCObj::d_canon_invert_divide_str;
Expr LFSCObj::d_iff_true_str;
Expr LFSCObj::d_mult_eqn_str;
Expr LFSCObj::d_rewrite_eq_symm_str;
Expr LFSCObj::d_implyWeakerInequality_str;
Expr LFSCObj::d_implyWeakerInequalityDiffLogic_str;
Expr LFSCObj::d_imp_mp_str;
Expr LFSCObj::d_rewrite_implies_str;
Expr LFSCObj::d_rewrite_or_str;
Expr LFSCObj::d_rewrite_and_str;
Expr LFSCObj::d_rewrite_iff_symm_str;
Expr LFSCObj::d_iff_not_false_str;
Expr LFSCObj::d_iff_false_str;
Expr LFSCObj::d_iff_false_elim_str;
Expr LFSCObj::d_not_to_iff_str;
Expr LFSCObj::d_not_not_elim_str;
Expr LFSCObj::d_const_predicate_str;
Expr LFSCObj::d_rewrite_not_not_str;
Expr LFSCObj::d_rewrite_not_true_str;
Expr LFSCObj::d_rewrite_not_false_str;
Expr LFSCObj::d_if_lift_rule_str;
Expr LFSCObj::d_CNFITE_str;
Expr LFSCObj::d_var_intro_str;
Expr LFSCObj::d_int_const_eq_str;
Expr LFSCObj::d_rewrite_eq_refl_str;
Expr LFSCObj::d_iff_symm_str;
Expr LFSCObj::d_rewrite_iff_str;
Expr LFSCObj::d_implyNegatedInequality_str;
Expr LFSCObj::d_uminus_to_mult_str;
Expr LFSCObj::d_lessThan_To_LE_rhs_rwr_str;
Expr LFSCObj::d_rewrite_ite_same_str;
Expr LFSCObj::d_andE_str;
Expr LFSCObj::d_implyEqualities_str;
Expr LFSCObj::d_CNF_str;
Expr LFSCObj::d_cnf_add_unit_str;
Expr LFSCObj::d_minisat_proof_str;
Expr LFSCObj::d_or_final_s;
Expr LFSCObj::d_and_final_s;
Expr LFSCObj::d_ite_s;
Expr LFSCObj::d_iff_s;
Expr LFSCObj::d_imp_s;
Expr LFSCObj::d_or_mid_s;
Expr LFSCObj::d_and_mid_s;
Expr LFSCObj::d_addInequalities_str;


void LFSCObj::initialize( const Expr& pf_expr, int lfscm )
{
  lfsc_mode = lfscm;
  cvc3_mimic = lfsc_mode==2 || lfsc_mode==7 || (lfsc_mode>=20 && lfsc_mode <= 29 );
  cvc3_mimic_input = cvc3_mimic;
  debug_conv = lfsc_mode%10 == 0;
  debug_var = lfsc_mode>10 && ( lfsc_mode%10 == 1 );

  d_pf_expr = pf_expr;
  // initialize rules
  d_bool_res_str = pf_expr.getEM()->newVarExpr("bool_resolution");
  d_assump_str = pf_expr.getEM()->newVarExpr("assumptions");
  d_iff_mp_str = pf_expr.getEM()->newVarExpr("iff_mp");
  d_impl_mp_str = pf_expr.getEM()->newVarExpr("impl_mp");
  d_iff_trans_str = pf_expr.getEM()->newVarExpr("iff_trans");
  d_real_shadow_str = pf_expr.getEM()->newVarExpr("real_shadow");
  d_cycle_conflict_str = pf_expr.getEM()->newVarExpr("cycleConflict");
  d_real_shadow_eq_str = pf_expr.getEM()->newVarExpr("real_shadow_eq");
  d_basic_subst_op_str = pf_expr.getEM()->newVarExpr("basic_subst_op");
  d_mult_ineqn_str = pf_expr.getEM()->newVarExpr("mult_ineqn");
  d_flip_inequality_str = pf_expr.getEM()->newVarExpr("flip_inequality");
  d_right_minus_left_str = pf_expr.getEM()->newVarExpr("right_minus_left");
  d_eq_trans_str = pf_expr.getEM()->newVarExpr("eq_trans");
  d_eq_symm_str = pf_expr.getEM()->newVarExpr("eq_symm");
  d_canon_plus_str = pf_expr.getEM()->newVarExpr("canon_plus");
  d_refl_str = pf_expr.getEM()->newVarExpr("refl");
  d_cnf_convert_str = pf_expr.getEM()->newVarExpr("cnf_convert");
  d_learned_clause_str = pf_expr.getEM()->newVarExpr("learned_clause");
  d_minus_to_plus_str = pf_expr.getEM()->newVarExpr("minus_to_plus");
  d_plus_predicate_str = pf_expr.getEM()->newVarExpr("plus_predicate");
  d_flip_inequality_str = pf_expr.getEM()->newVarExpr("flip_inequality");
  d_negated_inequality_str = pf_expr.getEM()->newVarExpr("negated_inequality");

  d_iff_true_elim_str = pf_expr.getEM()->newVarExpr("iff_true_elim");
  d_basic_subst_op1_str= pf_expr.getEM()->newVarExpr("basic_subst_op1");
  d_basic_subst_op0_str= pf_expr.getEM()->newVarExpr("basic_subst_op0");
  d_canon_mult_str= pf_expr.getEM()->newVarExpr("canon_mult");
  d_canon_invert_divide_str= pf_expr.getEM()->newVarExpr("canon_invert_divide");
  d_iff_true_str= pf_expr.getEM()->newVarExpr("iff_true");
  d_mult_eqn_str= pf_expr.getEM()->newVarExpr("mult_eqn");
  d_rewrite_eq_symm_str= pf_expr.getEM()->newVarExpr("rewrite_eq_symm");
  d_optimized_subst_op_str= pf_expr.getEM()->newVarExpr("optimized_subst_op");
  d_implyWeakerInequality_str= pf_expr.getEM()->newVarExpr("implyWeakerInequality");
  d_implyWeakerInequalityDiffLogic_str = pf_expr.getEM()->newVarExpr("implyWeakerInequalityDiffLogic");
  d_imp_mp_str= pf_expr.getEM()->newVarExpr("impl_mp");
  d_rewrite_implies_str = pf_expr.getEM()->newVarExpr("rewrite_implies");
  d_rewrite_or_str = pf_expr.getEM()->newVarExpr("rewrite_or");
  d_rewrite_and_str = pf_expr.getEM()->newVarExpr("rewrite_and");
  d_rewrite_iff_symm_str = pf_expr.getEM()->newVarExpr("rewrite_iff_symm");
  d_iff_not_false_str = pf_expr.getEM()->newVarExpr("iff_not_false");
  d_iff_false_str = pf_expr.getEM()->newVarExpr("iff_false");
  d_iff_false_elim_str = pf_expr.getEM()->newVarExpr("iff_false_elim");
  d_not_to_iff_str = pf_expr.getEM()->newVarExpr("not_to_iff");
  d_not_not_elim_str = pf_expr.getEM()->newVarExpr("not_not_elim");
  d_const_predicate_str = pf_expr.getEM()->newVarExpr("const_predicate");
  d_rewrite_not_not_str = pf_expr.getEM()->newVarExpr("rewrite_not_not");
  d_rewrite_not_true_str = pf_expr.getEM()->newVarExpr("rewrite_not_true");
  d_rewrite_not_false_str = pf_expr.getEM()->newVarExpr("rewrite_not_false");

  d_if_lift_rule_str = pf_expr.getEM()->newVarExpr("if_lift_rule");
  d_CNFITE_str = pf_expr.getEM()->newVarExpr("CNFITE");
  d_var_intro_str = pf_expr.getEM()->newVarExpr("var_intro");
  d_int_const_eq_str = pf_expr.getEM()->newVarExpr("int_const_eq");
  d_rewrite_eq_refl_str = pf_expr.getEM()->newVarExpr("rewrite_eq_refl");
  d_iff_symm_str = pf_expr.getEM()->newVarExpr("iff_symm");
  d_rewrite_iff_str = pf_expr.getEM()->newVarExpr("rewrite_iff");
  d_implyNegatedInequality_str = pf_expr.getEM()->newVarExpr("implyNegatedInequality");
  d_uminus_to_mult_str = pf_expr.getEM()->newVarExpr("uminus_to_mult");
  d_lessThan_To_LE_rhs_rwr_str = pf_expr.getEM()->newVarExpr("lessThan_To_LE_rhs_rwr");

  d_CNF_str = pf_expr.getEM()->newVarExpr("CNF");
  d_cnf_add_unit_str = pf_expr.getEM()->newVarExpr("cnf_add_unit");
  d_minisat_proof_str = pf_expr.getEM()->newVarExpr("minisat_proof");
  d_rewrite_ite_same_str = pf_expr.getEM()->newVarExpr("rewrite_ite_same");
  d_andE_str = pf_expr.getEM()->newVarExpr("andE");
  d_implyEqualities_str = pf_expr.getEM()->newVarExpr("implyEqualities");
  d_addInequalities_str = pf_expr.getEM()->newVarExpr("addInequalities");

  //reasons for CNF
  d_or_final_s = pf_expr.getEM()->newStringExpr("or_final");
  d_and_final_s = pf_expr.getEM()->newStringExpr("and_final");
  d_ite_s = pf_expr.getEM()->newStringExpr("ite");
  d_iff_s = pf_expr.getEM()->newStringExpr("iff");
  d_imp_s = pf_expr.getEM()->newStringExpr("imp");
  d_or_mid_s = pf_expr.getEM()->newStringExpr("or_mid");
  d_and_mid_s = pf_expr.getEM()->newStringExpr("and_mid");

  // add them to d_rules
  d_rules[d_iff_mp_str]=true;
  d_rules[d_impl_mp_str]=true;
  d_rules[d_iff_trans_str]=true;
  d_rules[d_real_shadow_str]=true;
  d_rules[d_cycle_conflict_str]=true;
  d_rules[d_real_shadow_eq_str]=true;
  d_rules[d_basic_subst_op_str]=true;
  d_rules[d_mult_ineqn_str]=true;
  d_rules[d_flip_inequality_str]=true;
  d_rules[d_right_minus_left_str]=true;
  d_rules[d_eq_trans_str]=true;
  d_rules[d_eq_symm_str]=true;
  d_rules[d_canon_plus_str]=true;
  d_rules[d_refl_str]=true;
  d_rules[d_cnf_convert_str]=true;
  d_rules[d_learned_clause_str]=true;
  d_rules[d_bool_res_str] = true;
  d_rules[d_assump_str] = true;
  d_rules[d_minus_to_plus_str] = true;
  d_rules[d_minus_to_plus_str] = true;
  d_rules[d_plus_predicate_str] = true;
  d_rules[d_flip_inequality_str] = true;
  d_rules[d_negated_inequality_str] = true;
  d_rules[d_iff_true_elim_str] = true;
  d_rules[d_basic_subst_op1_str] = true;
  d_rules[d_basic_subst_op0_str] = true;
  d_rules[d_canon_mult_str] = true;
  d_rules[d_canon_invert_divide_str] = true;
  d_rules[d_iff_true_str] = true;
  d_rules[d_mult_eqn_str] = true;
  d_rules[d_rewrite_eq_symm_str] = true;
  d_rules[d_optimized_subst_op_str] = true;
  d_rules[d_implyWeakerInequality_str] = true;
  d_rules[d_implyWeakerInequalityDiffLogic_str] = true;
  d_rules[d_imp_mp_str] = true;
  d_rules[d_addInequalities_str] = true;
  d_rules[d_rewrite_implies_str] = true;
  d_rules[d_rewrite_or_str] = true;
  d_rules[d_rewrite_and_str] = true;
  d_rules[d_rewrite_iff_symm_str] = true;
  d_rules[d_iff_not_false_str] = true;
  d_rules[d_iff_false_str] = true;
  d_rules[d_iff_false_elim_str] = true;
  d_rules[d_not_to_iff_str] = true;
  d_rules[d_not_not_elim_str] = true;
  d_rules[d_const_predicate_str] = true;
  d_rules[d_rewrite_not_not_str] = true;
  d_rules[d_rewrite_not_true_str] = true;
  d_rules[d_rewrite_not_false_str] = true;

  d_rules[d_if_lift_rule_str] = true;
  d_rules[d_CNFITE_str] = true;
  d_rules[d_var_intro_str] = true;
  d_rules[d_int_const_eq_str] = true;
  d_rules[d_rewrite_eq_refl_str] = true;
  d_rules[d_iff_symm_str] = true;
  d_rules[d_rewrite_iff_str] = true;
  d_rules[d_implyNegatedInequality_str] = true;
  d_rules[d_uminus_to_mult_str] = true;
  d_rules[d_lessThan_To_LE_rhs_rwr_str] = true;

  d_rules[d_CNF_str] = true;
  d_rules[d_cnf_add_unit_str] = true;
  d_rules[d_minisat_proof_str] = true;

  d_rules[d_andE_str] = true;
  d_rules[d_implyEqualities_str] = true;
  d_rules[d_rewrite_ite_same_str] = true;
}


int LFSCObj::getNumNodes( const Expr& pf, bool recount ){
  if( pf.arity()>0 && d_rules[pf[0]] ){
    if( nnode_map.find( pf )==nnode_map.end() ){
      int sum=0;
      for( int a=1; a<pf.arity(); a++ ){
        sum += getNumNodes( pf[a], recount );
      }
      nnode_map[pf] = sum + 1;
      return sum + 1;
    }else if( recount ){
      return nnode_map[pf];
    }else{
      return 1;
    }
  }
  return 0;
}

Expr LFSCObj::cascade_expr( const Expr& e )
{
  if( cas_map.find( e ) != cas_map.end() ){
    return cas_map[e];
  }else{
    Expr ce;
    if( e.getKind()==SKOLEM_VAR ){
      ce = skolem_vars[e];
    }else if( e.getKind()==ITE ){
      ce = Expr( ITE, cascade_expr( e[0] ),
                cascade_expr( e[1] ),
                cascade_expr( e[2] ) );
    }else if( e.arity()==1 ){
      ce = Expr( e.getKind(), cascade_expr( e[0] ) );
    }else if( e.arity()>0 ){
      ce = cascade_expr( e[e.arity()-1]  );
      for( int a=e.arity()-2; a>=0; a-- ){
        ce = Expr( e.getKind(), cascade_expr( e[a] ), ce );
      }
    }else{
      return e;
    }
    cas_map[e] = ce;
    return ce;
  }
}

void LFSCObj::define_skolem_vars( const Expr& e )
{
  if( e.arity()>0 && d_rules[ e[0] ] && !temp_visited[e] )
  {
    temp_visited[e] = true;
    if( e[0] == d_assump_str )
    {
      if( e[1].isIff() && e[1][1].isEq() && e[1][1][1].getKind()==SKOLEM_VAR ){
        Expr ce = cascade_expr( e[1][1][0] );
        skolem_vars[ e[1][1][1] ] = ce;
        //store it in the tmap
        queryT( ce );
      }else{
        Expr ce = cascade_expr( e[1] );
        if( !d_assump_map[ ce ] ){
          ostringstream ose;
          ose << "Unexpected non-discharged assumption " << ce;
          print_error( ose.str().c_str(), cout );
        }
      }
    }
    if( e[0]!=d_learned_clause_str ){
      for( int a=1; a<e.arity(); a++ ){
        define_skolem_vars( e[a] );
      }
    }
  }
}

bool LFSCObj::isVar( const Expr& e )
{
  return (e.getKind()==UCONST && d_rules[e]==false);
}

void LFSCObj::collect_vars(const Expr& e,bool readPred){
  if(isVar(e)){
    if( readPred )
      input_preds[e] = true;
    else
      input_vars[e]=true;
  }else{
    readPred = !is_eq_kind( e.getKind() ) && readPred;
    for(int a=0; a<e.arity(); a++ ){
      collect_vars( e[a], ( readPred || (e.getKind()==ITE && a==0 ) ) );
    }
  }
}

Expr LFSCObj::queryElimNotNot(const Expr& expr)
{
  Expr e = expr;
  while( e.isNot() && e[0].isNot() )
    e = e[0][0];
  return e;
}


Expr LFSCObj::queryAtomic(const Expr& expr, bool getBase)
{
  Expr e = cascade_expr( queryElimNotNot( expr ) );
  if( e.isNot() ){
    if( getBase ){
      return e[0];
    }else{
      if( e[0].isTrue() ){
        e = d_pf_expr.getEM()->falseExpr();
        return e;
      }else if( e[0].isFalse() ){
        e = d_pf_expr.getEM()->trueExpr();
        return e;
      }else if( is_eq_kind( e[0].getKind() ) ){
        return Expr( get_not( e[0].getKind() ), e[0][1], e[0][0] );
      }
    }
  }
  return e;
}

int LFSCObj::queryM(const Expr& expr, bool add, bool trusted)
{
  //cout << "query : " << expr << endl;
  bool neg = false;
  Expr e = cascade_expr( queryElimNotNot( expr ) );
  if( !trusted ){
    if( e.isNot() ){
      neg = true;
      e = e[0];
    }
    int val = d_formulas[e];
    if( val==0 && add )
    {
      if( !e.isInitialized() ){
        print_error( "WARNING: uninitialized e in query", cout );
      }
      d_formulas[e] = formula_i;
      val = formula_i;
      formula_i++;
    }
    return val*(neg ? -1 : 1 );
  }else{
    int val = d_trusted[e];
    if( val==0 && add ){
      d_trusted[e] = trusted_i;
      val = trusted_i;
      trusted_i++;
    }
    return val;
  }
}

int LFSCObj::queryMt(const Expr& expr)
{
  Expr ce = cascade_expr( expr );
  if( !can_pnorm( ce ) ){
    ostringstream os;
    os << "ERROR: cannot make polynomial normalization for " << ce << std::endl;
    print_error( os.str().c_str(), cout );
  }
  int val = d_pn[ce];
  if( val==0 )
  {
    d_pn[ce] = tnorm_i;
    val = tnorm_i;
    tnorm_i++;
  }
  return val;
}

int LFSCObj::queryT( const Expr& e )
{
  Expr ce = cascade_expr( e );
  int val = d_terms[ce];
  if( val==0 ){
    d_terms[ce] = term_i;
    val = term_i;
    term_i++;
  }
  return val;
}

bool LFSCObj::getY( const Expr& e, Expr& pe, bool doIff, bool doLogic )
{
  //cout << "getY = " << e << std::endl;
  Expr ea = queryAtomic( e );
  if( is_eq_kind( ea.getKind() ) ){
    //must be able to pnorm it
    if( can_pnorm( ea[0] ) && can_pnorm( ea[1] ) ){
      if( is_opposite( ea.getKind() ) ){
        pe = Expr( get_normalized( ea.getKind() ), ea[1], ea[0] );
      }else{
        pe = ea;
      }
      return true;
    }else{
      ostringstream ose;
      ose << "Can't pnorm " << ea[0] << " " << ea[1] << std::endl;
      print_error( ose.str().c_str(), cout );
    }
  }
  if( doIff ){
    if( e.arity()==2 )
    {
      Expr pe1;
      Expr pe2;
      if ( e.isIff() ){
        if( getY( e[1], pe2, false ) ){
          if( getY( e[0], pe1, false, pe2.getKind()==TRUE_EXPR || pe2.getKind()==FALSE_EXPR ) ){
            if( pe2.getKind()==TRUE_EXPR ){
              pe = pe1;
              return true;
            }else if( pe1.getKind()==FALSE_EXPR ){
              pe = d_pf_expr.getEM()->trueExpr();
              return true;
            }
            if( pe1.getKind()==pe2.getKind() ){
              pe = Expr( EQ, Expr( MINUS, pe1[0], pe2[0] ), Expr( MINUS, pe1[1], pe2[1] ) );
            }
            return true;
          }
        }
      }
      else if( e.isImpl() ){
        if( getY( e[1], pe2, false, false ) ){
          if( getY( e[0], pe1, false, false ) ){
            if( is_comparison( pe1.getKind() ) && is_comparison( pe2.getKind() ) ){
              pe = Expr( pe1.getKind()==GT && pe2.getKind()==GT ? GT : GE,
                         Expr( MINUS, pe1[0], pe2[0] ), Expr( MINUS, pe1[1], pe2[1] ) );
            }
            return true;
          }
        }
      }
    }
  }
  if( doLogic ){
    if( ea.isFalse() ){
      pe = d_pf_expr.getEM()->trueExpr();
      return true;
    }else if( ea.isTrue() ){
      pe = ea;
      return true;
    }
  }
  return false;
}

bool LFSCObj::isFormula( const Expr& e )
{
  return ( is_eq_kind( e.getKind() ) || e.isAnd() || e.isOr() || e.isImpl() || e.isIff() || e.isFalse() || e.isTrue() || e.isNot() ||
           ( e.getKind()==ITE && isFormula( e[1] ) ) || ( input_preds.find( e )!=input_preds.end() )  );
}

bool LFSCObj::can_pnorm( const Expr& e )
{
  if( is_eq_kind( e.getKind() ) ){
    return can_pnorm( e[0] ) && can_pnorm( e[1] );
  }else if( e.getKind()==PLUS || e.getKind()==MINUS || e.getKind()==MULT || e.getKind()==DIVIDE ){
    return can_pnorm( e[0] ) && can_pnorm( e[1] );
  }else if( e.getKind()==UMINUS ){
    return can_pnorm( e[0] );
  }else if( e.isRational() ){
    return true;
  }else if( e.getKind()==ITE ){
    queryT( e );
    return true;
  }else if( e.isVar() && input_preds.find( e )==input_preds.end() ){
    return true;
  }
  return false;
}

bool LFSCObj::what_is_proven( const Expr& pf, Expr& pe )
{
  if(pf.arity()>0 ){
    if(d_rules[pf[0]]&&pf[0].getKind()==UCONST){
      if( pf[0] == d_assump_str || pf[0] == d_cnf_add_unit_str ||
          pf[0]== d_cnf_convert_str || pf[0] == d_iff_true_elim_str ){
        pe = pf[1];
        return true;
      }
      else if( pf[0] == d_canon_plus_str || pf[0]==d_canon_mult_str ){
        pe = Expr( EQ, pf[1], pf[2] );
        return true;
      }
      else if( pf[0] == d_canon_invert_divide_str )
      {
        Rational r1 = Rational( 1 );
        Expr er1 = d_pf_expr.getEM()->newRatExpr( pf[1][0].getRational() );
        Expr er2 = d_pf_expr.getEM()->newRatExpr( r1/pf[1][1].getRational() );
        pe = Expr( EQ, pf[1], Expr( MULT, er1, er2 ) );
        return true;
      }
      else if( pf[0] == d_iff_trans_str )
      {
        pe = Expr( IFF, pf[1], pf[3] );
        return true;
      }
      else if( pf[0] == d_iff_mp_str || pf[0] == d_impl_mp_str)
      {
        pe = pf[2];
        return true;
      }
      else if( pf[0] == d_eq_trans_str )
      {
        pe = Expr( EQ, pf[2], pf[4] );
        return true;
      }
      else if( pf[0] == d_eq_symm_str )
      {
        pe = Expr( EQ, pf[3], pf[2] );
        return true;
      }
      else if( pf[0] == d_basic_subst_op_str || pf[0] == d_rewrite_and_str ||
               pf[0] == d_rewrite_or_str || pf[0] == d_lessThan_To_LE_rhs_rwr_str ||
               pf[0] == d_mult_ineqn_str || pf[0] == d_plus_predicate_str ||
               pf[0] == d_flip_inequality_str || pf[0] == d_int_const_eq_str ||
               pf[0] == d_const_predicate_str )
      {
        pe = Expr( IFF, pf[1], pf[2] );
        return true;
      }
      else if (pf[0] == d_iff_symm_str){
        pe = pf[2].iffExpr(pf[1]);
        return true;
      }
      else if( pf[0] == d_basic_subst_op0_str )
      {
        if( pf[1].getKind()==UMINUS ){
          pe = Expr( EQ, pf[1], pf[2] );
          return true;
        }else if( pf[1].getKind()==NOT ){
          pe = Expr( IFF, pf[1], pf[2] );
          return true;
        }
      }
      else if( pf[0] == d_mult_eqn_str )
      {
        pe = Expr( IFF, Expr( EQ, pf[1], pf[2] ),
                        Expr( EQ, Expr( MULT, pf[1], pf[3] ), Expr( MULT, pf[2], pf[3] ) ) );
        return true;
      }
      else if( pf[0] == d_real_shadow_str )
      {
        pe = Expr( ( pf[1].getKind()==LE && pf[2].getKind()==LE ) ? LE : LT, pf[1][0], pf[2][1] );
        return true;
      }
      else if(pf[0] == d_real_shadow_eq_str){
        pe = Expr(EQ, pf[2][0], pf[2][1]);
        return true;
      }
      else if( pf[0] == d_optimized_subst_op_str || pf[0] == d_basic_subst_op1_str )
      {
        if( pf[1].getKind()==AND || pf[1].getKind()==OR || pf[1].getKind()==IFF || is_eq_kind( pf[1].getKind() ) || 
            ( pf[1].getKind()==ITE && isFormula( pf[1] ) ) ){
          pe = Expr( IFF, pf[1], pf[2] );
          return true;
        }else if( pf[1].getKind()==ITE || pf[1].getKind()==PLUS || pf[1].getKind()==MINUS || pf[1].getKind()==MULT ){
          pe = Expr( EQ, pf[1], pf[2] );
          return true;
        }
      }
      else if( pf[0] == d_andE_str )
      {
        pe = pf[2][ pf[1].getRational().getNumerator().getInt() ];
        return true;
      }
      else if( pf[0] == d_rewrite_implies_str )
      {
        Expr e1 = Expr( IMPLIES, pf[1], pf[2] );
        Expr e2 = Expr( NOT, pf[1] );
        Expr e3 = Expr( OR, e2, pf[2] );
        pe = Expr( IFF, e1, e3 );
        return true;
      }
      else if( pf[0] == d_rewrite_eq_symm_str )
      {
        Expr e1 = Expr( EQ, pf[2], pf[3] );
        Expr e2 = Expr( EQ, pf[3], pf[2] );
        pe = Expr( IFF, e1, e2 );
        return true;
      }
      else if( pf[0] == d_rewrite_iff_symm_str )
      {
        Expr e1 = Expr( IFF, pf[1], pf[2] );
        Expr e2 = Expr( IFF, pf[2], pf[1] );
        pe = Expr( IFF, e1, e2 );
        return true;
      }
      else if( pf[0] == d_rewrite_ite_same_str )
      {
        pe = Expr( EQ, Expr( ITE, pf[2], pf[3], pf[3] ), pf[3] );
        return true;
      }
      else if( pf[0] == d_rewrite_eq_refl_str )
      {
        pe = Expr( IFF, Expr( EQ, pf[2], pf[2] ), d_pf_expr.getEM()->trueExpr() );
        return true;
      }
      else if( pf[0] == d_refl_str )
      {
        if( isFormula( pf[1] ) )
          pe = Expr( IFF, pf[1], pf[1] );
        else
          pe = Expr( EQ, pf[1], pf[1] );
        return true;
      }
      else if( pf[0] == d_rewrite_not_not_str )
      {
        Expr e1 = Expr( NOT, pf[1] );
        pe = Expr( NOT, e1 );
        return true;
      }
      else if( pf[0] == d_not_to_iff_str )
      {
        pe = Expr( IFF, Expr( NOT, pf[1] ), d_pf_expr.getEM()->falseExpr() );
        return true;
      }
      else if( pf[0] == d_minus_to_plus_str )
      {
        Expr er1 = d_pf_expr.getEM()->newRatExpr( Rational( -1 ) );
        pe = Expr( EQ, Expr( MINUS, pf[1], pf[2] ), Expr( PLUS, pf[1], Expr( MULT, er1, pf[2] ) ) );
        return true;
      }
      else if( pf[0] == d_right_minus_left_str )
      {
        Expr er1 = d_pf_expr.getEM()->newRatExpr( Rational( 0 ) );
        Expr e1 = Expr( pf[1].getKind(), er1, Expr( MINUS, pf[1][1], pf[1][0] ) );
        pe = Expr(IFF, pf[1], e1);
        return true;
      }
      else if( pf[0] == d_negated_inequality_str )
      {
        pe = Expr( IFF, pf[1], Expr( get_not( pf[1][0].getKind() ), pf[1][0][0], pf[1][0][1] ) );
        return true;
      }
      else if( pf[0] == d_iff_false_elim_str )
      {
        pe = queryElimNotNot( Expr( NOT, pf[1] ) );
        return true;
      }
      else if( pf[0] == d_iff_true_str )
      {
        pe = Expr( IFF, pf[1], d_pf_expr.getEM()->trueExpr() );
        return true;
      }
      else if( pf[0] == d_iff_not_false_str )
      {
        pe = Expr( IFF, queryElimNotNot( Expr( NOT, pf[1] ) ), d_pf_expr.getEM()->falseExpr() );
        return true;
      }
      else if( pf[0] == d_uminus_to_mult_str )
      {
        Expr er1 = d_pf_expr.getEM()->newRatExpr( Rational( -1 ) );
        pe = Expr( EQ, Expr( UMINUS, pf[1] ), Expr( MULT, er1, pf[1] ) );
        return true;
      }
      else if( pf[0] == d_rewrite_not_true_str )
      {
        pe = Expr( IFF, Expr( NOT, d_pf_expr.getEM()->trueExpr() ),
                        d_pf_expr.getEM()->falseExpr() );
        return true;
      }
      else if( pf[0] == d_rewrite_not_false_str )
      {
        pe = Expr( IFF, Expr( NOT, d_pf_expr.getEM()->falseExpr() ),
                        d_pf_expr.getEM()->trueExpr() );
        return true;
      }
      else if( pf[0] == d_cycle_conflict_str )
      {
        pe = d_pf_expr.getEM()->falseExpr();
        return true;
      }
      else if(pf[0] == d_implyNegatedInequality_str)
      {
        pe = pf[1].impExpr(pf[3]);
        return true;
      }
      else if(pf[0] == d_implyWeakerInequality_str){
        pe = pf[1].impExpr(pf[2]);
        return true;
      }
      else if( pf[0] == d_rewrite_iff_symm_str )
      {
        Expr e1 = Expr( IFF, pf[1], pf[2] );
        Expr e2 = Expr( IFF, pf[2], pf[1] );
        pe = Expr( IFF, e1, e2 );
        return true;
      }
      else if( pf[0] == d_rewrite_iff_str){
        Expr e = Expr( IFF, pf[1], pf[2]);
        Expr e_true = d_pf_expr.getEM()->trueExpr();
        Expr e_false = d_pf_expr.getEM()->falseExpr();

        if(pf[1] == pf[2]){
          pe = e.iffExpr(d_pf_expr.getEM()->trueExpr());
          return true;
        }

        if(pf[1] == e_true){
          pe = e.iffExpr(e_true);
          return true;
        }
        if(pf[1] == e_false){
          pe = e.iffExpr(e_false);
          return true;
        }

        if(pf[1].isNot() && pf[1][0] == pf[2]){
          pe = e.iffExpr(pf[2].negate());
          return true;
        }

       if(pf[2] == e_true){
          pe = e.iffExpr(e_true);
          return true;
        }

        if(pf[2] == e_false){
          pe = e.iffExpr(e_false);
          return true;
        }

        if(pf[2].isNot() && pf[2][0] == pf[1]){
          pe = e.iffExpr(pf[1].negate());
          return true;
        }

        if(pf[1] < pf[2]){
          Expr e_sym = Expr(IFF, pf[2], pf[1]);
          pe = e.iffExpr(e_sym);
          return true;
        }
        pe = e.iffExpr(e);
        return true;
      }
      else if(pf[0] == d_implyEqualities_str){
        pe = Expr(AND, pf[1][0]);
        return true;
      }
    }
  }
  ostringstream ose;
  ose << "What_is_proven, unknown: (" << d_rules[pf[0]] << "): " << pf[0];
  print_error( ose.str().c_str(), cout );
  return false;
}
