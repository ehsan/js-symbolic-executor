#ifndef LFSC_OBJ_H_
#define LFSC_OBJ_H_

#include "Object.h"
#include "Util.h"

class LFSCPrinter;

class LFSCObj : public Obj
{
public:
  LFSCObj(){}
  static void initialize( const Expr& pf_expr, int lfscm );
protected:
  //the printer object
  static LFSCPrinter* printer;
  //counters
  static int formula_i;
  static int trusted_i;
  static int term_i;
  static int tnorm_i;
  //options for the conversion
  static int lfsc_mode;
  static bool debug_conv;
  static bool debug_var;
  static bool cvc3_mimic;
  static bool cvc3_mimic_input;
  //null rational
  static Rational nullRat;
  //get number of nodes
  static ExprMap< int > nnode_map;
  static int getNumNodes( const Expr& pf, bool recount = false );
  //cascade expr
  static ExprMap< Expr > cas_map;
  static Expr cascade_expr( const Expr& e );
  //skolem variables
  static ExprMap< Expr > skolem_vars;    //with the expr they point to
  static ExprMap< bool > temp_visited;
  static void define_skolem_vars( const Expr& e );
  //is variable
  static bool isVar( const Expr& e );
  //collect free variables
  static void collect_vars( const Expr& e, bool readPred = true );
protected:
  // this is actually the M map <formula, int> where M = {v_i -> non-negated formula}
  static ExprMap<int> d_formulas;
  //trusted formulas
  static ExprMap<int> d_trusted;
  // this is the M_t map <term, int> where M_t = { v_i -> term }
  static ExprMap<int> d_pn;
  //this is the equations that will use the d_pn map.  They are mapped to the index of the pn_i they will use
  static ExprMap<int> d_pn_form;
  //similar to m, but with terms
  static ExprMap<int> d_terms;
  //input variables
  static ExprMap<bool> input_vars;
  //input predicates
  static ExprMap<bool> input_preds;
  //pnt that are needed to print
  static std::map< int, bool > pntNeeded;
  //atoms that must be printed
  static ExprMap<bool> d_formulas_printed;
  //original proof expression
  static Expr d_pf_expr;
  //assumptions
  static ExprMap<bool> d_assump_map;
protected:
  //eliminate not not
  static Expr queryElimNotNot(const Expr& expr);
  //get base will get you the base formula, i.e. ~( a = b ) returns ( a = b )
  //get base = false will get you the equivalent atomic, i.e. ~( a = b ) returns ( b != a )
  static Expr queryAtomic(const Expr& expr, bool getBase = false );
  //returns a integer v, +v means M( v ) = expr, -v means M( v ) = expr', where expr := NOT expr'
  //add is whether or not to add it to M, or just query
  static int queryM(const Expr& expr, bool add = true, bool trusted = false);
  //returns an integer v, where M_t( v ) = expr
  static int queryMt(const Expr& expr);
  //similar to m, but this time it is with terms
  static int queryT( const Expr& e );
  //get Y
  static bool getY( const Expr& e, Expr& pe, bool doIff = true, bool doLogic = true );
  //is this expr a formula
  static bool isFormula( const Expr& e );
  //can this expr be polynomial normalized
  static bool can_pnorm( const Expr& e );
  //what is proven
  static bool what_is_proven( const Expr& pf, Expr& pe );
protected:
  // differentiate between variables and rules
  static ExprMap<bool> d_rules;
  // boolean resultion rules
  static Expr d_bool_res_str;
  static Expr d_assump_str;
  // arithmetic rules
  static Expr d_iff_mp_str;
  static Expr d_impl_mp_str;
  static Expr d_iff_trans_str;
  static Expr d_real_shadow_str;
  static Expr d_cycle_conflict_str;
  static Expr d_real_shadow_eq_str;
  static Expr d_basic_subst_op_str;
  static Expr d_mult_ineqn_str;
  static Expr d_right_minus_left_str;
  static Expr d_eq_trans_str;
  static Expr d_eq_symm_str;
  static Expr d_canon_plus_str;
  static Expr d_refl_str;
  static Expr d_cnf_convert_str;
  static Expr d_learned_clause_str;
  static Expr d_minus_to_plus_str;
  static Expr d_plus_predicate_str;
  static Expr d_negated_inequality_str;
  static Expr d_flip_inequality_str;
  static Expr d_optimized_subst_op_str;
  static Expr d_iff_true_elim_str;
  static Expr d_basic_subst_op1_str;
  static Expr d_basic_subst_op0_str;
  static Expr d_canon_mult_str;
  static Expr d_canon_invert_divide_str;
  static Expr d_iff_true_str;
  static Expr d_mult_eqn_str;
  static Expr d_rewrite_eq_symm_str;
  static Expr d_implyWeakerInequality_str;
  static Expr d_implyWeakerInequalityDiffLogic_str;
  static Expr d_imp_mp_str;
  static Expr d_rewrite_implies_str;
  static Expr d_rewrite_or_str;
  static Expr d_rewrite_and_str;
  static Expr d_rewrite_iff_symm_str;
  static Expr d_iff_not_false_str;
  static Expr d_iff_false_str;
  static Expr d_iff_false_elim_str;
  static Expr d_not_to_iff_str;
  static Expr d_not_not_elim_str;
  static Expr d_const_predicate_str;
  static Expr d_rewrite_not_not_str;
  static Expr d_rewrite_not_true_str;
  static Expr d_rewrite_not_false_str;
  static Expr d_if_lift_rule_str;
  static Expr d_CNFITE_str;
  static Expr d_var_intro_str;
  static Expr d_int_const_eq_str;
  static Expr d_rewrite_eq_refl_str;
  static Expr d_iff_symm_str;
  static Expr d_rewrite_iff_str;
  static Expr d_implyNegatedInequality_str;
  static Expr d_uminus_to_mult_str;
  static Expr d_lessThan_To_LE_rhs_rwr_str;
  static Expr d_rewrite_ite_same_str;
  static Expr d_andE_str;
  static Expr d_implyEqualities_str;
  static Expr d_addInequalities_str;
  //CNF rules
  static Expr d_CNF_str;
  static Expr d_cnf_add_unit_str;
  static Expr d_minisat_proof_str;
  //reasons for CNF
  static Expr d_or_final_s;
  static Expr d_and_final_s;
  static Expr d_ite_s;
  static Expr d_iff_s;
  static Expr d_imp_s;
  static Expr d_or_mid_s;
  static Expr d_and_mid_s;
};

#endif
