#ifndef LFSC_PRINTER_H_
#define LFSC_PRINTER_H_

#include "TReturn.h"
#include "LFSCConvert.h"

class LFSCPrinter : public LFSCObj{
private:
  //user assumptions
  std::vector <Expr> d_user_assumptions;
  //the converter object
  RefPtr< LFSCConvert > converter;
  //count for lets
  int let_i;
  //common proof rules (need this?)
  CommonProofRules* d_common_pf_rules;
  //for printing formulas
  ExprMap<int> d_print_map;
  ExprMap<bool> d_print_visited_map;
  //make the expr into possible let's
  void make_let_map( const Expr& e );
  //print the polynomial normalization
  void print_poly_norm(const Expr& expr, std::ostream& s, bool pnRat = true, bool ratNeg = false );
  void print_terms_h(const Expr& expr,std::ostream& s );
  void print_formula_h(const Expr& clause, std::ostream& s );
 public:
  LFSCPrinter(const Expr pf_expr, Expr qExpr, std::vector<Expr> assumps, int lfscm, CommonProofRules* commonRules);
  
  //print the LFSC proof for the cvc3 proof
  void print_LFSC(const Expr& pf_expr);

  //this is an expression that will be printed
  void set_print_expr( const Expr& expr ) { make_let_map( expr ); }
  //print expression
  void print_expr(const Expr& expr, std::ostream& s){
    if( isFormula( expr ) )
      print_formula( expr, s );
    else
      print_terms( expr, s );
  }
  //print formula
  void print_formula(const Expr& clause, std::ostream& s ){
    //if( clause!=cascade_expr( clause, false ) )
    //  cout << "Warning: printing non-cascaded formula " << clause  << std::endl;
    print_formula_h( cascade_expr( clause ), s );
  }
  //print term
  void print_terms(const Expr& expr,std::ostream& s ){
    //if( expr!=cascade_expr( expr, false ) )
    //  cout << "Warning: printing non-cascaded term " << expr << std::endl;
    print_terms_h( cascade_expr( expr ), s );
  }
};


#endif
