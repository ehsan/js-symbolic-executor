#include "LFSCPrinter.h"


LFSCPrinter::LFSCPrinter( Expr pf_expr, Expr qExpr, std::vector<Expr> assumps,
                          int lfscm, CommonProofRules* commonRules ):
                            d_user_assumptions(assumps),
                            d_common_pf_rules(commonRules){

  printer = this;

  if( !qExpr.isFalse() ){
    d_user_assumptions.push_back( cascade_expr( Expr( NOT, qExpr ) ) );
  }

  Obj::initialize();

  let_i = 1;
  LFSCObj::initialize( pf_expr, lfscm );
  converter = new LFSCConvert( lfscm );
}

///////////////////////////////////////
// main print method
///////////////////////////////////////

void LFSCPrinter::print_LFSC( const Expr& pf )
{
  ostringstream cparen;

  //(AJR-1) Print the input formula and (: bottom ascription

  cout << "(check " << endl;
  cparen << ")";

  // collecting variables from assumptions
  std::vector<Expr>::iterator a = d_user_assumptions.begin(), aend = d_user_assumptions.end();
  while(a!=aend){
    Expr ce = cascade_expr( *a );
    queryM( ce );
    d_assump_map[ ce ] = true;
    collect_vars(*a);
    a++;
  }

  //////scan for the assumptions
  //std::vector< Expr > assumps;
  //collect_assumptions( pf, assumps );
  ////we must record skolemizations
  //for( int a=1; a<(int)assumps.size(); a++ ){
  //  if( !d_assump_map[ assumps[a] ] ){
  //    ostringstream ose;
  //    ose << "Unexpected non-discharged assumption " << assumps[a];
  //    print_error( ose.str().c_str(), cout );
  //  }
  //}

  //printing variables
  ExprMap<bool>::iterator v = input_vars.begin(), vend = input_vars.end();
  while(v!= vend){
    cout<<"(% "<<(*v).first<<" var_real"<<endl;
    v++;
    cparen<<")";
  }
  v = input_preds.begin(), vend = input_preds.end();
  while(v!= vend){
    cout<<"(% "<<(*v).first<<" formula"<<endl;
    v++;
    cparen<<")";
  }
  //cout << "here1" << std::endl;
  //(AJR-2) Run T0( pf )
  define_skolem_vars( pf );
  //cout << "here2" << std::endl;
  //convert the proof
  converter->convert( pf );

  //make the let map for input formulas
  a = d_user_assumptions.begin();
  while(a!=aend){
    make_let_map( cascade_expr( *a ) );
    a++;
  }
  //make the let map for trusted formulas
  ExprMap<int>::iterator j = d_trusted.begin(), jend = d_trusted.end();
  while( j != jend){
    make_let_map( cascade_expr( (*j).first ) );
    j++;
  }
  //make the let map for output atomic formulas and terms
  ExprMap<bool>::iterator j2 = d_formulas_printed.begin(), j2end = d_formulas_printed.end();
  while( j2 != j2end){
    if( (*j2).second ){
      make_let_map( cascade_expr( (*j2).first ) );
    }
    j2++;
  }
  //j = d_terms.begin(), jend = d_terms.end();
  //while( j != jend){
  //  make_let_map((*j).first);
  //  j++;
  //}

  ////output skolem vars
  //j = skolem_vars.begin(), jend = skolem_vars.end();
  //while( j != jend ){
  //  if( (*j).second!=0 ){
  //    cout<<"(% "<<(*j).first<<" var_real"<<endl;
  //    cparen << ")";
  //  }
  //  j++;
  //}

  //output let definitions
  j2 = d_print_visited_map.begin(), j2end = d_print_visited_map.end();
  while( j2 != j2end ){
    int val = d_print_map[(*j2).first];
    if( val!=0 ){
      cout << "(@ ";
      d_print_map[(*j2).first] = 0;
      if( isFormula( (*j2).first ) ){
        cout << "@f" << val << " ";
        print_formula( (*j2).first, cout );
      }else{
        cout << "@x" << val << " ";
        print_terms( (*j2).first, cout );
      }
      d_print_map[(*j2).first] = val;
      cout << endl;
      cparen << ")";
    }
    j2++;
  }
  if( !d_print_map.empty() )
    cout << endl;

  // printing user assumptions
  a = d_user_assumptions.begin();
  int m = 1;
  while(a!=aend){
    cout<<"(% @F"<<m<<" (th_holds ";
    print_formula(*a, cout);
    cout<<")"<<endl;
    a++;
    m++;
    cparen << ")";
  }

  //print trusted formulas
  j = d_trusted.begin(), jend = d_trusted.end();
  while( j != jend){
    cout <<"(% @T" << (*j).second <<" (th_holds ";
    print_formula((*j).first, cout);
    cout<<")"<<endl;
    cparen << ")";
    j++;
  }

  cout << "(: bottom" << endl;
  cparen << ")";


  //outer lambda abstractions
  //cout << "number of outer lam abstractions = " << LFSCProof::lambdaCounter << std::endl;
  RefPtr< LFSCProof > lambda_pf = converter->getLFSCProof();


  ////debug----
  //j = d_formulas.begin(), jend = d_formulas.end();
  //while( j != jend){
  //  ExprMap< int >::iterator jPrev = j;
  //  j++;
  //  while( j != jend ){
  //    Expr e1 = cascade_expr( (*j).first );
  //    Expr e2 = cascade_expr( (*jPrev).first );
  //    if( e1==e2 ){
  //      ostringstream ose;
  //      ose << "Warning: Atomizing identical formulas " << (*j).second << " " << (*jPrev).second << std::endl;
  //      print_error( ose.str().c_str(), cout );
  //    }
  //    j++;
  //  }
  //  j = jPrev;
  //  j++;
  //}
  ////debug----

  //(AJR-3) Print the atoms used in the proof, these are contained in M.
  j = d_formulas.begin(), jend = d_formulas.end();
  while( j != jend){
    cout <<"(decl_atom ";
    //if( d_formulas_printed[(*j).first] ){     //HACK to ignore this
      print_formula( (*j).first, cout );
    //}else{
    //  cout << "_";
    //}
    cout<< " (\\ @b"<<(*j).second<<" (\\ @a"<<(*j).second<<endl;
    cparen << ")))";
    j++;
  }
  //need to print out atomized terms too
  j = d_terms.begin(), jend = d_terms.end();
  while( j != jend){
    cout <<"(decl_term_atom ";
    print_terms( (*j).first, cout );
    cout<< " (\\ @bt"<<(*j).second<<" (\\ @at"<<(*j).second<<endl;
    cparen << ")))";
    j++;
  }

  //(AJR-4) Print all polynomial normalization proofs.  These are stored in M_t.
  //print out the term normalizations
  j = d_pn_form.begin(), jend = d_pn_form.end();
  while(j !=jend ){
    pntNeeded[ (*j).second ] = true;
    j++;
  }
  j = d_pn.begin(), jend = d_pn.end();
  while(j !=jend){
    if( cvc3_mimic || pntNeeded[ (*j).second ] ){
      cout << "(pn_let _ _ ";
      Expr ce = cascade_expr( (*j).first );
      print_poly_norm( ce, cout);
      cout << "(\\ @pnt" << (*j).second << endl;
      cparen << "))";
    }
    j++;
  }

  //print out the equation normalizations
  j = d_pn_form.begin(), jend = d_pn_form.end();
  while(j !=jend){
    cout << "(poly_norm_" << kind_to_str( (*j).first.getKind() ) << " _ _ _ @pnt";
    //mapped to the polynomial norm proof
    cout << (*j).second << " ";
    //print out the same number as the equation in M
    cout << "(\\ @pn" << abs( queryM( (*j).first ) ) << endl;
    cparen << "))";
    j++;
  }

  //(AJR-5) print the proof and closing parentheses.
  if( lfsc_mode%10==7 ){
    LFSCProof::indentFlag = true;
    lambda_pf->print_structure( cout );
  }else
    lambda_pf->print( cout );
  cout << endl;


  //print closing parentheses
  cout << cparen.str() << endl;
}


void LFSCPrinter::print_poly_norm(const Expr& expr, std::ostream& s, bool pnRat, bool ratNeg ){
  // if +, -, etc.
  if(expr.arity()==2 ){
    if( expr.getKind()==MULT ){
      ostringstream cparen;
      int nrIndex = -1;    //the non-rational child
      for( int a=0; a<2; a++ ){
        if( nrIndex==-1 )
        {
          Expr ec = expr[a];
          bool rNeg = ratNeg;
          while( ec.getKind()==UMINUS ){
            ec = ec[0];
            if( !cvc3_mimic )
              rNeg = !rNeg;
          }
          if( ec.isRational() || ec.getKind()==DIVIDE )
          {
            s<<"(pn_mul_";
            if( cvc3_mimic && expr[a].getKind()==UMINUS ){
              s << "u-_";
            }
            s<< "c_" << ( a==0 ? "L" : "R" );
            s<<" _ _ _ ";
            print_poly_norm( ec, s, false, rNeg );
            s << " ";
            nrIndex = (1-a);
            cparen << ")";
          }
        }
      }
      if( nrIndex==-1 )
      {
        ostringstream ose;
        ose << "ERROR: Multiplying by non-constant " << expr;
        print_error( ose.str().c_str(), s );
      }
      else
      {
        print_poly_norm(expr[nrIndex],s);
      }
      s << cparen.str();
    }
    else if( expr.getKind()==DIVIDE )
    {
      //this should be 2 constants
      if( expr[0].isRational() && expr[1].isRational() )
      {
        if( pnRat )
          s<<"(pn_const ";
        Rational r = expr[0].getRational();
        print_rational_divide( ratNeg ? -r : r, expr[1].getRational(), s );
        if( pnRat )
          s << ")";
      }
      else
      {
        print_error("ERROR: Pn Dividing by non-constant", s );
      }
    }
    else
    {
      //TODO: checks for appropriate op
      //cout<<"e0 and e1"<<expr[0]<<" "<<expr[1]<<endl;
      s<<"(pn_"<<kind_to_str(expr.getKind())<<" _ _ _ _ _ ";
      print_poly_norm(expr[0],s);
      s<<" ";
      print_poly_norm(expr[1],s);
      s<<")";
    }
  }else if(expr.getKind()==UMINUS ){
    if( !cvc3_mimic )
      print_poly_norm( expr[0], s, pnRat, !ratNeg );
    else{
      s << "(pn_u- _ _ _ ";
      print_poly_norm( expr[0], s, pnRat, ratNeg );
      s << ")";
    }
  }else if(expr.isRational()){
    if( pnRat )
      s<<"(pn_const ";
    Rational r = expr.getRational();
    print_rational( ratNeg ? -r : r, s );
    if( pnRat )
      s << ")";
  }
  else if( expr.getKind()==SKOLEM_VAR )
  {
    bool success = false;
    if( skolem_vars.find( expr )!=skolem_vars.end() )
    {
      int val = d_terms[skolem_vars[expr]];
      if( val!=0 ){
        success = true;
        s << "(pn_var_atom _ _ @at" << val << ")";
      }
    }
    if( !success ){
      ostringstream ose;
      ose << "Trying to pn_var_atom a non-atomized skolem var " << expr;
      print_error( ose.str().c_str(), cout );
    }
  }
  else if( expr.getKind()==ITE ){
    int val = d_terms[expr];
    if( val!=0 ){
      s << "(pn_var_atom _ _ @at" << val << ")";
    }else{
      ostringstream ose;
      ose << "Trying to pn_var_atom a non-atomized ITE " << expr;
      print_error( ose.str().c_str(), cout );
    }
  }else if(expr.isVar()){
    s<<"(pn_var "<<expr<<")";
  }
  else{
    ostringstream ose;
    ose<<"ERROR printing polynomial norm for "<<expr;
    print_error( ose.str().c_str(), s );
  }
}

// recursively prints arithm terms
void LFSCPrinter::print_terms_h( const Expr& expr,std::ostream& s ){
  int val = d_print_map[expr];
  if( val!=0 ){
    s << "@x" << val;
  }else if(expr.isRational()){
    s<<"(a_real ";
    print_rational( expr.getRational(), s );
    s<<")";
  }else if(expr.isVar()){
    s<<"(a_var_real "<<expr<<")";
  }else if(expr.arity()==2 ){
    if( expr.getKind()==DIVIDE ){
      if( expr[0].isRational() && expr[1].isRational() ){
        s<<"(a_real ";
        print_rational_divide( expr[0].getRational(), expr[1].getRational(), s );
        s<<")";
      }else{
        print_error( "ERROR: Dividing by non constant", s );
      }
    }else{
      //TODO: checks for appropriate op
      s<<"("<<kind_to_str(expr.getKind())<<"_Real ";
      print_terms_h(expr[0],s);
      s<< " ";
      print_terms_h(expr[1],s);
      s<<")";
    }
  }else if( expr.getKind()==ITE ){
    s << "(ite Real ";
    print_formula_h( expr[0], s );
    s << " ";
    print_terms_h( expr[1], s );
    s << " ";
    print_terms_h( expr[2], s );
    s << ")";
  }else if( expr.getKind()==UMINUS ){
    if( !cvc3_mimic ){ 
      s<<"(a_real ";
      if( expr[0].isRational() ){
        Rational r = expr[0].getRational();
        r = -r;
        print_rational( r, s );
      }else if( expr[0].getKind()==DIVIDE && expr[0][0].isRational() && expr[0][1].isRational() ){
        print_rational_divide( -expr[0][0].getRational(), expr[0][1].getRational(), s );
      }else{
        cout << "cannot determine rational " << expr << endl;
      }
      s<<")";
    }else{
      s<<"(u-_Real ";
      print_terms_h( expr[0], s );
      s<<")";
    }
  }else if(expr.arity()>2){
    //cout<<"term debug"<<expr<<" "<<expr.arity()<<endl;
    vector<Expr> kids = expr.getKids();
    vector<Expr>::iterator i = kids.begin(), iend= kids.end();
    while(i+1!=iend){
      s<<"("<<kind_to_str(expr.getKind())<<"_Real ";
      print_terms_h(*i,s);
      i++;
      s << " ";
    }
    print_terms_h(*i,s);
    for(int j=0; j<expr.arity();j++){
      s<<")";

    }
  }else{
    ostringstream os;
    os << "ERROR printing term "<<expr<<" "<<expr.arity();
    print_error( os.str().c_str(), s );
  }
}

void LFSCPrinter::print_formula_h(const Expr& clause, std::ostream& s){
  int val = d_print_map[clause];
  if( val!=0 ){
    s << "@f" << val;
  }else if(clause.isNot()){
    s<<"(not ";
    print_formula_h(clause[0],s);
    s<<")";
  }else if(clause.isOr()){
    s<<"(or ";
    print_formula_h(clause[0],s);
    s << " ";
    print_formula_h(clause[1],s);
    s<<")";
  }else if(clause.isAnd()){
    s<<"(and ";
    print_formula_h(clause[0],s);
    s << " ";
    print_formula_h(clause[1],s);
    s<<")";
  }else if(clause.isImpl()){
    s<<"(impl ";
    print_formula_h(clause[0],s);
    s << " ";
    print_formula_h(clause[1],s);
    s<<")";
  }else if(clause.isIff()){
    s<<"(iff ";
    print_formula_h(clause[0],s);
    s << " ";
    print_formula_h(clause[1],s);
    s<<")";
  }else if(clause.getKind()==ITE){
    s<<"(ifte ";
    print_formula_h( clause[0], s );
    s << " ";
    print_formula_h( clause[1], s );
    s << " ";
    print_formula_h( clause[2], s );
    s << ")";
  }else if( is_eq_kind( clause.getKind() ) ){
    int k = clause.getKind();
    s<<"("<<kind_to_str(k);
    s<<(is_smt_kind( k ) ? " " : "_" );
    s<<"Real ";
    print_terms_h(clause[0],s);
    s << " ";
    print_terms_h(clause[1],s);
    s<<")";
  }else if( clause.isFalse() ){
    s << "false";
  }else if( clause.isTrue() ){
    s << "true";
  }else{
    s << clause;
  }
}

void LFSCPrinter::make_let_map( const Expr& e ){
  if( e.arity()<=1 || d_print_visited_map.find( e )==d_print_visited_map.end() ){
    for( int a=0; a<(int)e.arity(); a++ ){
      make_let_map( e[a] );
    }
    if( e.arity()>1 ){
      if( d_print_map[e]==0 ){
        d_print_map[e] = let_i;
        let_i++;
      }
      d_print_visited_map[e] = true;
    }
  }
}
