#include "Util.h"

bool Obj::errsInit = false;
ofstream Obj::errs;
bool Obj::indentFlag = false;

// helper utility functions
void ajr_debug_print( const Expr& pf )
{
  for( int a=0; a<pf.arity(); a++ )
  {
    cout << a << ": ";
    pf[a].print();
  }
}

string kind_to_str(int knd ){

  string knd_str;
  switch(knd){
  case EQ: knd_str = "="; break;
  case LE: knd_str = "<="; break;
  case LT: knd_str = "<"; break;
  case GE: knd_str = ">="; break;
  case GT: knd_str = ">"; break;
  case DISTINCT: knd_str = "distinct"; break;
  case PLUS: knd_str = "+"; break;
  case MINUS: knd_str = "-"; break;
  case MULT: knd_str = "*"; break;
  case AND: knd_str = "and"; break;
  case OR: knd_str = "or";break;
  case NOT: knd_str = "not";break;
  case ITE: knd_str = "ite";break;
  case IFF: knd_str = "iff";break;
  case UMINUS: knd_str = "u-";break;
  default:
    {
      knd_str="Unknown";
      ostringstream ose;
      ose << "WARNING: Unknown operator "<<knd;
      Obj::print_error( ose.str().c_str(), cout );
    }
  }
  return knd_str;
}

bool is_eq_kind( int knd )
{
  switch(knd){
  case EQ:
  case LE:
  case LT:
  case GE:
  case GT:
  case DISTINCT:return true;break;
  }
  return false;
}

bool is_smt_kind( int knd )
{
  return knd==EQ || knd==DISTINCT;
}

//equation types ( a ~ b ) that are normalized to (b-a) ~' 0
bool is_opposite( int knd )
{
  return ( knd==LE || knd==LT || knd==DISTINCT );
}
bool is_comparison( int knd )
{
  return ( knd==LE || knd==LT || knd==GE || knd==GT );
}

int get_not( int knd )
{
  switch(knd){
  case EQ: return DISTINCT; break;
  case LE: return GT; break;
  case LT: return GE; break;
  case GE: return LT; break;
  case GT: return LE; break;
  case DISTINCT: return EQ; break;
  }
  return knd;
}

//order in LFSC signature for rules when order does not matter (such as lra_add)
int get_knd_order( int knd )
{
  switch(knd){
  case EQ: return 0; break;
  case GT: return 1; break;
  case GE: return 2; break;
  case DISTINCT: return 3; break;
  }
  return 4;
}

int get_normalized( int knd, bool isnot )
{
  if( isnot ) return get_normalized( get_not( knd ) );
  switch(knd){
  case LE: return GE; break;
  case LT: return GT; break;
  }
  return knd;
}

//should only be called on normalized ops
int get_knd_result( int knd1, int knd2 )
{
  if( knd1==EQ )
    return knd2;
  if( knd2==EQ )
    return knd1;
  if( knd1!=DISTINCT && knd2!=DISTINCT ){
    return ( knd1==GT || knd2==GT ) ? GT : GE;
  }
  ostringstream ose;
  ose << "Unknown get_op_result. " << kind_to_str( knd1 ) << " " << kind_to_str( knd2 ) << std::endl;
  Obj::print_error( ose.str().c_str(), cout );
  return -1;
}

// print helpers
void print_mpq(int num, int den, std::ostream& s )
{
  if( num<0 )
    s << "(~ ";
  s << abs( num ) << "/" << den;
  if( num<0 )
    s << ")";
}

void print_rational( const Rational& r, std::ostream& s )
{
  //print_mpq( r.getNumerator().getInt(), r.getDenominator().getInt(), s );
  if( r<0 )
    s << "(~ " << -r;
  else
    s << r;
  if( r.isInteger() )
    s << "/1";
  if( r<0 )
    s << ")";
}

void print_rational_divide( const Rational& n, const Rational& d, std::ostream& s )
{
  //print_mpq( n.getNumerator().getInt(), d.getNumerator().getInt(), s );
  if( n<0 )
    s << "(~ " << -n << "/" << d << ")";
  else
    s << n << "/" << d;
}

bool getRat( const Expr& e, Rational& r ){
  if( e.isRational() ){
    r = e.getRational();
    return true;
  }else if( e.getKind()==DIVIDE && e[0].isRational() && e[1].isRational() ){
    r = e[0].getRational()/e[1].getRational();
    return true;
  }else if( e.getKind()==UMINUS ){
    getRat( e[0], r );
    r = -r;
    return true;
  }
  return false;
}

bool isFlat( const Expr& e ){
  for( int a=0; a<e.arity(); a++ ){
    if( e.getKind()==e[a].getKind() ){
      if( e.arity()>=10 )
        return false;
      else if( !isFlat( e[a] ) )
        return false;
    }
  }
  return true;
}

void make_flatten_expr_h( const Expr& e, Expr& pe, const Expr& pec, bool pecDef, int knd ){
  //cout << "Trav " << e << std::endl;
  if( e.getKind()==knd ){
    make_flatten_expr_h( e[1], pe, pec, pecDef, knd );
    if( e[0].getKind()==knd ){
      make_flatten_expr_h( e[0], pe, pe, true, knd );
    }else{
      pe = Expr( knd, e[0], pe );
    }
  }else{
    if( pecDef ){
      pe = Expr( knd, e, pec );
    }else{
      pe = e;
    }
  }
}

void make_flatten_expr( const Expr& e, Expr& pe, int knd ){
  Expr pec;
  make_flatten_expr_h( e, pe, pec, false, knd );
}
