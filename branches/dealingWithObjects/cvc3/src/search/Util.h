#ifndef UTIL_H_
#define UTIL_H_

#include "Object.h"

// helper utility functions
void ajr_debug_print( const Expr& pf );
string kind_to_str(int knd );
bool is_eq_kind( int knd );
bool is_smt_kind( int knd );

//equation types ( a ~ b ) that are normalized to (b-a) ~' 0
bool is_opposite( int knd );
bool is_comparison( int knd );
int get_not( int knd );

//order in LFSC signature for rules when order does not matter (such as lra_add)
int get_knd_order( int knd );
int get_normalized( int knd, bool isnot = false );

//should only be called on normalized ops
int get_knd_result( int knd1, int knd2 );

//print helpers
void print_mpq(int num, int den, std::ostream& s );
void print_rational( const Rational& r, std::ostream& s );
void print_rational_divide( const Rational& n, const Rational& d, std::ostream& s );

bool getRat( const Expr& e, Rational& r );
bool isFlat( const Expr& e );
void make_flatten_expr( const Expr& e, Expr& pe, int knd );

#endif
