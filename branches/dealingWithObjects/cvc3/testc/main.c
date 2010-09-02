///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// File: main.cpp                                                            //
// Author: Clark Barrett                                                     //
// Created: Sat Apr 19 01:47:47 2003                                         //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


#include "c_interface.h"
#include <stdio.h>
#include <stdlib.h>


#define TRUE 1
#define FALSE 0


#define FatalAssert(b,msg) \
if (!(b)) { \
  fprintf(stderr, "Assertion Failure: %s\n", msg); \
  exit(1); }


// Check whether e is valid

void check_error(char* msg) {
  if(vc_get_error_status() < 0) {
    fprintf(stderr, "%s\n", msg);
    fprintf(stderr, "%s\n", vc_get_error_string());
    exit(1);
  }
}

int check(VC vc, Expr e)
{
  int res;
  printf("Query: ");
  vc_printExpr(vc, e);
  check_error("Error occured during query");
  res = vc_query(vc, e);
  switch (res) {
    case 0:
      printf("Invalid\n\n");
      break;
    case 1:
      printf("Valid\n\n");
      break;
  }
  return res;
}


// Make a new assertion
void newAssertion(VC vc, Expr e)
{
  // Testing printing to file descriptor.  Turns out, we need to flush
  // the file in C before printing through C++ (they apparently use
  // different buffers, and text may come out of order).
  printf("Assert: "); fflush(stdout);
  vc_printExprFile(vc, e, 1);
  vc_assertFormula(vc, e);
  check_error("Error occured during assertion");
}


void test1()
{
  Flags flags = vc_createFlags();
  VC vc;
  Type b;
  Expr p, np, e;
  Type r, real2real;
  Expr x, y, fx, fy, xeqy, fxeqfy, w, z, weqx, yeqz, one, two, xeqone, xeqtwo,
    simp, simp2;
  Op f;
  Expr* assertions;
  int i, size, res;

  vc_setStringFlag(flags, "dump-log", ".testc1.cvc");
  vc_setStrSeqFlag(flags, "trace", "pushpop", 1);

  vc = vc_createValidityChecker(flags);

  // Check p OR ~p

  b = vc_boolType(vc);
  p = vc_varExpr(vc, "p", vc_boolType(vc));
  np = vc_notExpr(vc, p);
  e = vc_orExpr(vc, p, np);

  res = check(vc, e);
  FatalAssert(res == 1, "Expected Valid");

  vc_deleteType(b);
  vc_deleteExpr(p);
  vc_deleteExpr(np);
  vc_deleteExpr(e);

  /* Check x = y -> f(x) = f(y) */

  r = vc_realType(vc);

  x = vc_varExpr(vc, "x", r);
  y = vc_varExpr(vc, "y", r);

  real2real = vc_funType1(vc, r, r);
  f = vc_createOp(vc, "f", real2real);

  fx = vc_funExpr1(vc, f, x);
  fy = vc_funExpr1(vc, f, y);
  
  xeqy = vc_eqExpr(vc, x, y);
  fxeqfy = vc_eqExpr(vc, fx, fy);

  e = vc_impliesExpr(vc, xeqy, fxeqfy);
  res = check(vc, e);
  FatalAssert(res == 1, "Expected Valid");

  vc_deleteType(real2real);
  vc_deleteExpr(e);

  // Check f(x) = f(y) -> x = y

  e = vc_impliesExpr(vc, fxeqfy, xeqy);
  vc_push(vc);
  res = check(vc, e);
  FatalAssert(res == 0, "Expected Invalid");
  vc_deleteExpr(e);

  // Get counter-example

  printf("Stack level: %d\n", vc_stackLevel(vc));
  printf("Counter-example:\n");
  assertions = vc_getCounterExample(vc, &size);
  
  for (i = 0; i < size; ++i) {
    vc_printExpr(vc, assertions[i]);
  }
  vc_deleteVector(assertions);
  printf("End of counter-example\n\n");

  printf("Concrete model:\n");
  assertions = vc_getConcreteModel(vc, &size);
  
  for (i = 0; i < size; ++i) {
    vc_printExpr(vc, assertions[i]);
  }
  vc_deleteVector(assertions);
  printf("End of concrete model\n\n");

  // Reset to initial scope
  printf("Resetting\n");
  vc_pop(vc);
  printf("Stack level: %d\n\n", vc_stackLevel(vc));

  // Check w = x & x = y & y = z & f(x) = f(y) & x = 1 & z = 2

  w = vc_varExpr(vc, "w", r);
  z = vc_varExpr(vc, "z", r);

  printf("Push Scope\n\n");
  vc_push(vc);

  weqx = vc_eqExpr(vc, w, x);
  yeqz = vc_eqExpr(vc, y, z);
  
  one = vc_ratExpr(vc, 1, 1);
  two = vc_ratExpr(vc, 2, 1);
  xeqone = vc_eqExpr(vc, x, one);
  xeqtwo = vc_eqExpr(vc, x, two);

  newAssertion(vc, weqx);
  newAssertion(vc, xeqy);
  newAssertion(vc, yeqz);
  newAssertion(vc, fxeqfy);
  newAssertion(vc, xeqone);
  newAssertion(vc, xeqtwo);

  printf("\nsimplify(w) = ");

  simp = vc_simplify(vc, w);

  char* str = vc_printExprString(vc, simp);
  printf("%s\n", str);
  vc_deleteString(str);

  printf("Inconsistent?: %d\n", vc_inconsistent(vc, &assertions, &size));
  check_error("Error occured during inconsistency check");

  printf("Assumptions Used:\n");
  for (i = 0; i < size; ++i) {
    vc_printExpr(vc, assertions[i]);
  }
  vc_deleteVector(assertions);

  printf("\nPop Scope\n\n");
  vc_pop(vc);

  printf("simplify(w) = ");

  simp2 = vc_simplify(vc, w);
  vc_printExpr(vc, simp2);
  printf("\n");

  printf("Inconsistent?: %d\n", vc_inconsistent(vc, &assertions, &size));
  vc_deleteVector(assertions);

  vc_deleteType(r);
  vc_deleteExpr(x);
  vc_deleteExpr(y);
  vc_deleteOp(f);
  vc_deleteExpr(fx);
  vc_deleteExpr(fy);
  vc_deleteExpr(xeqy);
  vc_deleteExpr(fxeqfy);
  vc_deleteExpr(w);
  vc_deleteExpr(z);
  vc_deleteExpr(weqx);
  vc_deleteExpr(yeqz);
  vc_deleteExpr(one);
  vc_deleteExpr(two);
  vc_deleteExpr(xeqone);
  vc_deleteExpr(xeqtwo);
  vc_deleteExpr(simp);
  vc_deleteExpr(simp2);

  vc_destroyValidityChecker(vc);
  vc_deleteFlags(flags);
}


void test2()
{
  VC vc = vc_createValidityChecker(NULL);

  // Check x = y -> g(x,y) = g(y,x)

  Type r = vc_realType(vc);

  Expr x = vc_varExpr(vc, "x", r);
  Expr y = vc_varExpr(vc, "y", r);

  Type realxreal2real = vc_funType2(vc, r, r, r);
  Op g = vc_createOp(vc, "g", realxreal2real);

  Expr gxy = vc_funExpr2(vc, g, x, y);
  Expr gyx = vc_funExpr2(vc, g, y, x);

  Expr xeqy = vc_eqExpr(vc, x, y);
  Expr gxyeqgyx = vc_eqExpr(vc, gxy, gyx);

  Expr e = vc_impliesExpr(vc, xeqy, gxyeqgyx);
  Type v[2];
  Op h;
  Expr hxy, hyx, hxyeqhyx;
  int res;

  res = check(vc, e);
  FatalAssert(res == 1, "Expected Valid");

  vc_deleteType(realxreal2real);
  vc_deleteOp(g);
  vc_deleteExpr(gxy);
  vc_deleteExpr(gyx);
  vc_deleteExpr(gxyeqgyx);
  vc_deleteExpr(e);

  v[0] = r;
  v[1] = r;

  realxreal2real = vc_funTypeN(vc, v, r, 2);
  h = vc_createOp(vc, "h", realxreal2real);

  hxy = vc_funExpr2(vc, h, x, y);
  hyx = vc_funExpr2(vc, h, y, x);
  hxyeqhyx = vc_eqExpr(vc, hxy, hyx);

  e = vc_impliesExpr(vc, xeqy, hxyeqhyx);
  res = check(vc, e);
  FatalAssert(res == 1, "Expected Valid");

  vc_deleteType(r);
  vc_deleteExpr(x);
  vc_deleteExpr(y);
  vc_deleteType(realxreal2real);
  vc_deleteExpr(hxy);
  vc_deleteExpr(hxyeqhyx);
  vc_deleteExpr(e);

  vc_destroyValidityChecker(vc);
}


/* void test3() */
/* { */
/*   VC vc = vc_createValidityChecker(NULL); */
/*   // Check x = y -> g(x,y) = g(y,x) */

/*   Type r = vc_realType(vc); */
/*   Expr x = vc_varExpr(vc, "x", r); */
/*   Expr y = vc_varExpr(vc, "y", r); */

/*   Type realxreal2real = vc_funType2(vc, r, r, r); */
/*   Op g = vc_createOp(vc, "g", realxreal2real); */

/*   Expr gxy = vc_parseExpr(vc, "g(x,y)"); */
/*   Expr gxy2; */

/*   vc_printExpr(vc, gxy); */

/*   gxy2 = vc_funExpr2(vc, g, x, y); */
/*   vc_printExpr(vc, gxy2); */
/*   FatalAssert((gxy == gxy2), "Should be equal"); */

/*   vc_deleteType(r); */
/*   vc_deleteExpr(x); */
/*   vc_deleteExpr(y); */
/*   vc_deleteType(realxreal2real); */
/*   vc_deleteOp(g); */
/*   vc_deleteExpr(gxy); */
/*   vc_deleteExpr(gxy2); */

/*   vc_destroyValidityChecker(vc); */
/* } */

void test4(int regressLevel)
{
  VC vc = vc_createValidityChecker(NULL);

  // Check x >= 10 /\ x >= 40 /\ y <= 0 -->
  //       x >= 1 /\ y < 10

  Type r = vc_realType(vc);
  Expr x = vc_varExpr(vc, "x", r);
  Expr y = vc_varExpr(vc, "y", r);

  Expr ten = vc_ratExpr(vc, 10, 1);
  Expr ge = vc_geExpr(vc, x, ten);

  Expr forty = vc_ratExpr(vc, 40, 1);
  Expr ge2 = vc_geExpr(vc, x, forty);

  Expr zero = vc_ratExpr(vc, 0, 1);
  Expr ge3 = vc_leExpr(vc, y, zero);

  Expr children[3];
  Expr hyp, one, conc, query;
  int i;

  children[0] = ge;
  children[1] = ge2;
  children[2] = ge3;

  hyp = vc_andExprN(vc, children, 3);

  vc_deleteType(r);
  vc_deleteExpr(ge);
  vc_deleteExpr(forty);
  vc_deleteExpr(ge2);
  vc_deleteExpr(zero);
  vc_deleteExpr(ge3);

  one = vc_ratExpr(vc, 1, 1);
  ge = vc_geExpr(vc, x, one);

  ge2 = vc_ltExpr(vc, y, ten);

  conc = vc_andExpr(vc, ge, ge2);
  query = vc_impliesExpr(vc, hyp, conc);

  vc_deleteExpr(x);
  vc_deleteExpr(y);
  vc_deleteExpr(ten);
  vc_deleteExpr(hyp);
  vc_deleteExpr(one);
  vc_deleteExpr(ge);
  vc_deleteExpr(ge2);
  vc_deleteExpr(conc);

  for (i = 0; i < 100*regressLevel; i++)
    vc_query(vc, query);

  vc_deleteExpr(query);

  vc_destroyValidityChecker(vc);
}


void test5()
{
  Flags flags = vc_createFlags();
  VC vc;
  Type r;
  Expr x, xEQx, p;

  //  vc_setBoolFlag(flags, "proofs", TRUE);
  vc = vc_createValidityChecker(flags);

  r = vc_realType(vc);
  x = vc_varExpr(vc, "x", r);
  xEQx = vc_eqExpr(vc, x, x);

  vc_query(vc, xEQx);

  //  p = vc_getProof(vc);

  //  vc_printExpr(vc, p);

  vc_deleteType(r);
  vc_deleteExpr(x);
  vc_deleteExpr(xEQx);
  //  vc_deleteExpr(p);

  vc_destroyValidityChecker(vc);
  vc_deleteFlags(flags);
}


void test6()
{
  Flags flags = vc_createFlags();
  VC vc;
  Expr p, p3, p32;
  char *x;

  //  vc_setBoolFlag(flags, "proofs", 1);
  vc_setBoolFlag(flags, "dagify-exprs", 0);
  vc = vc_createValidityChecker(flags);

  //  p = vc_getProofOfFile(vc,"benchmarks/add1.cvc");
  check_error("Failed to check file");

  //  vc_deleteExpr(p);
  vc_destroyValidityChecker(vc);
  vc_deleteFlags(flags);

/*   p3 = getChild(p,3); */
/*   p32 = getChild(p3,2); */

/*   if (isLambda(p32)) */
/*     printf("The expression is Lambda\n"); */
/*   else */
/*     printf("The expression is not Lambda\n"); */

/*   x = exprString(p32); */

  /*  printf("Test expr,%s",x);*/

}


int printImpliedLiterals(VC vc)
{
  int count = 0;
  Expr impLit = vc_getImpliedLiteral(vc);
  printf("Implied Literals:\n");
  while (impLit) {
    ++count;
    vc_printExpr(vc, impLit);
    vc_deleteExpr(impLit);
    impLit = vc_getImpliedLiteral(vc);
  }
  return count;
}


void test7()
{
  VC vc = vc_createValidityChecker(NULL);

  Type r = vc_realType(vc);
  Type b = vc_boolType(vc);

  Expr x = vc_varExpr(vc, "x", r);
  Expr y = vc_varExpr(vc, "y", r);
  Expr z = vc_varExpr(vc, "z", r);

  Type real2real = vc_funType1(vc, r, r);
  Type real2bool = vc_funType1(vc, r, b);

  Op f = vc_createOp(vc, "f", real2real);
  Op p = vc_createOp(vc, "p", real2bool);

  Expr fx = vc_funExpr1(vc, f, x);
  Expr fy = vc_funExpr1(vc, f, y);
  Expr fxeqfy = vc_eqExpr(vc, fx, fy);

  Expr px = vc_funExpr1(vc, p, x);
  Expr py = vc_funExpr1(vc, p, y);

  Expr xeqy = vc_eqExpr(vc, x, y);
  Expr yeqx = vc_eqExpr(vc, y, x);
  Expr xeqz = vc_eqExpr(vc, x, z);
  Expr zeqx = vc_eqExpr(vc, z, x);
  Expr yeqz = vc_eqExpr(vc, y, z);
  Expr zeqy = vc_eqExpr(vc, z, y);

  Expr notxeqz = vc_notExpr(vc, xeqz);

  int c;

  vc_registerAtom(vc, xeqy);
  vc_registerAtom(vc, yeqx);
  vc_registerAtom(vc, xeqz);
  vc_registerAtom(vc, zeqx);
  vc_registerAtom(vc, yeqz);
  vc_registerAtom(vc, zeqy);
  vc_registerAtom(vc, px);
  vc_registerAtom(vc, py);
  vc_registerAtom(vc, fxeqfy);

  printf("Push\n");
  vc_push(vc);

  printf("Assert x = y\n");
  vc_assertFormula(vc, xeqy);
  c = printImpliedLiterals(vc);
  FatalAssert(c==3,"Implied literal error 0");

  printf("Push\n");
  vc_push(vc);
  printf("Assert x /= z\n");
  vc_assertFormula(vc, notxeqz);
  c = printImpliedLiterals(vc);
  FatalAssert(c==4,"Implied literal error 1");
  printf("Pop\n");
  vc_pop(vc);
  printf("Pop\n");
  vc_pop(vc);

  vc_deleteExpr(notxeqz);
  vc_deleteExpr(zeqy);
  vc_deleteExpr(yeqz);
  vc_deleteExpr(zeqx);
  vc_deleteExpr(xeqz);
  vc_deleteExpr(yeqx);
  vc_deleteExpr(xeqy);
  vc_deleteExpr(py);
  vc_deleteExpr(px);
  vc_deleteExpr(fxeqfy);
  vc_deleteExpr(fy);
  vc_deleteExpr(fx);
  vc_deleteOp(p);
  vc_deleteOp(f);
  vc_deleteType(real2bool);
  vc_deleteType(real2real);
  vc_deleteExpr(z);
  vc_deleteExpr(y);
  vc_deleteExpr(x);
  vc_deleteType(b);
  vc_deleteType(r);

  vc_destroyValidityChecker(vc);
}


void test8 (void)
{
  Flags flags = vc_createFlags();
/*   vc_setStrSeqFlag(flags, "trace", "pushpop", 1); */
/*   vc_setStrSeqFlag(flags, "trace", "assertLit", 1); */
/*   vc_setStrSeqFlag(flags, "trace", "assertFactCore", 1); */
/*   vc_setStrSeqFlag(flags, "trace", "assertFormula", 1); */

  VC vc = vc_createValidityChecker (flags);
  Type bv32 = vc_bvType (vc, 32);
  Expr zero = vc_bvConstExprFromInt (vc, 32, 0);
  Expr one = vc_bvConstExprFromInt (vc, 32, 1);
  Expr a = vc_varExpr (vc, "a", bv32);
  Expr three = vc_bvConstExprFromInt (vc, 32, 3);
  Expr prod = vc_bvMultExpr (vc, 32, a, three);
  {
    Expr a64 = vc_bvSignExtend (vc, a, 64);
    Expr three64 = vc_bvSignExtend (vc, three, 64);
    Expr prod64 = vc_bvMultExpr (vc, 64, a64, three64);
    Expr max = vc_bvConstExprFromInt (vc, 32, 2147483647);
    Expr min = vc_bvConstExprFromInt (vc, 32, (-2147483647 - 1));
    Expr prod64_sge_min = vc_bvSGeExpr (vc, prod64, min);
    Expr prod64_sle_max = vc_bvSLeExpr (vc, prod64, max);
    Expr prod64_sge_min_and_sle_max =
      vc_andExpr (vc, prod64_sge_min, prod64_sle_max);
    vc_assertFormula (vc, prod64_sge_min_and_sle_max);
  }
  Expr D4 = vc_varExpr (vc, "D4", bv32);
  {
    Expr cond = vc_bvSLtExpr (vc, a, prod);
    Expr test = vc_iteExpr (vc, cond, one, zero);
    Expr D4_eq_test = vc_eqExpr (vc, D4, test);
    vc_assertFormula (vc, D4_eq_test);
  }
  Expr D6 = vc_varExpr (vc, "D6", bv32);
  {
    Expr cond = vc_bvSLeExpr (vc, a, prod);
    Expr test = vc_iteExpr (vc, cond, one, zero);
    Expr D6_eq_test = vc_eqExpr (vc, D6, test);
    vc_assertFormula (vc, D6_eq_test);
  }
  vc_push (vc);
  vc_pop (vc);
  vc_push (vc);
  {
    Expr cond = vc_bvSLtExpr (vc, a, zero);
    Expr test = vc_iteExpr (vc, cond, one, zero);
    Expr test_eq_one = vc_eqExpr (vc, test, one);
    vc_assertFormula (vc, test_eq_one);
    vc_push (vc);
    {
      Expr D4_eq_one = vc_eqExpr (vc, D4, one);
      vc_query (vc, D4_eq_one);
    }
    vc_pop (vc);
    vc_push (vc);
    vc_pop (vc);
    vc_push (vc);
    vc_pop (vc);
  }
  vc_pop (vc);
  {
    Expr cond = vc_eqExpr (vc, a, zero);
    Expr test = vc_iteExpr (vc, cond, one, zero);
    Expr test_eq_one = vc_eqExpr (vc, test, one);
    vc_assertFormula (vc, test_eq_one);
    vc_push (vc);
    vc_pop (vc);
    {
      Expr zero_eq_one = vc_eqExpr (vc, zero, one);
      vc_query (vc, zero_eq_one);
    }
  }
  vc_destroyValidityChecker(vc);
}


void test9 (void)
{
  VC vc = vc_createValidityChecker (((void *) 0));
  Type bv32 = vc_bvType (vc, 32);
  Expr zero = vc_bvConstExprFromInt (vc, 32, 0);
  Expr one = vc_bvConstExprFromInt (vc, 32, 1);
  Expr a = vc_varExpr (vc, "a", bv32);
  Expr three = vc_bvConstExprFromInt (vc, 32, 3);
  Expr three64 = vc_bvSignExtend (vc, three, 64);
  Expr a64 = vc_bvSignExtend (vc, a, 64);
  Expr prod64 = vc_bvMultExpr (vc, 64, a64, three64);
  Expr min = vc_bvConstExprFromInt (vc, 32, (-2147483647 - 1));
  Expr max = vc_bvConstExprFromInt (vc, 32, 2147483647);
  Expr prod64_sge_min = vc_bvSGeExpr (vc, prod64, min);
  Expr prod64_sle_max = vc_bvSLeExpr (vc, prod64, max);
  Expr prod64_sge_min_and_sle_max =
    vc_andExpr (vc, prod64_sge_min, prod64_sle_max);
  vc_assertFormula (vc, prod64_sge_min_and_sle_max);
  Expr D3 = vc_varExpr (vc, "D3", bv32);
  Expr prod = vc_bvMultExpr (vc, 32, a, three);
  Expr D3_eq_prod = vc_eqExpr (vc, D3, prod);
  vc_assertFormula (vc, D3_eq_prod);
  Expr D4 = vc_varExpr (vc, "D4", bv32);
  Expr D3_sle_a_cond = vc_bvSLeExpr (vc, D3, a);
  Expr D3_sle_a_expr = vc_iteExpr (vc, D3_sle_a_cond, one, zero);
  Expr D4_eq_D3_sle_a_expr = vc_eqExpr (vc, D4, D3_sle_a_expr);
  vc_assertFormula (vc, D4_eq_D3_sle_a_expr);
  Expr D6 = vc_varExpr (vc, "D6", bv32);
  Expr D3_slt_a_cond = vc_bvSLtExpr (vc, D3, a);
  Expr D3_slt_a_expr = vc_iteExpr (vc, D3_slt_a_cond, one, zero);
  Expr D6_eq_D3_slt_a_expr = vc_eqExpr (vc, D6, D3_slt_a_expr);
  vc_assertFormula (vc, D6_eq_D3_slt_a_expr);
  Expr zero_lt_a = vc_bvSLtExpr (vc, zero, a);
  vc_assertFormula (vc, zero_lt_a);
  Expr D4_eq_one = vc_eqExpr (vc, D4, one);
  Expr not_D4_eq_one = vc_notExpr (vc, D4_eq_one);
  vc_query (vc, not_D4_eq_one);
  Expr D6_eq_one = vc_eqExpr (vc, D6, one);
  Expr not_D6_eq_one = vc_notExpr (vc, D6_eq_one);
  vc_query (vc, not_D6_eq_one);
  vc_destroyValidityChecker(vc);
}


void test10()
{
  Flags flags = vc_createFlags();
  VC vc = vc_createValidityChecker(flags);
  Type a = vc_createType(vc, "a");
  Type aa = vc_funType1(vc, a, a);
  Op f1 = vc_createOp(vc, "f", aa);
  Type aa2;
  Op f2 = vc_lookupOp(vc, "f", &aa2);
  FatalAssert(f2 != NULL, "Expected f2 not NULL");
  FatalAssert(f1 == f2, "Expected equal");
  Expr x = vc_varExpr(vc, "x", a);
  Expr f1x = vc_funExpr1(vc, f1, x);
  Expr f2x = vc_funExpr1(vc, f2, x);
  Expr eq = vc_eqExpr(vc, f1x, f2x);
  int res = vc_query(vc, eq);
  printf("eq: %d\n", res);
  vc_destroyValidityChecker(vc);
}


int main(int argc, char** argv)
{
  int regressLevel = 2;
  if (argc > 1) regressLevel = atoi(argv[1]);
  printf("Running C API test, regress level = %d\n", regressLevel);
  printf("\ntest1() {\n");
  test1();
  check_error("test1");
  printf("\n}\ntest2() {\n");
  test2();
  check_error("test2");
/* TODO: implement parseExpr */
/*   test3(); */
/*   check_error("test3"); */

  printf("\n}\ntest4() {\n");
  test4(regressLevel);
  check_error("test4");
  printf("\n}\ntest5() {\n");
  test5();
  check_error("test5");
  if (regressLevel > 0) {
    printf("\n}\ntest6() {\n");
    test6();
    check_error("test6");
  }
  printf("\n}\ntest7() {\n");
  test7();
  check_error("test7");
  if (regressLevel > 0) {
    printf("\n}\ntest8() {\n");
    test8();
    check_error("test8");
    printf("\n}\ntest9() {\n");
    test9();
    check_error("test9");
  }
  printf("\n}");
  printf("\ntest10() {\n");
  test10();
  return 0;
}
