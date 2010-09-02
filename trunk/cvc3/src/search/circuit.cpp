/*****************************************************************************/
/*!
 * \file circuit.cpp
 * \brief Circuit class
 * 
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/


#include "circuit.h"
#include "search_fast.h"
#include "search_rules.h"

using namespace std;

namespace CVC3
{

Circuit::Circuit(SearchEngineFast* se, const Theorem& thm)
  : d_thm(thm)
{
  const Expr& e = d_thm.getExpr();
  for (int i = 0; i < e.arity(); i++)
  {
    d_lits[i] =
      e[i].isNot() ?
      Literal(Variable(se->d_vm, e[i][0]), false) :
      Literal(Variable(se->d_vm, e[i]), true);

    se->d_circuitsByExpr[e[i]].push_back(this);
    se->d_circuitsByExpr[e[i].negate()].push_back(this);
  }
}

#define vals3(a, b, c) ((a) + 1 + ((b) + 1) * 3 + ((c) + 1) * 9)
#define vals4(a, b, c, d) (vals3(a, b, c) + ((d) + 1) * 27)

bool Circuit::propagate(SearchEngineFast* se)
{
  int v0 = d_lits[0].getValue();
  int v1 = d_lits[1].getValue();
  int v2 = d_lits[2].getValue();
  int v3 = d_lits[3].getValue();

  const Theorem& t0 = d_lits[0].getTheorem();
  const Theorem& t1 = d_lits[1].getTheorem();
  const Theorem& t2 = d_lits[2].getTheorem();
  const Theorem& t3 = d_lits[3].getTheorem();

  int values = d_thm.getExpr().arity() == 3 ?
    vals3(v0, v1, v2) : vals4(v0, v1, v2, v3);

  Theorem thm;
  Theorem thm2;

  switch (d_thm.getExpr().getKind())
  {
  case AND_R:
    switch (values)
    {
    case vals3(0,0,0): case vals3(0,0,1): case vals3(0,1,0):
    case vals3(1,1,1): case vals3(-1,0,0): case vals3(-1,0,-1):
    case vals3(-1,1,-1): case vals3(-1,-1,0): case vals3(-1,-1,1):
    case vals3(-1,-1,-1):
      break;

    case vals3(0,0,-1): case vals3(0,1,-1): case vals3(0,-1,0):
    case vals3(0,-1,1): case vals3(0,-1,-1):
      // simp
      thm = se->d_rules->propAndrAF(d_thm, v1 == -1, v1 == -1 ? t1 : t2);
      break;

    case vals3(0,1,1):
      // simp
      thm = se->d_rules->propAndrAT(d_thm, t1, t2);
      break;

    case vals3(1,1,0): case vals3(1,0,1): case vals3(1,0,0):
      // split cases to avoid doing extra work?
      se->d_rules->propAndrLRT(d_thm, t0, &thm, &thm2);
      break;

    case vals3(-1,0,1):
      thm = se->d_rules->propAndrLF(d_thm, t0, t2);
      break;

    case vals3(-1,1,0):
      thm = se->d_rules->propAndrRF(d_thm, t0, t1);
      break;

    case vals3(1,0,-1): case vals3(1,1,-1): case vals3(1,-1,0):
    case vals3(1,-1,1): case vals3(1,-1,-1):
      se->d_conflictTheorem =
	se->d_rules->confAndrAT(d_thm, t0, v1 == -1, v1 == -1 ? t1 : t2);
      return false;

    case vals3(-1,1,1):
      se->d_conflictTheorem =
	se->d_rules->confAndrAF(d_thm, t0, t1, t2);
      return false;
    }
    break;

  case IFF_R:
    switch (values)
    {
    case vals3(0,0,0): case vals3(0,0,1): case vals3(0,0,-1):
    case vals3(0,1,0): case vals3(0,-1,0): case vals3(1,0,0):
    case vals3(1,1,1): case vals3(1,-1,-1): case vals3(-1,0,0):
    case vals3(-1,1,-1): case vals3(-1,-1,1):
      break;

    case vals3(0,1,1): case vals3(0,-1,-1):
    case vals3(0,1,-1): case vals3(0,-1,1):
      // simp
      thm = se->d_rules->propIffr(d_thm, 0, t1, t2);
      break;

    case vals3(1,0,1): case vals3(-1,0,-1):
    case vals3(1,0,-1): case vals3(-1,0,1):
      thm = se->d_rules->propIffr(d_thm, 1, t0, t2);
      break;

    case vals3(1,1,0): case vals3(-1,-1,0):
    case vals3(1,-1,0): case vals3(-1,1,0):
      thm = se->d_rules->propIffr(d_thm, 2, t0, t1);
      break;

    case vals3(1,1,-1): case vals3(1,-1,1):
    case vals3(-1,1,1): case vals3(-1,-1,-1):
      se->d_conflictTheorem = se->d_rules->confIffr(d_thm, t0, t1, t2);
      return false;
    }
    break;

  case ITE_R:
    switch (values)
    {
    case vals4(0,0,0,0): case vals4(0,0,0,1): case vals4(0,0,0,-1):
    case vals4(0,0,1,0): case vals4(0,0,1,1): case vals4(0,0,1,-1):
    case vals4(0,0,-1,0): case vals4(0,0,-1,1): case vals4(0,0,-1,-1):
    case vals4(0,1,0,0): case vals4(0,1,0,1): case vals4(0,1,0,-1):
    case vals4(0,-1,0,0): case vals4(0,-1,1,0): case vals4(0,-1,-1,0):
    case vals4(1,0,0,0): case vals4(1,0,0,1): case vals4(1,0,1,0):
    case vals4(1,0,1,1): case vals4(1,1,1,0): case vals4(1,1,1,1):
    case vals4(1,1,1,-1): case vals4(1,-1,0,1): case vals4(1,-1,1,1):
    case vals4(1,-1,-1,1): case vals4(-1,0,0,0): case vals4(-1,0,0,-1):
    case vals4(-1,0,-1,0): case vals4(-1,0,-1,-1): case vals4(-1,1,-1,0):
    case vals4(-1,1,-1,1): case vals4(-1,1,-1,-1): case vals4(-1,-1,0,-1):
    case vals4(-1,-1,1,-1): case vals4(-1,-1,-1,-1):
      break;

    case vals4(0,1,1,0): case vals4(0,1,1,1): case vals4(0,1,1,-1):
    case vals4(0,1,-1,0): case vals4(0,1,-1,1): case vals4(0,1,-1,-1):
    case vals4(0,-1,0,-1): case vals4(0,-1,1,-1): case vals4(0,-1,-1,-1):
    case vals4(0,-1,0,1): case vals4(0,-1,1,1): case vals4(0,-1,-1,1):
      // simp
      thm = se->d_rules->propIterIte(d_thm, v1 == 1, t1, v1 == 1 ? t2 : t3);
      break;

    case vals4(1,0,0,-1): case vals4(1,0,1,-1): case vals4(1,0,-1,0):
    case vals4(1,0,-1,1): case vals4(-1,0,0,1): case vals4(-1,0,1,0):
    case vals4(-1,0,1,-1): case vals4(-1,0,-1,1):
      se->d_rules->propIterIfThen(d_thm, v0 == -v2, t0, v0 == -v2 ? t2 : t3,
				  &thm, &thm2);
      break;

    case vals4(1,1,0,0): case vals4(1,1,0,1): case vals4(1,1,0,-1):
    case vals4(1,-1,0,0): case vals4(1,-1,1,0): case vals4(1,-1,-1,0):
    case vals4(-1,1,0,0): case vals4(-1,1,0,1): case vals4(-1,1,0,-1):
    case vals4(-1,-1,0,0): case vals4(-1,-1,1,0): case vals4(-1,-1,-1,0):
      thm = se->d_rules->propIterThen(d_thm, t0, t1);
      break;

    case vals4(1,0,-1,-1): case vals4(-1,0,1,1):
    case vals4(-1,1,1,1): case vals4(1,1,-1,-1):
      se->d_conflictTheorem =
	se->d_rules->confIterThenElse(d_thm, t0, t2, t3);
      return false;

    case vals4(1,1,-1,0): case vals4(1,1,-1,1): case vals4(1,-1,0,-1):
    case vals4(1,-1,1,-1): case vals4(1,-1,-1,-1): case vals4(-1,1,1,0):
    case vals4(-1,1,1,-1): case vals4(-1,-1,0,1): case vals4(-1,-1,1,1):
    case vals4(-1,-1,-1,1):
      se->d_conflictTheorem =
	se->d_rules->confIterIfThen(d_thm, v1 == 1, t0, t1, v1 == 1 ? t2 : t3);
      return false;
    }
    break;

  default:
    DebugAssert(false, "unhandled circuit");
  }

  if (!thm.isNull() && se->newLiteral(thm.getExpr()).getValue() == 0)
  {
    se->d_core->addFact(thm);
    se->recordFact(thm);
    se->d_literals.push_back(se->newLiteral(thm.getExpr()));
    se->d_circuitPropCount++;
  }

  if (!thm2.isNull() && se->newLiteral(thm2.getExpr()).getValue() == 0)
  {
    se->d_core->addFact(thm2);
    se->recordFact(thm2);
    se->d_literals.push_back(se->newLiteral(thm2.getExpr()));
    se->d_circuitPropCount++;
  }

  return true;
}


} // namespace CVC3

