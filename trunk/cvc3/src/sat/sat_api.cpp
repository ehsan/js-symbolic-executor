///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// File: sat_api.cpp                                                         //
// Author: Clark Barrett                                                     //
// Created: 2002		                 			     //
// Description: Implementation of SatSolver class                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#include "sat_api.h"

using namespace std;

#ifndef DPLL_BASIC
SatSolver *SatSolver::Create()
{
  return NULL;
}
#endif

void SatSolver::PrintStatistics(ostream & os)
{
  int val;
  float time;

    os << "Number of Variables\t\t\t" << NumVariables() << endl;

  val = GetNumLiterals();
  if (val != -1)
    os << "Number of Literals\t\t\t" << val << endl;

    os << "Number of Clauses\t\t\t" << NumClauses() << endl;

  val = GetBudgetUsed();
  if (val != -1)
    os << "Budget Used\t\t\t\t" << val << endl;

  val = GetMemUsed();
  if (val != -1)
    os << "Memory Used\t\t\t\t" << val << endl;

  val = GetMaxDLevel();
  if (val != -1)
    os << "Maximum Decision Level\t\t\t" << val << endl;

  val = GetNumDecisions();
  if (val != -1)
    os << "Number of Decisions\t\t\t" << val << endl;

  val = GetNumImplications();
  if (val != -1)
    os << "Number of Implications\t\t\t" << val << endl;

  val = GetNumConflicts();
  if (val != -1)
    os << "Number of Conflicts\t\t\t" << val << endl;

  val = GetNumExtConflicts();
  if (val != -1)
    os << "Number of External Conflicts\t\t" << val << endl;

  val = GetNumDeletedClauses();
  if (val != -1)
    os << "Number of Deleted Clauses\t\t" << val << endl;

  val = GetNumDeletedLiterals();
  if (val != -1)
    os << "Number of Deleted Literals\t\t" << val << endl;

  time = GetTotalTime();
  if (time != -1)
    os << endl << "Total Run Time\t\t\t\t" << time << endl;

  time = GetSATTime();
  if (time != -1)
    os << "Time spent in SAT\t\t\t" << time << endl;
}
