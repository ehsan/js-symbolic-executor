/*****************************************************************************/
/*!
 * \file theorem_producer.cpp
 * \brief See theorem_producer.h file for more information.
 * 
 * Author: Sergey Berezin
 * 
 * Created: Thu Feb 20 16:22:31 2003
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


#define _CVC3_TRUSTED_
#include "theorem_producer.h"
#include "sound_exception.h"
#include "command_line_flags.h"


using namespace std;
using namespace CVC3;


void TheoremProducer::soundError(const std::string& file, int line,
                                 const std::string& cond,
                                 const std::string& msg)
{
  ostringstream ss;
  ss << "in " << file << ":" << line << " (" << cond << ")\n" << msg;
  throw SoundException(ss.str());
}
  

// Constructor
TheoremProducer::TheoremProducer(TheoremManager *tm)
  : d_tm(tm), d_em(tm->getEM()),
    d_checkProofs(&(tm->getFlags()["check-proofs"].getBool())),
    // Proof rule application: will have kids
    d_pfOp(PF_APPLY)
{ d_hole = d_em->newLeafExpr(PF_HOLE); }


Proof TheoremProducer::newLabel(const Expr& e)
{
  // Counter to generate unique proof labels ('u')
  static int s_counter = 0;
  static string s_prefix = "assump";
  ostringstream ss;
  ss << s_counter++;

  if ((d_tm->getFlags()["lfsc-mode"]).getInt()!= 0 ) {
    return newPf("assumptions", e);
  }
  else {
    //TODO: Get rid of hack storing expr in Type field
    // the following lines are commented by Yeting, for neat proofs
    Expr var = d_tm->getEM()->newBoundVarExpr(s_prefix, ss.str(), Type(e, true));
    return Proof(var);  //by Yeting. 
  }  
  
  return newPf("assumptions", e);
  //return newPf("assumptions", var , e);
}


Proof TheoremProducer::newPf(const string& name)
{ return Proof(Expr(d_pfOp, d_em->newVarExpr(name))); }


Proof TheoremProducer::newPf(const string& name, const Expr& e)
{ return Proof(Expr(d_pfOp, d_em->newVarExpr(name), e)); }


Proof TheoremProducer::newPf(const string& name, const Proof& pf)
{ return Proof(Expr(d_pfOp, d_em->newVarExpr(name), pf.getExpr())); }

		
Proof TheoremProducer::newPf(const string& name,
			     const Expr& e1, const Expr& e2)
{ return Proof(Expr(d_pfOp, d_em->newVarExpr(name), e1, e2)); }


Proof TheoremProducer::newPf(const string& name, const Expr& e,
			     const Proof& pf)
{ return Proof(Expr(d_pfOp, d_em->newVarExpr(name), e, pf.getExpr())); }


Proof TheoremProducer::newPf(const string& name, const Expr& e1,
			     const Expr& e2, const Expr& e3) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e1);
  kids.push_back(e2);
  kids.push_back(e3);
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name, const Expr& e1,
			     const Expr& e2, const Proof& pf) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e1);
  kids.push_back(e2);
  kids.push_back(pf.getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     Expr::iterator begin,
			     const Expr::iterator &end) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.insert(kids.end(), begin, end);
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name, const Expr& e,
			     Expr::iterator begin, const Expr::iterator &end) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e);
  kids.insert(kids.end(), begin, end);
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     Expr::iterator begin, const Expr::iterator &end,
			     const vector<Proof>& pfs) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.insert(kids.end(), begin, end);
  for(vector<Proof>::const_iterator i=pfs.begin(), iend=pfs.end();
      i != iend; ++i)
    kids.push_back(i->getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const vector<Expr>& args) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.insert(kids.end(), args.begin(), args.end());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const Expr& e,
			     const vector<Expr>& args) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e);
  kids.insert(kids.end(), args.begin(), args.end());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const Expr& e,
			     const vector<Proof>& pfs) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e);
  for(vector<Proof>::const_iterator i=pfs.begin(), iend=pfs.end();
      i != iend; ++i)
    kids.push_back(i->getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const Expr& e1, const Expr& e2,
			     const vector<Proof>& pfs) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.push_back(e1);
  kids.push_back(e2);
  for(vector<Proof>::const_iterator i=pfs.begin(), iend=pfs.end();
      i != iend; ++i)
    kids.push_back(i->getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const vector<Proof>& pfs) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  for(vector<Proof>::const_iterator i=pfs.begin(), iend=pfs.end();
      i != iend; ++i)
    kids.push_back(i->getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const vector<Expr>& args,
			     const Proof& pf) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.insert(kids.end(), args.begin(), args.end());
  kids.push_back(pf.getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const string& name,
			     const vector<Expr>& args,
			     const vector<Proof>& pfs) {
  vector<Expr> kids;
  kids.push_back(d_em->newVarExpr(name));
  kids.insert(kids.end(), args.begin(), args.end());
  for(vector<Proof>::const_iterator i=pfs.begin(), iend=pfs.end();
      i != iend; ++i)
    kids.push_back(i->getExpr());
  return Proof(Expr(d_pfOp, kids));
}


Proof TheoremProducer::newPf(const Proof& label, const Expr& frm,
			     const Proof& pf) {
  Expr v(label.getExpr());
  IF_DEBUG(Type tp(frm, true);)
  DebugAssert(v.isVar() && v.getType() == tp,
	      "TheoremProducer::newPf: bad variable in LAMBDA expression: "
	      +v.toString());
  vector<Expr> u;
  u.push_back(v);
  return Proof(d_tm->getEM()->newClosureExpr(LAMBDA, u, pf.getExpr()));
}


Proof TheoremProducer::newPf(const Proof& label, const Proof& pf) {
  Expr v(label.getExpr());
  DebugAssert(v.isVar(),
	      "TheoremProducer::newPf: bad variable in LAMBDA expression: "
	      +v.toString());
  vector<Expr> u;
  u.push_back(v);
  return Proof(d_tm->getEM()->newClosureExpr(LAMBDA, u, pf.getExpr()));
}


Proof TheoremProducer::newPf(const std::vector<Proof>& labels,
			     const std::vector<Expr>& frms,
			     const Proof& pf) {
  std::vector<Expr> u;
  for(unsigned i=0; i<labels.size(); i++) {
    const Expr& v = labels[i].getExpr();
    IF_DEBUG(Type tp(frms[i], true);)
    DebugAssert(v.isVar(),
		"TheoremProducer::newPf: bad variable in LAMBDA expression: "
		+v.toString());
    DebugAssert(v.getType() == tp,
		"TheoremProducer::newPf: wrong variable type in "
		"LAMBDA expression.\nExpected: "+tp.getExpr().toString()
		+"\nFound: "+v.getType().getExpr().toString());
    u.push_back(v);
  }
  return Proof(d_tm->getEM()->newClosureExpr(LAMBDA, u, pf.getExpr()));
}


Proof TheoremProducer::newPf(const std::vector<Proof>& labels,
			     const Proof& pf) {
  std::vector<Expr> u;
  for(unsigned i=0; i<labels.size(); i++) {
    const Expr& v = labels[i].getExpr();
    DebugAssert(v.isVar(),
		"TheoremProducer::newPf: bad variable in LAMBDA expression: "
		+v.toString());
    u.push_back(v);
  }
  return Proof(d_tm->getEM()->newClosureExpr(LAMBDA, u, pf.getExpr()));
}
