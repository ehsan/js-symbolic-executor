/*****************************************************************************/
/*!
 *\file bitvector_expr_value.h
 *\brief Subclasses of ExprValue for bit-vector expressions
 *
 * Author: Sergey Berezin, Vijay Ganesh
 *
 * Created: Wed Jun 23 14:36:59 2004
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

#ifndef _cvc3__theory_bitvector__bitvector_expr_value_h_
#define _cvc3__theory_bitvector__bitvector_expr_value_h_

#include "theory_bitvector.h"

namespace CVC3 {

///////////////////////////////////////////////////////////////////////////////
//class BVConstExpr
///////////////////////////////////////////////////////////////////////////////
//! An expression subclass for bitvector constants.
class BVConstExpr : public ExprValue {
private:
  std::vector<bool> d_bvconst; //!< value of bitvector constant
  size_t d_MMIndex; //!< The registration index for ExprManager
 public:
  //! Constructor
  BVConstExpr(ExprManager* em, std::string bvconst,
	      size_t mmIndex, ExprIndex idx = 0);
  
  //! Constructor
  BVConstExpr(ExprManager* em, std::vector<bool> bvconst,
	      size_t mmIndex, ExprIndex idx = 0);
  
  ExprValue* copy(ExprManager* em, ExprIndex idx = 0) const {
    return new(em->getMM(getMMIndex()))
      BVConstExpr(em, d_bvconst, d_MMIndex, idx);
  }

  size_t computeHash() const;
  size_t getMMIndex() const { return d_MMIndex; }

  const ExprValue* getExprValue() const { return this; }
  
  //! Only compare the bitvector constant, not the integer attribute
  bool operator==(const ExprValue& ev2) const {
    if(ev2.getMMIndex() != d_MMIndex) return false;
    return (d_bvconst == ((const BVConstExpr&)ev2).d_bvconst);
  }
  
  void* operator new(size_t size, MemoryManager* mm) {
    return mm->newData(size);
  }
  void operator delete(void* pMem, MemoryManager* mm) {
    mm->deleteData(pMem);
  }

  void operator delete(void*) { }

  unsigned size() const { return d_bvconst.size(); }
  bool getValue(int i) const
    { DebugAssert(0 <= i && (unsigned)i < size(), "out of bounds");
      return d_bvconst[i]; }

}; //end of BVConstExpr

} // end of namespace CVC3
#endif
