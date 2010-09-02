/*****************************************************************************/
/*!
 * \file records_theorem_producer.h
 * 
 * Author: Daniel Wichs
 * 
 * Created: Jul 22 22:59:07 GMT 2003
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
#ifndef _cvc3__records_theorem_producer_h_
#define _cvc3__records_theorem_producer_h_

#include "records_proof_rules.h"
#include "theorem_producer.h"
#include "theory_records.h"

namespace CVC3 {
  
  class RecordsTheoremProducer: public RecordsProofRules,
    public TheoremProducer {
      TheoryRecords* d_theoryRecords;

    public:
    // Constructor
      RecordsTheoremProducer(TheoremManager* tm, TheoryRecords* t):
	TheoremProducer(tm), d_theoryRecords(t) { }
      Theorem rewriteLitSelect(const Expr &e);
      Theorem rewriteUpdateSelect(const Expr& e);
      Theorem rewriteLitUpdate(const Expr& e);
      Theorem expandEq(const Theorem& eqThrm);
      Theorem expandNeq(const Theorem& neqThrm);
      Theorem expandRecord(const Expr& e);
      Theorem expandTuple(const Expr& e);

      // Expr creation functions
      //! Test whether expr is a record type
      bool isRecordType(const Expr& e)
	{ return d_theoryRecords->isRecordType(e); }
      //! Test whether Type is a record type
      bool isRecordType(const Type& t)
	{ return d_theoryRecords->isRecordType(t); }
      //! Test whether expr is a record select/update subclass
      bool isRecordAccess(const Expr& e)
	{ return d_theoryRecords->isRecordAccess(e); }
      //! Create a record literal
      Expr recordExpr(const std::vector<std::string>& fields,
		      const std::vector<Expr>& kids)
	{ return d_theoryRecords->recordExpr(fields, kids); }
      //! Create a record literal
      Expr recordExpr(const std::vector<Expr>& fields,
		      const std::vector<Expr>& kids)
	{ return d_theoryRecords->recordExpr(fields, kids); }
      //! Create a record type
      Type recordType(const std::vector<std::string>& fields,
		      const std::vector<Type>& types)
	{ return d_theoryRecords->recordType(fields, types); }
      //! Create a record type (field types are given as a vector of Expr)
      Type recordType(const std::vector<std::string>& fields,
		      const std::vector<Expr>& types)
	{ return d_theoryRecords->recordType(fields, types); }
      //! Create a record field select expression
      Expr recordSelect(const Expr& r, const std::string& field)
	{ return d_theoryRecords->recordSelect(r, field); }
      //! Create a record field update expression
      Expr recordUpdate(const Expr& r, const std::string& field,
			const Expr& val)
	{ return d_theoryRecords->recordUpdate(r, field, val); }
      //! Get the list of fields from a record literal
      const std::vector<Expr>& getFields(const Expr& r)
	{ return d_theoryRecords->getFields(r); }
      //! Get the i-th field name from the record literal or type
      const std::string& getField(const Expr& e, int i)
	{ return d_theoryRecords->getField(e, i); }
      //! Get the field index in the record literal or type
      /*! The field must be present in the record; otherwise it's an error. */
      int getFieldIndex(const Expr& e, const std::string& field)
	{ return d_theoryRecords->getFieldIndex(e, field); }
      //! Get the field name from the record select and update expressions
      const std::string& getField(const Expr& e)
	{ return d_theoryRecords->getField(e); }
      //! Create a tuple literal
      Expr tupleExpr(const std::vector<Expr>& kids)
	{ return d_theoryRecords->tupleExpr(kids); }
      //! Create a tuple type
      Type tupleType(const std::vector<Type>& types)
	{ return d_theoryRecords->tupleType(types); }
      //! Create a tuple type (types of components are given as Exprs)
      Type tupleType(const std::vector<Expr>& types)
	{ return d_theoryRecords->tupleType(types); }
      //! Create a tuple index selector expression
      Expr tupleSelect(const Expr& tup, int i)
	{ return d_theoryRecords->tupleSelect(tup, i); }
      //! Create a tuple index update expression
      Expr tupleUpdate(const Expr& tup, int i, const Expr& val)
	{ return d_theoryRecords->tupleUpdate(tup, i, val); }
      //! Get the index from the tuple select and update expressions
      int getIndex(const Expr& e)
	{ return d_theoryRecords->getIndex(e); }
      //! Test whether expr is a tuple select/update subclass
      bool isTupleAccess(const Expr& e)
	{ return d_theoryRecords->isTupleAccess(e); }
    };

} 

#endif
