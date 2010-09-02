/*****************************************************************************/
/*!
 *\file sat_proof.h
 *\brief Sat solver proof representation
 *
 * Author: Alexander Fuchs
 *
 * Created: Sun Dec 07 11:09:00 2007
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 */
/*****************************************************************************/

#ifndef _cvc3__sat__proof_h_
#define _cvc3__sat__proof_h_

#include "theorem.h"
#include <list>

namespace SAT {

  // a node in a resolution tree, either:
  // - a leaf
  //   then d_clause is a clause added to the sat solver by the cvc controller;
  //   the other values are empty
  // - a binary node
  //   then the node represents the clause which can be derived by resolution
  //   between its left and right parent on d_lit,
  //   where d_left contains d_lit and d_right contains the negation of d_lit
  class SatProofNode {
  private:
    CVC3::Theorem d_theorem;
    SatProofNode* d_left;
    SatProofNode* d_right;
    SAT::Lit      d_lit;
    CVC3::Proof   d_proof; // by yeting, to store the proof.  We do not need to set a null value to proof bcause this is done by the constructor of proof
  public:
    SatProofNode(CVC3::Theorem theorem) :
      d_theorem(theorem), d_left(NULL), d_right(NULL){
      DebugAssert(!theorem.isNull(), "SatProofNode: constructor");
    }
      //we can modify the constructor of SatProofNode(clause) to store the clauses
      //add a method to return all clauses here

    SatProofNode(SatProofNode* left, SatProofNode* right, SAT::Lit lit) :
      d_left(left), d_right(right), d_lit(lit) {
      DebugAssert(d_left != NULL, "SatProofNode: constructor");
      DebugAssert(d_right != NULL, "SatProofNode: constructor");
    }

    bool isLeaf() { return !d_theorem.isNull(); }
    CVC3::Theorem getLeaf() { DebugAssert(isLeaf(), "SatProofNode: getLeaf"); return d_theorem; }
    SatProofNode* getLeftParent() { DebugAssert(!isLeaf(), "SatProofNode: getLeftParent"); return d_left; }
    SatProofNode* getRightParent() { DebugAssert(!isLeaf(), "SatProofNode: getRightParent"); return d_right; }
    SAT::Lit getLit() { DebugAssert(!isLeaf(), "SatProofNode: getLit"); return d_lit; }
    bool hasNodeProof() {return !d_proof.isNull();};
    CVC3::Proof getNodeProof() {DebugAssert(!d_proof.isNull(), "SatProofNode: nodeProof get null"); return d_proof;}
    void setNodeProof(CVC3::Proof pf) { d_proof=pf;}
  };
  

  // a proof of the clause d_root
  class SatProof {
  private:
    SatProofNode* d_root;
    std::list<SatProofNode*> d_nodes;
  public:
    SatProof() : d_root(NULL) { };

    ~SatProof() {
      for (std::list<SatProofNode*>::iterator i = d_nodes.begin(); i != d_nodes.end(); ++i) {
	delete(*i);
      }      
    }


    // build proof

    // ownership of created node remains with SatProof
    SatProofNode* registerLeaf(CVC3::Theorem theorem) {
      SatProofNode* node = new SatProofNode(theorem);
      d_nodes.push_back(node);
      return node;
    }

    // ownership of created node remains with SatProof
    SatProofNode* registerNode(SatProofNode* left, SatProofNode* right, SAT::Lit l) {
      SatProofNode* node = new SatProofNode(left, right, l);
      d_nodes.push_back(node);
      return node;
    }

    void setRoot(SatProofNode* root) {
      d_root = root;
    }


    // access proof

    // ownership of all nodes remains with SatProof
    SatProofNode* getRoot() {
      DebugAssert(d_root != NULL, "null root found in getRoot");
      return d_root;
    }
  };

}

#endif
