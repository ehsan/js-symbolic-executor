#include "LFSCLraProof.h"

//LFSCLraAdd ...

void LFSCLraAdd::print_pf( std::ostream& s, int ind )
{
  s<<"(lra_add_";
  s <<kind_to_str(d_op1);
  s <<"_";
  s << kind_to_str(d_op2);
  s <<" _ _ _ ";
  d_children[0]->print(s, ind+1);
  s<<" ";
  d_children[1]->print(s, ind+1);
  s<<")";
}
LFSCProof* LFSCLraAdd::Make(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2)
{
  if( pf1->isTrivial() )
    return pf2;
  else if( pf2->isTrivial() )
    return pf1;
  else{
    op1 = pf1->checkOp()!=-1 ? pf1->checkOp() : op1;
    op2 = pf2->checkOp()!=-1 ? pf2->checkOp() : op2;
    if( get_knd_order( op1 )>get_knd_order( op2 ) )
      return Make( pf2, pf1, op2, op1 );
    else
      return new LFSCLraAdd( pf1, pf2, op1, op2 );
  }
}

// LFSCLraAxiom ...

RefPtr< LFSCProof > LFSCLraAxiom::eq;

LFSCProof* LFSCLraAxiom::MakeEq(){ 
  if( !eq.get() ){
    eq = new LFSCLraAxiom( EQ ); 
  }
  return eq.get();
}

void LFSCLraAxiom::print_pf( std::ostream& s, int ind )
{
  s<<"(lra_axiom_" << kind_to_str(d_op);
  if( d_op!= EQ ){
    s << " ";
    print_rational( d_r, s );
  }
  s<<")";
}

//LFSCLraMulC ...

void LFSCLraMulC::print_pf( std::ostream& s, int ind )
{
  s <<"(lra_mul_c_"<<kind_to_str(d_op)<<" _ _ ";
  print_rational( d_r, s );
  s << " ";
  d_pf->print( s, ind+1 );
  s << ")";
}

LFSCProof* LFSCLraMulC::Make(LFSCProof* pf, Rational r, int op)
{
  if( pf->isTrivial() || r==1 )
    return pf;
  else if( pf->AsLFSCLraMulC() ){
    Rational rt = r*pf->AsLFSCLraMulC()->d_r;
    if( rt==1 )
      return pf->AsLFSCLraMulC()->d_pf.get();
    else
      return new LFSCLraMulC( pf->AsLFSCLraMulC()->d_pf.get(), rt, op );
  }else
    return new LFSCLraMulC( pf, r, op );
}

//LFSCLraSub ...

void LFSCLraSub::print_pf( std::ostream& s, int ind ){
  s <<"(lra_sub_"<<kind_to_str(d_op1)<<"_"<<kind_to_str(d_op2)<<" _ _ _ ";
  d_children[0]->print(s, ind+1);
  s <<" ";
  d_children[1]->print(s, ind+1);
  s <<")";
}

LFSCProof* LFSCLraSub::Make(LFSCProof* pf1, LFSCProof* pf2, int op1, int op2){
  if( pf2->isTrivial() )
    return pf1;
  else if( pf1->isTrivial() ){
    Rational r = Rational( -1 );
    return LFSCLraMulC::Make( pf2, r, op2 );
  }else
    return new LFSCLraSub( pf1, pf2, op1, op2 );
}

//LFSCLraPoly ...

void LFSCLraPoly::print_pf( std::ostream& s, int ind ){
  if( d_var<0 ){
    s << "(lra_not_" << kind_to_str(get_normalized( d_op ));
    s << "_to_" << kind_to_str(get_normalized( get_not( d_op ) ));
    s << " _ _";
  }
  s << " (poly_form";
  if( d_var<0 )
    s << "_not";
  s << " _ _ @pn" << abs( d_var ) << " ";
  d_pf->print( s, ind );
  s << ")";
  if( d_var<0 )
    s << ")";
}

LFSCProof* LFSCLraPoly::Make( const Expr& e, LFSCProof* p )
{
  Expr e1 = queryAtomic( e );
  Expr eb = queryAtomic( e, true );
  if( is_eq_kind( e1.getKind() ) )
  {
    int m = queryM( e );
    //get the required term that is needed to normalize
    Expr et;
    if( is_opposite( eb.getKind() )  )
      et = Expr( MINUS, eb[1], eb[0] );
    else
      et = Expr( MINUS, eb[0], eb[1] );

    //et.print();

    //get the polynomial normalization proof number
    int valT = queryMt( et );
    //store it in d_pn_form (this will setup the proper pn*)
    d_pn_form[eb] = valT;

    p = LFSCLraPoly::Make( p, m, eb.getKind() );
    p->setChOp( get_normalized( e1.getKind() ) );
    return p;
    //if( m<0 )
    //{
    //  os << "(lra_not_" << kind_to_str(get_normalized( eb.getKind() ));
    //  os << "_to_" << kind_to_str(get_normalized( get_not( eb.getKind() ) ));
    //  os << " _ _";
    //  os2 << ")";
    //}
    //os << " (poly_form";
    //if( m<0 )
    //  os << "_not";
    //os << " _ _ @pn" << abs( m ) << " ";
    //os2 << ")";
  }
  else
  {
    ostringstream ose;
    ose << "ERROR:make_polynomial_proof: Trying to make non-atomic " << e1 << " " << e.isNot() << std::endl;
    ose << e << std::endl;
    print_error( ose.str().c_str(), cout );
    return NULL;
  }
}
