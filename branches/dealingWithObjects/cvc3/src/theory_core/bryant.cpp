#include "vc.h"
#include "expr_transform.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "core_proof_rules.h"


using namespace std;
using namespace CVC3;


const int LIMIT = 55;

int ExprTransform::CountSubTerms(const Expr& e, int& counter) {
	if (e.arity() == 0)
		return 0;
	for (int i = 0; i < e.arity(); i++) {
		     int count = CountSubTerms(e[i], counter) + 1;
			 if (count > counter)
			     counter = count;
	    }
	return counter;
}

std::string ExprTransform::NewBryantVar(const int a, const int b){
	std::string S;
	std::stringstream out1, out2;
	out1 << a;
	out2 << b;
	std::string Tempvar = "A";
    S = Tempvar + out1.str() + "B" + out2.str();
	return S;
}


ExprTransform::B_name_map ExprTransform::BryantNames(T_generator_map& generator_map, B_type_map& type_map) {
	B_name_map name_map;
	int VarTotal = 0;
	for (T_generator_map::iterator f = generator_map.begin(); f != generator_map.end(); f++){
		VarTotal++;
		Type TempType = type_map.find((*f).first)->second;
		int ArgVar = 0;
		for (set< Expr >::iterator p = (*f).second->begin(); p != (*f).second->end(); p++){
			ArgVar++;
			pair< Expr, Expr > key = pair< Expr, Expr >((*f).first, (*p));
			std::string NewName = NewBryantVar(VarTotal, ArgVar);
			Expr value = d_core->newVar(NewName, TempType);
			name_map.insert( *new pair< pair< Expr, Expr>, Expr >(key, value));
		}
	}
return name_map;
}


void ExprTransform::PredConstrainer(set<Expr>& Not_replaced_set, const Expr& e, const Expr& Pred, int location, B_name_map& name_map, set<Expr>& SeenBefore, set<Expr>& Constrained_set, T_generator_map& Constrained_map, set<Expr>& P_constrained_set) {
	if (!SeenBefore.insert(e).second)
		return;
	if (e.isApply() && e.getOpKind() == UFUNC && !e.isTerm())
	if (e.getOpExpr() == Pred.getOpExpr() && Pred[location] != e[location]) {

             Expr Temp0, Temp1;
			 if (e[location].isVar() || Not_replaced_set.find(e[location]) != Not_replaced_set.end())
                      Temp0 = e[location];
			 else Temp0 = name_map.find(pair<Expr, Expr>((e[location]).getOpExpr(),(e[location])))->second;
			 if (Pred[location].isVar())
				 Temp1 = Pred[location];
			 else Temp1 = name_map.find(pair<Expr, Expr>((Pred[location]).getOpExpr(),(Pred[location])))->second;
			 if (Constrained_set.find(e[location]) != Constrained_set.end()) {
                 Expr Eq = Temp0.eqExpr(Temp1);
			     Expr Reflexor = Temp1.eqExpr(Temp0);
			     Eq = Eq.notExpr();
			     Reflexor = Reflexor.notExpr();
			     if (P_constrained_set.find(Reflexor) == P_constrained_set.end())
			           P_constrained_set.insert(Eq);
		       }



		else {
	          if (Constrained_map.find(Pred[location]) == Constrained_map.end())
				     Constrained_map.insert(pair<Expr, set<Expr>*>(Pred[location], new set<Expr>));
			  Constrained_map[Pred[location]]->insert(Temp0);

		}
	}




    for (int l = 0; l < e.arity(); l++)
       PredConstrainer(Not_replaced_set, e[l], Pred, location, name_map, SeenBefore, Constrained_set, Constrained_map, P_constrained_set);
}

void ExprTransform::PredConstrainTester(set<Expr>& Not_replaced_set, const Expr& e, B_name_map& name_map, vector<Expr>& Pred_vec, set<Expr>& Constrained_set, set<Expr>& P_constrained_set, T_generator_map& Constrained_map) {
	for (vector<Expr>::iterator i = Pred_vec.begin(); i != Pred_vec.end(); i++) {
		for (int k = 0; k < (*i).arity(); k++)
			if (Constrained_set.find((*i)[k]) != Constrained_set.end()){
     		   set<Expr> SeenBefore;
		       PredConstrainer(Not_replaced_set, e, (*i), k, name_map, SeenBefore, Constrained_set, Constrained_map, P_constrained_set);
			}
	}

}






Expr ExprTransform::ITE_generator(Expr& Orig, Expr& Value, B_Term_map& Creation_map, B_name_map& name_map,
								      T_ITE_map& ITE_map) {

    Expr NewITE;
	for (vector<Expr>::reverse_iterator f = (Creation_map.find(Orig.getOpExpr())->second->rbegin());
		f != (Creation_map.find(Orig.getOpExpr())->second->rend()); f++) {
			if ((*f).getOpExpr() == Orig.getOpExpr()) {
			Expr TempExpr;
			for (int i = 0;  i < Orig.arity(); i++) {
				Expr TempEqExpr;
			    if ((*f)[i].isApply())  //(Orig[i].isApply())
					TempEqExpr = ITE_map.find((*f)[i])->second;
				else
					TempEqExpr = (*f)[i];  // TempEqExpr = Orig[i];
			    if (Orig[i].isApply())     // ((*f)[i].isApply())
				    TempEqExpr = TempEqExpr.eqExpr(ITE_map.find(Orig[i])->second);
				else
					TempEqExpr = TempEqExpr.eqExpr(Orig[i]);
			    if (TempExpr.isNull() == true)
				    TempExpr = TempEqExpr;
			    else
				    TempExpr = TempExpr.andExpr(TempEqExpr);
			 }
	if (NewITE.isNull() == true)
	    NewITE = TempExpr.iteExpr(name_map.find(pair<Expr, Expr>((*f).getOpExpr(),(*f)))->second, Value);
	else {
		Expr Temp = NewITE;
		NewITE = TempExpr.iteExpr(name_map.find(pair<Expr, Expr>((*f).getOpExpr(),(*f)))->second, Temp);
	}
	}

	}
return NewITE;
}





void ExprTransform::Get_ITEs(B_formula_map& instance_map, set<Expr>& Not_replaced_set, B_Term_map& P_term_map, T_ITE_vec& ITE_vec, B_Term_map& Creation_map,
							  B_name_map& name_map, T_ITE_map& ITE_map) {

	for (T_ITE_vec::iterator f = ITE_vec.begin(); f != ITE_vec.end(); f++) {
		if (!(*f).isVar()) {
			if (Creation_map.find((*f).getOpExpr()) == Creation_map.end()) {
				Creation_map.insert(pair<Expr, vector<Expr>*> (
						(*f).getOpExpr(), new vector<Expr> ()));
				Creation_map[(*f).getOpExpr()]->push_back((*f));
				if (instance_map[(*f).getOpExpr()] < LIMIT || !(*f).isTerm())
					ITE_map.insert(pair<Expr, Expr> ((*f), name_map.find(pair<
							Expr, Expr> ((*f).getOpExpr(), (*f)))->second));
				else {
					ITE_map.insert(pair<Expr, Expr> ((*f), (*f)));
					Not_replaced_set.insert(*f);
				}
			} else {
				if (instance_map[(*f).getOpExpr()] > LIMIT && (*f).isTerm()) {
					ITE_map.insert(pair<Expr, Expr> ((*f), (*f)));
					Creation_map[(*f).getOpExpr()]->push_back((*f));
					Not_replaced_set.insert(*f);
				} else {
					Expr NewValue = name_map.find(pair<Expr, Expr> (
							(*f).getOpExpr(), (*f)))->second;
					Expr Add = ITE_generator((*f), NewValue, Creation_map,
							name_map, ITE_map);
					ITE_map.insert(pair<Expr, Expr> ((*f), Add));
					Creation_map[(*f).getOpExpr()]->push_back((*f));
				}
			}
		}
	}
}



void ExprTransform::RemoveFunctionApps(const Expr& orig, set<Expr>& Not_replaced_set, vector<Expr>& Old, vector<Expr>& New, T_ITE_map& ITE_map, set<Expr>& SeenBefore) {
	if (!SeenBefore.insert( orig ).second)
		return;

	for (int i = 0; i < orig.arity() ; i++)
		RemoveFunctionApps(orig[i], Not_replaced_set, Old, New, ITE_map, SeenBefore);
    if (orig.isApply() && orig.getOpKind() == UFUNC && Not_replaced_set.find(orig) != Not_replaced_set.end()) {
		Old.push_back(orig);
		New.push_back(ITE_map.find(orig)->second);
	}
}



void ExprTransform::GetSortedOpVec(B_Term_map& X_generator_map, B_Term_map& X_term_map, B_Term_map& P_term_map, set<Expr>& P_terms, set<Expr>& G_terms, set<Expr>& X_terms, vector<Expr>& sortedOps, set<Expr>& SeenBefore) {

	for (B_Term_map::iterator i = X_generator_map.begin(); i != X_generator_map.end(); i++) {

		for (vector<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++) {
			if (P_terms.find(*j) != P_terms.end()) {
				vector<Expr>::iterator k = j;
		        k++;
			    bool added = false;
				for (; k != (*i).second->end(); k++) {
					if (G_terms.find(*k) != G_terms.end() && !added) {
						if (X_term_map.find((*j).getOpExpr()) == X_term_map.end())
							X_term_map.insert(pair<Expr, vector<Expr>*>((*j).getOpExpr(), new vector<Expr>));
					    X_term_map[(*j).getOpExpr()]->push_back(*j);
					    X_terms.insert(*j);
					    added = true;

					}
				}
			}
		}
	}


	set<int> sorted;
	map<int, set<Expr>*> Opmap;
	for (B_Term_map::iterator i = P_term_map.begin(); i != P_term_map.end(); i++) {
		int count = 0;
		for (vector<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++)
			    count++;
		if (X_term_map.find((*i).first) != X_term_map.end()) {
		for (vector<Expr>::iterator j = X_term_map[(*i).first]->begin(); j != X_term_map[(*i).first]->end(); j++)
			    count--;
		}
		if (Opmap.find(count) == Opmap.end())
			Opmap.insert(pair<int, set<Expr>*>(count, new set<Expr>));
		Opmap[count]->insert((*i).first);
		sorted.insert(count);
	}
	vector<int> sortedvec;
	for (set<int>::iterator i = sorted.begin(); i != sorted.end(); i++)
         sortedvec.push_back(*i);
    sort(sortedvec.begin(), sortedvec.end());


	for (vector<int>::iterator i = sortedvec.begin(); i != sortedvec.end(); i++) {
		for (set<Expr>::iterator j = Opmap[*i]->begin(); j != Opmap[*i]->end(); j++)
			sortedOps.push_back(*j);
	}


}

void ExprTransform::GetFormulaMap(const Expr& e, set<Expr>& formula_map, set<Expr>& G_terms, int& size, int negations) {
		if (e.isEq() && negations % 2 == 1)
			   formula_map.insert(e);
		if (e.isNot())
		   negations++;
        size++;
		for (int i = 0; i < e.arity(); i++)
		GetFormulaMap(e[i], formula_map, G_terms, size, negations);
}

void ExprTransform::GetGTerms2(set<Expr>& formula_map, set<Expr>& G_terms) {

	for (set<Expr>::iterator i = formula_map.begin(); i != formula_map.end(); i++)
		if ((*i)[0].isTerm())
			for (int j = 0; j < 2; j++)  {
				 G_terms.insert((*i)[j]);
			}
}

void ExprTransform::GetSub_vec(T_ITE_vec& ITE_vec, const Expr& e, set<Expr>& ITE_Added) {

   for (int i = 0; i < e.arity(); i++ )
		GetSub_vec(ITE_vec, e[i], ITE_Added);
   if (e.isTerm() && ITE_Added.insert(e).second)
	       ITE_vec.push_back(e);
}



void ExprTransform::GetOrderedTerms(B_formula_map& instance_map, B_name_map& name_map, B_Term_map& X_term_map, T_ITE_vec& ITE_vec, set<Expr>& G_terms, set<Expr>& X_terms, vector<Expr>& Pred_vec, vector<Expr>& sortedOps, vector<Expr>& Constrained_vec, vector<Expr>& UnConstrained_vec, set<Expr>& Constrained_set, set<Expr>& UnConstrained_set, B_Term_map& G_term_map, B_Term_map& P_term_map, set<Expr>& SeenBefore, set<Expr>& ITE_Added) {


	for (vector<Expr>::iterator i = sortedOps.begin(); i != sortedOps.end(); i++){
		if (G_term_map.find(*i) != G_term_map.end()) {
			for (vector<Expr>::iterator j = G_term_map[*i]->begin(); j != G_term_map[*i]->end(); j++)
				GetSub_vec(ITE_vec,(*j), ITE_Added);
		}
	}
	for (vector<Expr>::iterator i = sortedOps.begin(); i != sortedOps.end(); i++){
		if (!P_term_map[*i]->empty()) {
			for (vector<Expr>::iterator j = P_term_map[*i]->begin(); j != P_term_map[*i]->end(); j++)
                GetSub_vec(ITE_vec, (*j), ITE_Added);
		}
     }
	for (vector<Expr>::iterator i = ITE_vec.begin(); i != ITE_vec.end(); i++) {
		if (G_terms.find(*i) != G_terms.end()) {
			UnConstrained_set.insert(*i);
			UnConstrained_vec.push_back(*i);
		}
		else if ((*i).isApply()) {
			if (instance_map[(*i).getOpExpr()] > 40){
				UnConstrained_set.insert(*i);
		        UnConstrained_vec.push_back(*i);
			}
		} else if (X_terms.find(*i) == X_terms.end()) {
			Constrained_set.insert(*i);
			Constrained_vec.push_back(*i);
		}
		else {
			vector<Expr>::iterator j = i;
			j = j + 1;
			bool found = false;
			for (; j != ITE_vec.end(); j++) {
				if (!(*j).isVar())
				    if (G_terms.find(*j) != G_terms.end() && (*j).getOpExpr() == (*i).getOpExpr() && !found) {
					    UnConstrained_vec.push_back(*i);
					    UnConstrained_set.insert(*i);
						j = ITE_vec.end();
					    j--;
					    found = true;
				    }
			}
			if (!found) {
				Constrained_vec.push_back(*i);
			    Constrained_set.insert(*i);

			}

		}
	}
    for (vector<Expr>::iterator l = Pred_vec.begin(); l != Pred_vec.end(); l++)
		ITE_vec.push_back(*l);
}







void ExprTransform::BuildBryantMaps(const Expr& e, T_generator_map& generator_map, B_Term_map& X_generator_map,
									B_type_map& type_map, vector<Expr>& Pred_vec, set<Expr>& P_terms, set<Expr>& G_terms,
									B_Term_map& P_term_map, B_Term_map& G_term_map, set< Expr >& SeenBefore, set<Expr>& ITE_Added){
	if ( !SeenBefore.insert( e ).second )
		return;
	if ( e.isApply() && e.getOpKind() == UFUNC){
		type_map.insert(pair<Expr, Type>(e.getOpExpr(), e.getType()));
	if ( generator_map.find( e.getOpExpr() ) == generator_map.end() )
			generator_map.insert(pair< Expr, set<Expr>* >( e.getOpExpr(), new set<Expr>()));
		generator_map[e.getOpExpr()]->insert(e);
	}
	if (e.isApply() && e.getOpKind() == UFUNC && !e.isTerm())
		Pred_vec.push_back(e);
	for ( int i = 0; i < e.arity(); i++ )
		BuildBryantMaps(e[i], generator_map, X_generator_map, type_map, Pred_vec, P_terms, G_terms, P_term_map, G_term_map, SeenBefore, ITE_Added);


	if (e.isTerm() && G_terms.find(e) == G_terms.end())
		P_terms.insert(e);

    if (e.isTerm()) {
		if (!e.isVar()) {
		    if (X_generator_map.find(e.getOpExpr()) == X_generator_map.end())
			    X_generator_map.insert(pair< Expr, vector<Expr>* >( e.getOpExpr(), new vector<Expr>()));
			X_generator_map[e.getOpExpr()]->push_back(e);
		}
		if (ITE_Added.insert(e).second) {
				if (G_terms.find(e) != G_terms.end()) {
					if (e.isVar()) {
						G_term_map.insert(pair<Expr, vector<Expr>*>(e, new vector<Expr>()));
						P_term_map.insert(pair<Expr, vector<Expr>*>(e, new vector<Expr>()));
						G_term_map[e]->push_back(e);

					}
					else {
						if (G_term_map.find(e.getOpExpr()) == G_term_map.end()) {
						    G_term_map.insert(pair<Expr, vector<Expr>*>(e.getOpExpr(), new vector<Expr>()));
							P_term_map.insert(pair<Expr, vector<Expr>*>(e.getOpExpr(), new vector<Expr>()));
						}
                        G_term_map[e.getOpExpr()]->push_back(e);
				    }
				}
				else {
					if (e.isVar()) {
						if (P_term_map.find(e) == P_term_map.end())
						   P_term_map.insert(pair<Expr, vector<Expr>*>(e, new vector<Expr>()));
						P_term_map[e]->push_back(e);
					}
					else {
						if (P_term_map.find(e.getOpExpr()) == P_term_map.end())
						   P_term_map.insert(pair<Expr, vector<Expr>*>(e.getOpExpr(), new vector<Expr>()));
					    P_term_map[e.getOpExpr()]->push_back(e);
					}
				}
			}
		}
return;
}

void ExprTransform::GetPEqs(const Expr& e, B_name_map& name_map, set<Expr>& P_constrained_set, set<Expr>& Constrained_set, T_generator_map& Constrained_map, set<Expr>& SeenBefore) {
    if (!SeenBefore.insert(e).second)
    	return;
	if (e.isEq()) {
		if (Constrained_set.find(e[1]) != Constrained_set.end()
				&& Constrained_set.find(e[0]) != Constrained_set.end()) {
			Expr Temp0, Temp1;
			if (e[0] != e[1]) {
				if (e[0].isVar())
					Temp0 = e[0];
				else
					Temp0 = name_map.find(pair<Expr, Expr> ((e[0]).getOpExpr(),
							(e[0])))->second;
				if (e[1].isVar())
					Temp1 = e[1];
				else
					Temp1 = name_map.find(pair<Expr, Expr> ((e[1]).getOpExpr(),
							(e[1])))->second;
				Expr Eq = Temp0.eqExpr(Temp1);
				Expr Reflexor = Temp1.eqExpr(Temp0);
				Eq = Eq.notExpr();
				Reflexor = Reflexor.notExpr();
				if (P_constrained_set.find(Reflexor) == P_constrained_set.end())
					P_constrained_set.insert(Eq);
			}
		} else if (Constrained_set.find(e[0]) != Constrained_set.end()) {
			if (Constrained_map.find(e[0]) == Constrained_map.end())
				Constrained_map.insert(pair<Expr, set<Expr>*> (e[0], new set<
						Expr> ));
			Constrained_map[e[0]]->insert(e[1]);
		} else if (Constrained_set.find(e[1]) != Constrained_set.end()) {
			if (Constrained_map.find(e[1]) == Constrained_map.end())
				Constrained_map.insert(pair<Expr, set<Expr>*> (e[1], new set<
						Expr> ));
			Constrained_map[e[1]]->insert(e[0]);
		}
	}
	for (int i = 0; i < e.arity(); i++)
		 GetPEqs(e[i], name_map, P_constrained_set, Constrained_set, Constrained_map, SeenBefore);
}

Expr ExprTransform::ConstrainedConstraints(set<Expr>& Not_replaced_set, T_generator_map& Constrained_map, B_name_map& name_map, B_Term_map& Creation_map, set<Expr>& Constrained_set, set<Expr>& UnConstrained_set, set<Expr>& P_constrained_set) {
	if (Constrained_set.empty())
		return d_core->trueExpr();


	for (T_generator_map::iterator f = Constrained_map.begin(); f != Constrained_map.end(); f++) {

              Expr Value;
		if ((*f).first.isVar())
			Value = (*f).first;
		else
			Value = name_map.find(pair<Expr, Expr>((*f).first.getOpExpr(),(*f).first))->second;
			for (set<Expr>::iterator j = (*f).second->begin(); j != (*f).second->end(); j++) {
			       if (Value != (*j)) {
                            if ((*j).isVar() || Not_replaced_set.find(*j) != Not_replaced_set.end()){
					Expr Temp = Value.eqExpr(*j);
					Temp = Temp.notExpr();
					P_constrained_set.insert(Temp);
				}
				else {
				vector<Expr>::iterator c = Creation_map[(*j).getOpExpr()]->begin();
				bool done = false;
				while ( !done && c != Creation_map[(*j).getOpExpr()]->end() ) {
					if ((*c) == (*j))
						done = true;
					Expr Temp = name_map.find(pair<Expr, Expr>((*c).getOpExpr(),(*c)))->second;
					Expr TempEqExpr = Value.eqExpr(Temp);
					TempEqExpr = TempEqExpr.notExpr();
					if (!Value == Temp)
                       P_constrained_set.insert(TempEqExpr);
					c++;
					}
				}

			}
		}
	}
	if (P_constrained_set.empty())
		return d_core->trueExpr();
	else {
	Expr Constraints = *(P_constrained_set.begin());
	set<Expr>::iterator i = P_constrained_set.begin();
	i++;
	for (; i != P_constrained_set.end(); i++)
         Constraints = Constraints.andExpr(*i);

    return Constraints;
	}
}


void ExprTransform::GetOrdering(B_Term_map& X_generator_map, B_Term_map& G_term_map, B_Term_map& P_term_map) {

	for (B_Term_map::iterator i = X_generator_map.begin(); i != X_generator_map.end(); i++) {
		map<int, vector<Expr>*> Order_map;
		set<int> Order_set;
		for (vector<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++) {
			int temp = 0;
			int Counter = CountSubTerms(*j, temp);
			if (Order_map.find(Counter) == Order_map.end())
                Order_map.insert(pair<int, vector<Expr>*>(Counter, new vector<Expr>));
			Order_map[Counter]->push_back(*j);
			Order_set.insert(Counter);
		}
		vector<int> Order_vec;
		for (set<int>::iterator m = Order_set.begin(); m != Order_set.end(); m++)
            Order_vec.push_back(*m);
		(*i).second->clear();
		sort(Order_vec.begin(), Order_vec.end());
		for (vector<int>::iterator k = Order_vec.begin(); k != Order_vec.end(); k++)
			for (vector<Expr>::iterator l = Order_map[*k]->begin(); l != Order_map[*k]->end(); l++){
				(*i).second->push_back(*l);

			}
	}

for (B_Term_map::iterator i = G_term_map.begin(); i != G_term_map.end(); i++) {
		map<int, vector<Expr>*> Order_map;
		set<int> Order_set;
		for (vector<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++) {
			int temp = 0;
			int Counter = CountSubTerms(*j, temp);
			if (Order_map.find(Counter) == Order_map.end())
                Order_map.insert(pair<int, vector<Expr>*>(Counter, new vector<Expr>));
			Order_map[Counter]->push_back(*j);
			Order_set.insert(Counter);
		}
		vector<int> Order_vec;
		for (set<int>::iterator m = Order_set.begin(); m != Order_set.end(); m++)
            Order_vec.push_back(*m);
		(*i).second->clear();
		sort(Order_vec.begin(), Order_vec.end());
		for (vector<int>::iterator k = Order_vec.begin(); k != Order_vec.end(); k++)
			for (vector<Expr>::iterator l = Order_map[*k]->begin(); l != Order_map[*k]->end(); l++){
				(*i).second->push_back(*l);
			}
	}

for (B_Term_map::iterator i = P_term_map.begin(); i != P_term_map.end(); i++) {
		map<int, vector<Expr>*> Order_map;
		set<int> Order_set;
		for (vector<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++) {
			int temp = 0;
			int Counter = CountSubTerms(*j, temp);
			if (Order_map.find(Counter) == Order_map.end())
                Order_map.insert(pair<int, vector<Expr>*>(Counter, new vector<Expr>));
			Order_map[Counter]->push_back(*j);
			Order_set.insert(Counter);
		}
		vector<int> Order_vec;
		for (set<int>::iterator m = Order_set.begin(); m != Order_set.end(); m++)
            Order_vec.push_back(*m);
		(*i).second->clear();
		sort(Order_vec.begin(), Order_vec.end());
		for (vector<int>::iterator k = Order_vec.begin(); k != Order_vec.end(); k++)
			for (vector<Expr>::iterator l = Order_map[*k]->begin(); l != Order_map[*k]->end(); l++){
				(*i).second->push_back(*l);
			}
	}
}

void ExprTransform::B_Term_Map_Deleter(B_Term_map& Map) {
	for (B_Term_map::iterator j = Map.begin(); j != Map.end(); j++)
	    delete (*j).second;
}

void ExprTransform::T_generator_Map_Deleter(T_generator_map& Map) {
	for (T_generator_map::iterator j = Map.begin(); j != Map.end(); j++)
		delete (*j).second;
}

Theorem ExprTransform::dobryant(const Expr& T){

	Expr U = T.notExpr();
	set<Expr> P_terms, G_terms, X_terms, formula_1_map, Constrained_set, UnConstrained_set, P_constrained_set, UnConstrained_Pred_set, Not_replaced_set;
	B_name_map name_map;
	B_type_map type_map;
	B_Term_map P_term_map, G_term_map, X_term_map, X_generator_map, Creation_map;
	B_formula_map instance_map;
	T_generator_map generator_map, Constrained_map;
	T_ITE_vec ITE_vec;
	T_ITE_map ITE_map;
	int size = 0;
	GetFormulaMap(U, formula_1_map, G_terms, size, 0);


	GetGTerms2(formula_1_map, G_terms);
	vector<Expr> sortedOps, Constrained_vec, UnConstrained_vec, Pred_vec;
	set<Expr> SeenBefore1, ITE_Added1;
	BuildBryantMaps(U, generator_map, X_generator_map, type_map, Pred_vec, P_terms, G_terms, P_term_map, G_term_map, SeenBefore1, ITE_Added1);
	bool proceed = false;
	for (T_generator_map::iterator i = generator_map.begin(); i != generator_map.end(); i++)
	if ((*i).second->begin()->isTerm()) {

              int count = 0;
	    for (set<Expr>::iterator j = (*i).second->begin(); j != (*i).second->end(); j++)
			count++;
	    if (count <= LIMIT)
              proceed = true;
           instance_map.insert(pair<Expr, int>((*i).first, count));
	}


       if (!proceed)
         return d_core->reflexivityRule(T);


	GetOrdering(X_generator_map, G_term_map, P_term_map);
	name_map = BryantNames(generator_map, type_map);
	set<Expr> SeenBefore2;
	GetSortedOpVec(X_generator_map, X_term_map, P_term_map, P_terms, G_terms, X_terms, sortedOps, SeenBefore2);
	set<Expr> SeenBefore3, ITE_added3;
	GetOrderedTerms(instance_map, name_map, X_term_map, ITE_vec, G_terms, X_terms, Pred_vec, sortedOps, Constrained_vec, UnConstrained_vec, Constrained_set, UnConstrained_set, G_term_map, P_term_map, SeenBefore3, ITE_added3);




	//PredicateEliminator(U, Pred_vec, UnConstrained_Pred_set, name_map, ITE_map, Constrained_set);

	Get_ITEs(instance_map, Not_replaced_set, P_term_map, ITE_vec, Creation_map, name_map, ITE_map);

	set<Expr> SeenBefore4;
	GetPEqs(U, name_map, P_constrained_set, Constrained_set, Constrained_map, SeenBefore4);


      PredConstrainTester(Not_replaced_set, U, name_map, Pred_vec, Constrained_set, P_constrained_set, Constrained_map);

	Expr Constraints = ConstrainedConstraints(Not_replaced_set, Constrained_map, name_map, Creation_map, Constrained_set, UnConstrained_set, P_constrained_set);

        //       Constraints.pprintnodag();
	vector< Expr > Old;
	vector< Expr > New;







	set<Expr> SeenBefore6;

	RemoveFunctionApps(U, Not_replaced_set, Old, New, ITE_map, SeenBefore6);
	Expr Result = U.substExpr(Old, New);
	Expr Final = Constraints.impExpr(Result);
	Final = Final.notExpr();




	   B_Term_Map_Deleter(Creation_map);
	   B_Term_Map_Deleter(X_generator_map);
       B_Term_Map_Deleter(X_term_map);
	   B_Term_Map_Deleter(G_term_map);
       T_generator_Map_Deleter(Constrained_map);
	   T_generator_Map_Deleter(generator_map);


       return d_rules->dummyTheorem(T.iffExpr(Final));


}







