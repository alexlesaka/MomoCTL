include "Parsing_CTL_to_NNF_Sequents.dfy"
include "Auxiliaries_Tableau.dfy"
include "Print_Proofs.dfy"

module Tableau_Sat_Unsat {
    import opened Parsing_CTL_to_NNF_Sequents
	import opened Auxiliaries_Tableau
	import opened Print_Proofs


//is_unsat? is a version of is_refutable? THAT DOES NOT COMPUTE PROOFS NOR MODELS.
//This predicate is_unsat? gives true if the input sequent is unsatisfiable
//and otherwise it gives False. 
//is_unsat? applies the tableau rules without cycles checking
//is_unsat_child? do exactly the same but checking if there is a cycle in the branch
//The second is only call when the sequent is one of the children of the rule next-state.

method is_unsat? (	Sigma:seq<NNF_Formula>, //current sequent to be refuted
                    B:Branch,               //current branch
					APA: set<seq<NNF_Formula>>, //As Proved Above (set of elementary sequents)
					Inv:seq<NNF_Formula>, //Input formulas of the form AG(_)
					n:nat,              //CALL DEPTH
					SAT: set<seq<NNF_Formula>> //Sequents already proved satisfiable.
				 ) 
             returns (b:bool,      //True, if a refutation for Sigma is found, otherwise False
			          B':Branch,   //new branch to be explored
					  comp:int,   //companion node (>=0) of the last node in the current branch, 
					            // -1 if there is not cycle
					  APA': set<seq<NNF_Formula>>, 
					  SAT': set<seq<NNF_Formula>>
					  )
requires is_ordered(Sigma) && is_ordered(Inv)
requires B != []
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
if Sigma == [] {  
        b:= false;  B' := B;  APA' := APA; SAT' := SAT; 
		}
else if Sigma[|Sigma|-1] == F {
        b := true; APA' := APA; B' := B; SAT' := SAT; 
		}
else if is_Ctd(Sigma) { 
		b := true;  APA' := APA; B' := B; SAT' := SAT; 
		}
else if is_selected_Ev(Sigma[0]) ||
	    (is_non_selected_Ev(Sigma[0]) && there_is_not_selected_Ev_in(Sigma)) {
	 b,B',comp,APA',SAT' := apply_plus(Sigma,B,APA,Inv,n,SAT); 
	 }
else if !is_literal(Sigma[0]) && !is_next(Sigma[0]) {
							b,B',comp,APA',SAT' := apply_alpha_beta(Sigma,B,APA,Inv,n,SAT);
							}
else { 
	 minimality_of_elementary_Lemma(Sigma);
	 b,B',comp,APA',SAT' := apply_Next_State(Sigma,B,APA,Inv,n,SAT); 
     }
}

method is_unsat_child? (Sigma:seq<NNF_Formula>, //current sequent to be refuted
						B:Branch,               //current branch
						APA: set<seq<NNF_Formula>>, //As Proved Above (set of elementary sequents)
						Inv:seq<NNF_Formula>, //Input formulas of the form AG(_)
						n:nat,              //call depth
						SAT: set<seq<NNF_Formula>>
					   ) 
             returns (b:bool,      //T, if Sigma has been refuted, otherwise F
			          B':Branch,   //new branch to be explored
					  comp:int,   //companion node (>=0) of the last node in the current branch, -1 if there is not cycle
					  APA': set<seq<NNF_Formula>>, 
					  SAT': set<seq<NNF_Formula>>
					  )
requires is_ordered(Sigma) && is_ordered(Inv)
requires B != []
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
if Sigma == [] {  
        b:= false;  B' := B;  APA' := APA; SAT' := SAT; //print "\nis empty";
		}
else if Sigma[|Sigma|-1] == F {
        b := true; APA' := APA; B' := B; SAT' := SAT; //print "\nis (F)";
		}
else if is_Ctd(Sigma) { 
		b := true;  APA' := APA; B' := B; SAT' := SAT; //print "\nis (Ctd))";
		}
else {  
	  var currentcomp := min_stage(B,Sigma,Inv);
	  if currentcomp >= 0 { 
			b,B',comp,APA',SAT' := cycle_handling(currentcomp,Sigma,B,APA,Inv,n,SAT);
			}
	  else if is_selected_Ev(Sigma[0]) ||
		   (is_non_selected_Ev(Sigma[0]) && there_is_not_selected_Ev_in(Sigma)) {
			b,B',comp,APA',SAT' := apply_plus(Sigma,B,APA,Inv,n,SAT); 
			}
	  else if !is_literal(Sigma[0]) && !is_next(Sigma[0]) {
			b,B',comp,APA',SAT' := apply_alpha_beta(Sigma,B,APA,Inv,n,SAT);
			}
	  else  { 
			minimality_of_elementary_Lemma(Sigma);
			b,B',comp,APA',SAT' := apply_Next_State(Sigma,B,APA,Inv,n,SAT); 
			}
     }
}

// Cycles handling

method cycle_handling (currentcomp: nat, Sigma:seq<NNF_Formula>,B:Branch,APA: set<seq<NNF_Formula>>,
                        Inv:seq<NNF_Formula>,n:nat,SAT: set<seq<NNF_Formula>>) 
                returns(b:bool,B':Branch,comp:int,APA': set<seq<NNF_Formula>>,SAT': set<seq<NNF_Formula>>)
requires is_ordered(Sigma) && is_ordered(Inv)
requires B != []
requires 0 <= currentcomp < |B|
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
var ev_index := is_Ev_covered_cycle(Sigma,B,currentcomp);
if ev_index >= 0 {
	var SigmaMinusEv := if ev_index > 0 && (Sigma[0].AUsel? || Sigma[0].EUsel?)
	                    then insert(to_unselected(Sigma[0]),Sigma[1..ev_index] + Sigma[ev_index+1..])
						else Sigma[..ev_index] + Sigma[ev_index+1..];
	ordered_Lemma(Sigma);
	if ev_index > 0 {ordered_Lemma(Sigma[1..ev_index] + Sigma[ev_index+1..]);}
	ordered_Lemma (SigmaMinusEv);
	var newEv := to_selected(Sigma[ev_index]);
	var SigmaNewEv := insert(newEv,SigmaMinusEv);
	insert_preserves_order_Lemma();
	var Bnew := add_formula_to_last_stage(B,newEv); 
	b,B',comp,APA',SAT' := is_unsat?(SigmaNewEv,Bnew,APA,Inv,n+1,SAT);
    } 
else {
	 b := false; B' := B;  APA' := APA; SAT' := SAT; comp := currentcomp;
	 } 
}


// Implementation of the Alpha and Beta Rules

method apply_alpha_beta(Sigma:seq<NNF_Formula>,B:Branch,APA: set<seq<NNF_Formula>>,
                        Inv:seq<NNF_Formula>,n:nat,SAT: set<seq<NNF_Formula>>) 
                returns(b:bool,B':Branch,comp:int,APA': set<seq<NNF_Formula>>,SAT': set<seq<NNF_Formula>>)
requires is_ordered(Sigma) && is_ordered(Inv)
requires Sigma != []
requires B != []
requires !is_literal(Sigma[0]) && !is_next(Sigma[0])
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
assert is_ordered(Sigma[1..]);
insert_preserves_order_Lemma();
//
var b1,b2;
match Sigma[0]
case AG(sigma) => var Sigma1 := insert(sigma,insert(AX(Sigma[0]),Sigma[1..]));
                  B' := add_formula_to_last_stage(B,sigma);
                  if Sigma[0] !in Inv { B' := add_formula_to_last_stage(B',AX(Sigma[0])); } //AX(Inv) are not added to stages
				  b,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
case EG(sigma) => var Sigma1 := insert(sigma,insert(EX(Sigma[0]),Sigma[1..]));
                  B' := add_seq_to_last_stage(B,[sigma,EX(Sigma[0])]);
				  b,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
case AR(sigma1,sigma2) =>  if AG(neg_in_nnf(sigma1)) in Sigma[1..] 
								{
								var Sigma' := insert(AG(sigma2),Sigma[1..]);
								B' := add_formula_to_last_stage(B,AG(sigma2));
								b,B',comp,APA',SAT' := is_unsat?(Sigma',B',APA,Inv,n+1,SAT);
								}
                          else {
								var Sigma' := insert(sigma2,insert(Or(sigma1,AX(Sigma[0])),Sigma[1..]));
						        B' := add_seq_to_last_stage(B,[sigma2,Or(sigma1,AX(Sigma[0]))]);
								b,B',comp,APA',SAT' := is_unsat?(Sigma',B',APA,Inv,n+1,SAT);
								}
case ER(sigma1,sigma2) =>  var Sigma' := insert(sigma2,insert(Or(sigma1,EX(Sigma[0])),Sigma[1..]));
						   B' := add_seq_to_last_stage(B,[sigma2,Or(sigma1,EX(Sigma[0]))]);
						   b,B',comp,APA',SAT' := is_unsat?(Sigma',B',APA,Inv,n+1,SAT);									
case AF(sigma) =>   var Sigma1 := insert(sigma,Sigma[1..]);
					B' := add_formula_to_last_stage(B,sigma);
					b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
					if b1 { 
							var Sigma2 := insert(AX(Sigma[0]),Sigma[1..]);
							B' := add_formula_to_last_stage(B,AX(Sigma[0]));
							b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
							b := b2;
							}
					else { 
							b := false; 
							}			        
case EF(sigma) => 	var Sigma1 := insert(sigma,Sigma[1..]);
					B' := add_formula_to_last_stage(B,sigma);
					b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
					if b1 { 		
							var Sigma2 := insert(EX(Sigma[0]),Sigma[1..]);
							B' := add_formula_to_last_stage(B,EX(Sigma[0]));
							b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
							b := b2;
						}
					else { 
							b := false; 
							}
case AU(sigma1,sigma2) => 	var Sigma1 := insert(sigma2,Sigma[1..]);
								B' := add_formula_to_last_stage(B,sigma2);
								b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
								if b1 { 
										var Sigma2 := insert(AX(Sigma[0]),insert(sigma1,Sigma[1..]));
										B' := add_seq_to_last_stage(B,[sigma1,AX(Sigma[0])]);
										b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
										b := b2;
									 }
								else { 
									 b := false; 
									 }
case EU(sigma1,sigma2) => 	var Sigma1 := insert(sigma2,Sigma[1..]);
							B' := add_formula_to_last_stage(B,sigma2);
							b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
							if b1 { 
									var Sigma2 := insert(EX(Sigma[0]),insert(sigma1,Sigma[1..]));
									B' := add_seq_to_last_stage(B,[sigma1,EX(Sigma[0])]);
									b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
									b := b2;
									}
							else { 
								b := false; 
								}
case AUsel(sigma1,sigma2) =>    var Sigma1 := insert(sigma2,Sigma[1..]);
								B' := add_formula_to_last_stage(B,sigma2);
								b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
								if b1  { 
										var Sigma2 := insert(AX(Sigma[0]),insert(sigma1,Sigma[1..]));
										B' := add_seq_to_last_stage(B,[sigma1,AX(Sigma[0])]);
										b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
										b := b2;
										}
								  else { 
									   b := false; 
									   }
case EUsel(sigma1,sigma2) => var Sigma1 := insert(sigma2,Sigma[1..]);
                             B' := add_formula_to_last_stage(B,sigma2);
				             b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
						     if b1 { 
							       var Sigma2 := insert(EX(Sigma[0]),insert(sigma1,Sigma[1..]));
								   B' := add_seq_to_last_stage(B,[sigma1,EX(Sigma[0])]);
						           b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
						           b := b2;
								   }
						     else { 
								   b := false; 
								   }
case And(sigma1,sigma2) => var Sigma1 := insert(sigma1,insert(sigma2,Sigma[1..]));
                           B' := add_seq_to_last_stage(B,[sigma1,sigma2]);
						   b,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
case Or(sigma1,sigma2) =>  if is_subsumed_Or(Sigma[0],Sigma[1..]) {
								b,B',comp,APA',SAT' := is_unsat?(Sigma[1..],B,APA,Inv,n+1,SAT); 
                                }
                           else {
							    var newOr := clean_Or(Sigma[0],Sigma[1..]);
								var Bnew := add_formula_to_last_stage(B,newOr); 
								if !newOr.Or? {
									          var Sigma' := insert(newOr,Sigma[1..]);
											  b,B',comp,APA',SAT' := is_unsat?(Sigma',Bnew,APA,Inv,n+1,SAT); 
                                              }
								else {
									var Sigma1:= insert(newOr.f1,Sigma[1..]);
									var B1 := add_formula_to_last_stage(Bnew,newOr.f1);
									b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B1,APA,Inv,n+1,SAT); 
									if b1 { 
										var Sigma2 := insert(newOr.f2,Sigma[1..]);
										var B2 := add_formula_to_last_stage(Bnew,newOr.f2);
										b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B2,APA',Inv,n+1,SAT'); 
										b := b2; 
										}
									else { 
										b := false; 
										}
									  }
								}
}

// Implementation of Beta+ Rules (using the Negated Context)

method apply_plus(Sigma:seq<NNF_Formula>,B:Branch,APA: set<seq<NNF_Formula>>,Inv:seq<NNF_Formula>,n:nat,SAT: set<seq<NNF_Formula>>) 
                returns(b:bool,B':Branch,comp:int,APA': set<seq<NNF_Formula>>,SAT': set<seq<NNF_Formula>>)
requires is_ordered(Sigma) && is_ordered(Inv)
requires Sigma != []
requires B != []
requires is_Ev(Sigma[0])
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
var s := if Sigma[0].AUsel? || Sigma[0].AU? then "AU+"  
         else if Sigma[0].EUsel? || Sigma[0].EU? then "EU+"
		 else if Sigma[0].AF? then "AF+"
		 else "EF+";
var Sigma1 := if Sigma[0].AUsel? || Sigma[0].EUsel? || Sigma[0].AU? || Sigma[0].EU?
              then insert(Sigma[0].f2,Sigma[1..]) 
			  else insert(Sigma[0].f,Sigma[1..]);
if Sigma[0].AUsel? || Sigma[0].EUsel? || Sigma[0].AU? || Sigma[0].EU?
      {B' := add_formula_to_last_stage(B,Sigma[0].f2);}
else  {B' := add_formula_to_last_stage(B,Sigma[0].f);}
var b1,b2;
insert_preserves_order_Lemma();
b1,B',comp,APA',SAT' := is_unsat?(Sigma1,B',APA,Inv,n+1,SAT);
if b1 {
      var curContextSet := negatedSet(Sigma[1..],s); 
	  var prevContextSets := if Sigma[0].AUsel? || Sigma[0].EUsel? || Sigma[0].AU? || Sigma[0].EU?
	                         then And2Sets(Sigma[0].f1) 
							 else {{T}};
	  var newContextSet := composeContextSets(prevContextSets, curContextSet);
	  var newContextFor := setset2OrderedAndOr(newContextSet);
	  var sigma' := if Sigma[0].AUsel? || Sigma[0].EUsel? || Sigma[0].AU? || Sigma[0].EU?
		            then compose_U(newContextFor,Sigma[0].f2,s)
					else compose_U(newContextFor,Sigma[0].f,s);
      var Sigma2;
	  if Sigma[0].EUsel?  || Sigma[0].EU? {
	     Sigma2 := insert(EX(sigma'),insert(Sigma[0].f1,Sigma[1..]));
		 B':= add_seq_to_last_stage(B,[EX(sigma'),Sigma[0].f1]);}
	  else if Sigma[0].AUsel? || Sigma[0].AU? {
		 Sigma2 := insert(AX(sigma'),insert(Sigma[0].f1,Sigma[1..]));
		 B':= add_seq_to_last_stage(B,[AX(sigma'),Sigma[0].f1]); }
	  else if Sigma[0].AF? {
	     Sigma2 := insert(AX(sigma'),Sigma[1..]);
		 B' := add_formula_to_last_stage(B,AX(sigma'));}
	  else { Sigma2 := insert(EX(sigma'),Sigma[1..]);
	         B':= add_formula_to_last_stage(B,EX(sigma'));}
	  insert_preserves_order_Lemma();
	  b2,B',comp,APA',SAT' := is_unsat?(Sigma2,B',APA',Inv,n+1,SAT');  
	  b := b2;
      }
else { 
	  b := false; 
     }	
}

// Implementation of the Next-State Rule

predicate method is_V?(sigma:NNF_Formula) {
sigma.V?
}

method apply_Next_State (Sigma:seq<NNF_Formula>,B:Branch,APA: set<seq<NNF_Formula>>,Inv:seq<NNF_Formula>,n:nat,SAT: set<seq<NNF_Formula>>) 
                returns(b:bool,B':Branch,comp:int,APA': set<seq<NNF_Formula>>,SAT': set<seq<NNF_Formula>>)
requires is_ordered(Sigma) && is_ordered(Inv);
requires Sigma != []
requires B != []
requires is_elementary(Sigma)
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
decreases *
{
if exists p :: p in SAT  && subseq_ord(Sigma,p) {
	     b:= false;  B' := B;  APA' := APA; SAT' := SAT;
		 }
else { var children := go_next(Sigma,Inv);
	   var cleanChildren:seq<seq<NNF_Formula>>, k := [],0;
	   while  k < |children|
		    invariant 0 <= k <= |children|
			invariant |cleanChildren| == k
		    invariant forall i :: 0 <= i < k ==> is_ordered(cleanChildren[i])
		     {
			 var cleanchildk := clean_child(children[k]);
			 cleanChildren := cleanChildren + [cleanchildk];
			 k := k+1;
			 }
		if  exists Phi1,Phi2 :: Phi1 in cleanChildren && Phi2 in APA && subseq_ord(Phi2,Phi1)
			{
			b := true;
			B' := B;
			APA' := APA;
			SAT' := SAT;
			}
		else { b := false;
			  var i := 0;
			  var bi,compi;
			  APA' := APA; 
			  SAT' := SAT;
			  while !b && i <= |cleanChildren|-1 
					{
					B' := B + [[]];
					B' := add_seq_to_last_stage(B',cleanChildren[i]);
					var childreni_seq := merge(cleanChildren[i],Inv);
					merge_Lemma(cleanChildren[i],Inv);
                    bi,B',compi,APA',SAT' := is_unsat_child?(childreni_seq,B',APA',Inv,n+1,SAT');
					if bi { 
						   b := true;
						   APA' := APA' + {cleanChildren[i]};
						   }					
					i := i+1;
					}
			  B' := B;
		  	  if !b {
					SAT' := SAT' + {Sigma};
					}
			}
	}
}
}