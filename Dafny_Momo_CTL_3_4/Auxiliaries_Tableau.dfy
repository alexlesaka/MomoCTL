include "Parsing_CTL_to_NNF_Sequents.dfy"

module Auxiliaries_Tableau {
    import opened Parsing_CTL_to_NNF_Sequents

// MINIMALITY OF ELEMENTARY FORMULAE

predicate method is_next(phi:NNF_Formula) {
phi.AX? || phi.EX?
}

predicate method is_elementary(Sigma:seq<NNF_Formula>) {
forall sigma :: sigma in Sigma ==> (is_literal(sigma) || is_next(sigma))
}

lemma minimality_of_elementary_Lemma (Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma) && Sigma != [] 
requires is_literal(Sigma[0])  || is_next(Sigma[0]);
ensures is_elementary(Sigma);
{}

// Handling contradictions

predicate method is_Ctd(Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
{
exists phi:: phi in Sigma && 
     (  in_ord(neg_in_nnf(phi),Sigma)
		|| //the following is required by the subsumption 
		   //of eventualities by their contextualised variants
		   //and AR(sigma1,sigma2), AG(~sigma1) ==> AG(sigma2)
		   //Otherwise, contradiction should be checked in the stage,
		   //where subsumed formulas are present, instead of in Sigma
        ((phi.AUsel? || phi.AU?) && ( in_ord(EG(neg_in_nnf(phi.f2)),Sigma)
		                               ||
						              in_ord(AG(neg_in_nnf(phi.f2)),Sigma)) )
		||
		((phi.EUsel? || phi.EU?) && in_ord(AG(neg_in_nnf(phi.f2)),Sigma))
		||
		(phi.AX? && (phi.f.AUsel? || phi.f.AU?)
		         && (in_ord(EX(EG(neg_in_nnf(phi.f.f2))),Sigma) || 
					 in_ord(EG(neg_in_nnf(phi.f.f2)),Sigma) ))
		||
		(phi.EX? && (phi.f.EUsel? || phi.f.EU?)
		         && ( in_ord(AX(AG(neg_in_nnf(phi.f.f2))),Sigma) || 
					  in_ord(AG(neg_in_nnf(phi.f.f2)),Sigma)  ))
		|| 
        (phi.AR? && in_ord(AG(neg_in_nnf(phi.f2)),Sigma) )
	    || //The following are logical contradictions added to gain efficiency
		(phi.AF? && phi.f.And? && (EG(neg_in_nnf(phi.f.f1)) in Sigma ||EG(neg_in_nnf(phi.f.f2)) in Sigma))
	)
}

// Handling branches and cycles

type Branch = seq<seq<NNF_Formula>>
// A branch is a sequence of stages 
//(each stage is the collection of all formulas that appears between two elementary nodes,
// including the formulas that are susbsumed in nodes, otherwise cycles are not well detected.)
// We omit the initial formulas AG, called Invariants

method add_formula_to_last_stage(B:Branch,sigma:NNF_Formula) returns (B':Branch)
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
requires B != []
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
ensures B' != []
{
var aux := insert_in_place(sigma,B[|B|-1]);
insert_in_place_Lemma(sigma,B[|B|-1]); 
B' := B[|B|-1 := aux];
}

method add_seq_to_last_stage(B:Branch,Sigma:seq<NNF_Formula>) returns (B':Branch)
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
requires B != []
ensures forall k :: 0 <= k < |B'| ==> is_ordered(B'[k])
ensures B' != []
decreases Sigma
{
if Sigma == [] {return B;}
else {
     B' := add_formula_to_last_stage(B,Sigma[0]);
	 B' := add_seq_to_last_stage(B',Sigma[1..]);
     }
}

method is_subset(Sigma1:seq<NNF_Formula>,Sigma2:seq<NNF_Formula>) returns (subset:bool)
//requires is_ordered(Sigma1) && is_ordered(Sigma2)
//subset == True <=> Sigma1 is a subset of Sigma2
{
var k1,k2 := 0,0;
subset := true;
while subset && k1 < |Sigma1| && k2 < |Sigma2|
    invariant 0 <= k1 <= |Sigma1| && k2 <= |Sigma2|
	decreases |Sigma2|-k2, |Sigma1|-k1
   {
   if Sigma1[k1] == Sigma2[k2] 
      { k1 := k1 + 1; k2:= k2 + 1; }
   else if !leq_in_Seq(Sigma1[k1],Sigma2[k2]) 
           { if k2 < |Sigma2| {k2:= k2 + 1;} else {subset := false; } }
   else {subset := false; k1 := |Sigma1|; k2 := |Sigma2|;}
   }
if k1 < |Sigma1| && k2 == |Sigma2| {subset := false;}
}

method iterativeRemoveInv(Sigma:seq<NNF_Formula>,Inv:seq<NNF_Formula>) returns (Sigma':seq<NNF_Formula>)
//requires is_ordered(Sigma) 
//ensures is_ordered(Sigma') 
{
var k := 0;
while k < |Sigma| && family(Sigma[k]) > 6
     invariant k <= |Sigma|
     { k := k+1; }
if (k < |Sigma| && family(Sigma[k]) <= 3) || k ==  |Sigma|  { Sigma' := Sigma; }
else { 
     //assert k < |Sigma|  &&  4 <= family(Sigma[k]) <= 6;
     Sigma' := Sigma[..k];
	 ordered_Lemma(Sigma');
     while k < |Sigma| && family(Sigma[k]) >= 4
	     //invariant is_ordered(Sigma') 
	     {
		 if (Sigma[k].AG? && Sigma[k] !in Inv) 
		 || (Sigma[k].AX? && (!Sigma[k].f.AG? || Sigma[k].f !in Inv)) 
		 || Sigma[k].EX?
		     { 
			 Sigma' := Sigma'+[Sigma[k]]; 
			 }
		 k := k+1;
		 }
	 if k < |Sigma| { //assert family(Sigma[k]) <= 3;
	                Sigma' := Sigma' + Sigma[k..];
					}   
     }
}


method min_stage (B:Branch,node:seq<NNF_Formula>,Inv:seq<NNF_Formula>) returns (comp:int)
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
requires is_ordered(node)
requires B != []
ensures -1 <= comp < |B| 
{
comp := -1;
var node' := iterativeRemoveInv(node,Inv);
var subset := false;
while comp < |B|-1 && !subset
	{
	comp := comp+1;
	subset := is_subset(node',B[comp]);
	}
if comp < |B|-1 {return comp;} else { return -1; }
}

// Handling Eventuality Selection and Eventuality-covered

//////////////////////////////
predicate method there_is_not_selected_Ev_in(Sigma:seq<NNF_Formula>) {
(forall i :: (0 <= i < |Sigma| && (Sigma[i].AX? || Sigma[i].EX?))
			  ==> (!Sigma[i].f.AUsel? && !Sigma[i].f.EUsel?))
}

predicate method is_unfullfiled_in (sigma:NNF_Formula,B:Branch,comp:int) 
requires 0 <= comp < |B| && is_non_selected_Ev(sigma)
{
match sigma
   case AU(alpha,beta) => forall i :: comp <= i < |B| ==>  beta !in B[i]
   case EU(alpha,beta) => (forall i :: comp <= i < |B|-1 ==>  EX(sigma) in B[i] && beta !in B[i])
                           && beta !in B[|B|-1]
   case AF(alpha) => forall i :: comp <= i < |B| ==>  alpha !in B[i]
   case EF(alpha) => (forall i :: comp <= i < |B|-1 ==>  EX(sigma) in B[i] && alpha !in B[i])
                           && alpha !in B[|B|-1]
}

method is_Ev_covered_cycle(Sigma:seq<NNF_Formula>,B:Branch,comp:nat) returns (ev_index:int)
requires 0 <= comp < |B| 
requires is_ordered(Sigma)
requires forall k :: 0 <= k < |B| ==> is_ordered(B[k])
ensures ev_index < |Sigma|
ensures ev_index >= 0 ==> (is_Ev(Sigma[ev_index]) && is_non_selected_Ev(Sigma[ev_index]))
{
if exists i :: 0 <= i < |Sigma| && is_non_selected_Ev(Sigma[i]) && is_unfullfiled_in(Sigma[i],B,comp)
   { var i :| 0 <= i < |Sigma| && is_non_selected_Ev(Sigma[i]) && is_unfullfiled_in(Sigma[i],B,comp); 
     return i;}
else {
	 return -1;
     }
}

function method to_selected(sigma:NNF_Formula):NNF_Formula
requires is_Ev(sigma)
{
match sigma
   case AU(alpha,beta) => AUsel(alpha,beta)
   case EU(alpha,beta) => EUsel(alpha,beta)
   case AF(alpha) => AUsel(T,alpha)
   case EF(alpha) => EUsel(T,alpha)
   // The following cases are really only to avoid matching problems, in practique will be no used at all
   // The proof that an unfulfilled eventuality inside a loop cannot be a selected one is far from trivial
   case AUsel(alpha,beta) => AUsel(alpha,beta)
   case EUsel(alpha,beta) => EUsel(alpha,beta)
}

function method to_unselected(sigma:NNF_Formula):NNF_Formula
requires is_selected_Ev(sigma)
{
match sigma
   case AUsel(alpha,beta) => AU(alpha,beta)
   case EUsel(alpha,beta) => EU(alpha,beta)
}


// Handling Context for Beta+ Rules (with Subsumption)

function method And2Sets (sigma:NNF_Formula):(SS:set<set<NNF_Formula>>)
ensures forall S:: S in SS ==> S != {} 
{
if sigma.And? then And2Sets(sigma.f1) + And2Sets(sigma.f2) 
else if sigma.Or? then {Or2Set(sigma)}
else {{sigma}}
}

function method Or2Set (sigma:NNF_Formula):(S:set<NNF_Formula>)
ensures S !={}
{
if sigma.Or? then Or2Set(sigma.f1) + Or2Set(sigma.f2)
else {sigma}
}

predicate method is_AXiAG(sigma:NNF_Formula)
{
sigma.AG? || (sigma.AX? && is_AXiAG(sigma.f))
}

/*
predicate method is_exists(sigma: NNF_Formula) {
sigma.EX? ||sigma.EG? || sigma.ER? || sigma.EF?  || sigma.EU? || sigma.EUsel?
}
*/

predicate method is_excluded(sigma:NNF_Formula)
{
is_AXiAG(sigma) 
}

function method negatedSet (Sigma:seq<NNF_Formula>,s:string): (N:set<NNF_Formula>)
requires s != []
requires is_ordered(Sigma)
{
(set sigma | sigma in Sigma && !is_excluded(sigma) :: neg_in_nnf(sigma))
}

method addContextWithSubsmption (previous:set<set<NNF_Formula>>,current:set<NNF_Formula>) 
       returns (newC:set<set<NNF_Formula>>)
requires current != {} && forall S:: S in previous ==> S != {} 
ensures forall S:: S in newC ==> S != {} 
{
var negated_current := set phi | phi in current :: neg_in_nnf(phi);
if exists Phi :: Phi in previous && Phi <= negated_current { newC := {};}
else if current in previous { newC := previous; }
else {
		var c := previous;
		var currentSubsumed := false;
		var subsumedByCurrent:set<set<NNF_Formula>> := {};
		while c != {} && !currentSubsumed
		    decreases c
			{
			var picked :| picked in c;
			if picked <= current { currentSubsumed := true; }
			else if picked > current 
			        { subsumedByCurrent := subsumedByCurrent + {picked}; }
			c := c - {picked};
			}
		if currentSubsumed { newC := previous; }
		else { newC := (previous-subsumedByCurrent) + {current}; }
     }
}

method composeContextSets(previous:set<set<NNF_Formula>>,current:set<NNF_Formula>) 
                 returns (newC: set<set<NNF_Formula>>)
requires forall S:: S in previous ==> S != {} 
ensures forall S:: S in newC ==> S != {} 
{
if current == {} || previous == {{F}} {  return {{F}}; }
else if previous == {{T}} { return {current}; }
else { newC := addContextWithSubsmption(previous,current); }
}

method set2OrdSeq (S:set<NNF_Formula>) returns (Seq:seq<NNF_Formula>)
//ensures is_ordered(Seq)
{
if S == {} {Seq := [];}
else if |S| == 1 { var sigma :| sigma in S; Seq := [sigma]; }
else {
     var aux := S; 
     var sigma1 :| sigma1 in aux;
	 aux := aux - {sigma1};
	 var Seq' := set2OrdSeq(aux);
	 Seq := insert(sigma1,Seq');
	}
}

method ordSeq2Or(Seq:seq<NNF_Formula>) returns (sigma:NNF_Formula)
{
if Seq == []  { sigma := F; }
else if Seq[0] == T { sigma := T; }
else if Seq[0] == F { sigma := ordSeq2Or(Seq[1..]);}
else if |Seq| == 1 { sigma := Seq[0]; }
else { 
	  var sigma' := ordSeq2Or(Seq[1..]);
	  sigma := Or(Seq[0],sigma');	
      }
}

method ordSeq2And(Seq:seq<NNF_Formula>) returns (sigma:NNF_Formula)
{
if Seq == []  { sigma := T; }
else if Seq[0] == F { sigma := F; }
else if Seq[0] == T { sigma := ordSeq2And(Seq[1..]);}
else if |Seq| == 1 { sigma := Seq[0]; }
else { 
	  var sigma' := ordSeq2And(Seq[1..]);
	  sigma := And(Seq[0],sigma');	
      }
}

// substituye a setset2AndOr
method setset2OrderedAndOr(context:set<set<NNF_Formula>>) returns (sigma:NNF_Formula)
{
if context == {} { return F;} 
else {
     var aux := context; 
	 var SetSeq: set<NNF_Formula> := {};
	 while aux != {}
	    {
        var S1 :| S1 in aux;
	    aux := aux - {S1};
		var Seq1 := set2OrdSeq(S1);
		var phi1 := ordSeq2Or(Seq1); 
		SetSeq := SetSeq + {phi1};
		}
	 var OrdSeq := set2OrdSeq(SetSeq);
	 sigma := ordSeq2And(OrdSeq);
     }

}


////////////////////////////////
function method compose_U (sigma1:NNF_Formula,sigma2:NNF_Formula,s:string):(sigma: NNF_Formula)
requires s != []
{
if s[0] == 'E' then  EUsel(sigma1,sigma2) else AUsel(sigma1,sigma2)
}

// For the Next-State Rule

function method nextDelete(Sigma:seq<NNF_Formula>):(Sigma':seq<NNF_Formula>)
requires is_ordered(Sigma)
requires forall sigma :: sigma in Sigma ==> is_next(sigma)
{
if Sigma == [] then [] 
else assert Sigma[0] in Sigma;
     //assert (Sigma[0].AX? || Sigma[0].EX?);
     insert(Sigma[0].f,nextDelete(Sigma[1..]))
}

lemma nextDelete_Lemma(Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
requires forall sigma :: sigma in Sigma ==> is_next(sigma)
ensures is_ordered(nextDelete(Sigma))
{
if Sigma != [] { 
    assert is_next(Sigma[0]);
	}
insert_preserves_order_Lemma();
}

function method subSeq (Sigma:seq<NNF_Formula>, p:NNF_Formula -> bool): (Sigma':seq<NNF_Formula>)
requires is_ordered(Sigma)
{
if Sigma == [] then []
else if p(Sigma[0])
	    then [Sigma[0]] + subSeq(Sigma[1..],p)
	    else subSeq(Sigma[1..],p)
}

lemma SubSeq_Lemma(Sigma:seq<NNF_Formula>, p:NNF_Formula -> bool)
requires is_ordered(Sigma)
ensures forall sigma :: sigma in subSeq(Sigma,p) ==> (sigma in Sigma && p(sigma))
ensures is_ordered(subSeq(Sigma,p))
{
if Sigma != [] { 
   SubSeq_Lemma(Sigma[1..],p);
	//assert is_ordered(subSeq(Sigma[1..],p)); //I.H.
   if subSeq(Sigma[1..],p) != []  {
		//assert Sigma[0] in Sigma;
		assert subSeq(Sigma[1..],p)[0] in Sigma[1..];
		assert subSeq(Sigma[1..],p)[0] in Sigma;
		var i :| 1 <= i < |Sigma| && Sigma[i] == subSeq(Sigma[1..],p)[0];
		ordered_Lemma(Sigma);
		//assert forall i, j :: 0 <= i < j < |Sigma| ==> leq_in_Seq(Sigma[i], Sigma[j]);
		//assert leq_in_Seq(Sigma[0],Sigma[i]);
	}}
}

function method combineAE(A:seq<NNF_Formula>,E:seq<NNF_Formula>):seq<seq<NNF_Formula>>
requires is_ordered(A)
requires is_ordered(E)
{ 
if E == [] then [A]
else if |E| == 1 then [insert(E[0],A)]
else [insert(E[0],A)] + combineAE(A,E[1..])
}

lemma combineAE_Lemma(A:seq<NNF_Formula>,E:seq<NNF_Formula>)
requires is_ordered(A)
requires is_ordered(E)
ensures forall S :: S in combineAE(A,E)  ==> is_ordered(S)
{
if E != [] {
   combineAE_Lemma(A,E[1..]);
   insert_preserves_order_Lemma(); }
}

predicate method isAX(phi:NNF_Formula) {
phi.AX?
}

predicate method isEX(phi:NNF_Formula) {
phi.EX?
}

method go_next(Sigma:seq<NNF_Formula>,Inv:seq<NNF_Formula>) returns (seqSeq:seq<seq<NNF_Formula>>)
requires is_ordered(Sigma)
ensures forall S :: S in seqSeq  ==> is_ordered(S)
{
	var As := subSeq(Sigma, sigma => (isAX(sigma) && sigma.f !in Inv));
SubSeq_Lemma(Sigma, sigma => (isAX(sigma) && sigma.f !in Inv));
	var seqA := nextDelete(As);
nextDelete_Lemma(As);
    var Es := subSeq(Sigma, sigma => isEX(sigma));
SubSeq_Lemma(Sigma, sigma => isEX(sigma));
    var seqE := nextDelete(Es);
nextDelete_Lemma(Es);
combineAE_Lemma(seqA,seqE);
seqSeq := combineAE(seqA,seqE);
}

//Cleaning contexts of Next-children
method index_selected_Ev_to_clean(Sigma:seq<NNF_Formula>) returns (index:int)
requires is_ordered(Sigma)
ensures -1 <= index < |Sigma|
ensures index != -1 ==> 14 <= family(Sigma[index]) <= 15 
{
var i := 0;
while i < |Sigma| && family(Sigma[i]) > 15 
    invariant 0 <= i <= |Sigma|
    invariant i < |Sigma| ==> forall j :: 0 <= j < i ==> family(Sigma[j]) > 15
   {
    i := i+1;	   
   }
if i == |Sigma| { index := -1; }
else if 14 <= family(Sigma[i]) <= 15 
     { index := i; }
else { index := -1; }
}

function method seq2NegSet (s:seq<NNF_Formula>):set<NNF_Formula>
{
if s == [] then {}
else {neg_in_nnf(s[0])}	+ seq2NegSet(s[1..])
}

method clean_context(SS:set<set<NNF_Formula>>,tail_no_inv:seq<NNF_Formula>) 
       returns (SS':set<set<NNF_Formula>>)
{
SS' := {};
var auxSS := SS;
while auxSS != {}
   decreases |auxSS|
  {
  var S :| S in auxSS;
  var S' := S - seq2NegSet(tail_no_inv);
  //if exists phi :: phi in S' && phi.AF? && phi.f.And? && EG(neg_in_nnf(phi.f.f1)) in tail_no_inv  { S' := {};}
  if S' == {} { auxSS := {}; SS' := {};}
         else {SS' := SS'+ {S'}; auxSS := auxSS - {S};}
  }
}

method clean_child (child:seq<NNF_Formula>) returns (cleaned_child:seq<NNF_Formula>)
requires is_ordered(child)
ensures is_ordered(cleaned_child)
{
var index := index_selected_Ev_to_clean(child);
if index == -1 { cleaned_child := child; }
else {
	 var newf1 := clean_context(And2Sets(child[index].f1),child[1..]);
	 var newContextFor := setset2OrderedAndOr(newf1);
	 var s := if child[index].AUsel? then "A" else "E";
	 var Sigma0' :=  compose_U(newContextFor,child[index].f2,s);
	 cleaned_child := insert(Sigma0',child[..index]+child[index+1..]);
	 subseq_ordered_Lemma(child,index);
	 //assert is_ordered(child[..index]+child[index+1..]);
	 insert_Lemma(Sigma0',child[..index]+child[index+1..]);
	}
}

// OR subsumption and cleaning

predicate method is_subsumed_Or(or_formula:NNF_Formula, tail_sequent:seq<NNF_Formula>)
{ 
var S:set<NNF_Formula>  := Or2Set(or_formula);
exists i :: 0 <= i < |tail_sequent| && Or2Set(tail_sequent[i]) <= S
}

function method Or2Seq (sigma:NNF_Formula):seq<NNF_Formula>
{
if sigma.Or? then Or2Seq(sigma.f1) + Or2Seq(sigma.f2)
else [sigma]
}

function method Seq2Or(S:seq<NNF_Formula>):NNF_Formula
requires S != []
{
if |S| == 1 then S[0]
else Or(S[0],Seq2Or(S[1..])) 
}

method clean_Or(or_formula:NNF_Formula, tail_sequent:seq<NNF_Formula>) returns (newOr:NNF_Formula)
{
var S:seq<NNF_Formula> := Or2Seq(or_formula); 
var i := 0;
var S' := [];
while i < |S|
   {
    if neg_in_nnf(S[i]) !in tail_sequent  { S' := S' + [S[i]]; }
	i := i+1;
   }
if S' == [] { newOr := F; }
else { newOr := Seq2Or(S');}
}

// Datatypes for construction of models and proofs

datatype Model = EmptyM | LeafM(i:int) | NodeM(At:seq<NNF_Formula>,Seq:seq<Model>)

datatype Proof = EmptyP | LeafP(string,seq<NNF_Formula>) | NodeP(string,Seq:seq<NNF_Formula>,seq<Proof>)

}