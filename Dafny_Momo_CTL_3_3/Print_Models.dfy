include "Parsing_CTL_to_NNF_Sequents.dfy"
include "Auxiliaries_Tableau.dfy"

module Print_Models {
	import opened Parsing_CTL_to_NNF_Sequents
	import opened Auxiliaries_Tableau

// CLEANING AND PRINTING MODELS

predicate method is_subModel  (M1:Model,M2:Model)
{
if M1.LeafM? then M2.LeafM? && M1.i == M2.i
else M1.NodeM? && M2.NodeM? && M1.At == M2.At && 
     forall M :: M in M1.Seq ==> exists M' :: M' in M2.Seq && is_subModel(M,M')
}

method cleanModel (M:Model) returns (M':Model)
{
match M
case EmptyM => {}
case LeafM(i) => {
     return M;}
case NodeM(A,SM) => { 
     var i := 0;
	 var SM' := [];
	 while i < |SM| 
	      {
		  var SMi := cleanModel(SM[i]);
		  SM' := SM' + [SMi];
		  i := i+1;
		  }
     SM' := cleanSeqModels(SM');
     return NodeM(A,SM');}
}

method cleanSeqModels (SM:seq<Model>) returns (SM':seq<Model>)
{
if SM == [] { return [];}
else { SM' := cleanSeqModels(SM[1..]);
       if exists j :: 0 < j < |SM| && is_subModel(SM[0],SM[j]) { return SM'; }
       else { return [SM[0]]+ SM'; }
	 }
}

method printIndentM(n:nat)
{
print "\n";
var i := n;
while i > 0 
    {
	print "-";
	i := i - 1;
	}
}

method printSequentAtoms(E:seq<NNF_Formula>)
{
var i := 0;
if |E| == 0 { print ""; }
else if |E| == 1 {if E[i].V? { print E[i].prop;} }
else {if E[i].V? { print E[i].prop; print ", "; printSequentAtoms(E[1..]);} }
}

method printModelR(M:Model,state:nat,n:nat)
{
match M
case EmptyM => { }
case LeafM(comp) => { 
     if comp == -1 { printIndentM(n); print "State "; print state; print ":{}"; 
					  print " --> cycle to State "; print state;}
     else { 
		   //printModelR(cycle,state+1,n+3);
		   print " --> cycle to State "; print comp; } 
		   }
case NodeM(E,S) => {
     printIndentM(n); print "State "; print state; print ": {"; printSequentAtoms(E); print "}";
	 if S == [] { printIndentM(n); print "Empty Sequence of Models";}
	 else { var i:= 0;
            while i < |S| 
				{ 
				if  |S| > 1 { 
					printIndentM(n); print "Subtree "; 
					print i+1; 
					//print "(/#"; print |S|; print ") ";
					print " of State "; print state; }
				printModelR(S[i],state+1,n+3); 
				i:=i+1; 
				}}}
}


method printModel(M:Model)
{
printModelR(M,0,0);
}
     
}