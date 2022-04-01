include "Parsing_CTL_to_NNF_Sequents.dfy"
include "Auxiliaries_Tableau.dfy"
include "Print_Models.dfy"

module Print_Proofs {
	import opened Parsing_CTL_to_NNF_Sequents
	import opened Auxiliaries_Tableau
	import opened Print_Models

// PRINTING SMALL-STEP PROOFS (WITHOUT INPUT INVARIANTS IN NODES)

method printSequent(Sigma:seq<NNF_Formula>)
{
if Sigma == [] { print ""; }
else if |Sigma| == 1
     {
	  print toString(Sigma[0]);
	  }
else {
	  print toString(Sigma[0]); print ", ";
	  printSequent(Sigma[1..]);
	  }
}

method printIndentP(n:nat,k:nat)
{
print "\n";
var i := n;
while i > 0 
    {
	print "-";
	i := i - 1;
	}
print k; print ".";
}

method lengthProof(P:Proof) returns (lg:nat)
{
match P
	case EmptyP => {return 0;}
	case LeafP(s,Sigma)  => {return 1;}
	case NodeP(s,Sigma,children) => {
		 if |children| == 1 { 
			 var lg0 := lengthProof(children[0]); 
			 return 1 + lg0;
			 }
		 else if |children| == 2 {
		        var lg0 := lengthProof(children[0]);
				var lg1 := lengthProof(children[1]);
				return 1 + lg0 + lg1;         
				 }
		     else {return 0;}
	}
}

method depthProofGET(P:Proof,n:nat) returns (is_GET:bool)
requires n >= 2;
{
match P
	case EmptyP => return false;
	case LeafP(s,Sigma)  => return false;
	case NodeP(s,Sigma,children) => 
		 if |children| == 1 && n > 2 { 
			 is_GET:= depthProofGET(children[0],n-1);
			 }
		 else if |children| == 2 && n > 2 {
		        var aux_is_GET := depthProofGET(children[0],n-1);
				if !aux_is_GET { is_GET:= depthProofGET(children[1],n-1); }
				else { return true; }        
				 }
		else {is_GET := true;}
}

method printSequentUptoInv(Sigma:seq<NNF_Formula>,Inv:seq<NNF_Formula>,s:string) 
{
var Sigma' := iterativeRemoveInv(Sigma,Inv);
if Sigma != [] && Sigma[0] in Inv { 
       print "{"; printSequent(Sigma'); print "},  apply ("; print s; print ") to Inv: ";
	   if Sigma != [] {print toString(Sigma[0]);} }
else { print "{"; printSequent(Sigma'); print "},  apply ("; print s; print ")"; }
}

method printProofNoInvR(P:Proof,Inv:seq<NNF_Formula>,n:nat,k:nat) 
{
match P
case EmptyP => {}
case LeafP(s,Sigma) => {
     var Sigma' := iterativeRemoveInv(Sigma,Inv);
     printIndentP(n,k); print "{"; printSequent(Sigma'); print "}, ";
	 if s == "F" { print " by (F)";} 
	 else if s == "Ctd" { print " by (Ctd)";} 
	 else //if s == "APA" 
	      { print " (As Proved Above)";}
	 }
case NodeP(s,Sigma,children) => {
	printIndentP(n,k); printSequentUptoInv(Sigma,Inv,s);
	if |children| == 1 { printProofNoInvR(children[0],Inv,n+1,k+1);} 
	else if |children| == 2 {
         printProofNoInvR(children[0],Inv,n+1,k+1);
		 var lg := lengthProof(children[0]);
			printProofNoInvR(children[1],Inv,n+1,k+lg+1); 
	     }
	else {print "\n ill-constructed proof";}
    }
}

method printProofNoInv(P:Proof,Inv:seq<NNF_Formula>)
{
printProofNoInvR(P,Inv,0,0);
}

// PRINTING BIGSTEP PROOFS

method printBigStepProofR(P:Proof,Inv:seq<NNF_Formula>,n:nat,k:nat) 
{
match P
case EmptyP => {}
case LeafP(s,Sigma) => {}
case NodeP(s,Sigma,children) => {
	if s == "Next-state" { 
		    if |children| == 1 { 
			        var Sigma' := iterativeRemoveInv(Sigma,Inv);
					printIndentP(n,k); print "{"; printSequent(Sigma'); print "}"; 
					printBigStepProofR(children[0],Inv,n+1,k+1);
	            }
			else {print "\n ill-constructed proof";} 
	}
	else if |children| == 1 { printBigStepProofR(children[0],Inv,n+1,k+1);}
    else if |children| == 2 { 
			printBigStepProofR(children[0],Inv,n+1,k+1);
			var lg := lengthProof(children[0]);
			printBigStepProofR(children[1],Inv,n+1,k+lg+1); 
			}
	else {print "\n ill-constructed proof";}
	}
}

method printBigStepProof(P:Proof,Inv:seq<NNF_Formula>) 
{
printBigStepProofR(P,Inv,0,0);
}

// AUXILIARY PRINTING METHODS

method printBranch(B:Branch)
{
if |B| == 0 { print "empty Branch";}
else{
	var i := 0;
	while i <= |B|-1
			{
			var stagei:= B[i];
            //var S := {};
			print "\nState "; 
			print i;
			print " : {";
			if stagei == [] { print "}";}
			else {
			      printSequent(B[i]);
			      }
			i:= i+1;
			}
   }
}
lemma minimum_exists_Lemma (S:set<NNF_Formula>)
requires S != {}
ensures exists phi :: phi in S && forall psi :: psi in S ==> leq_NNF_Formula(phi,psi)
{
var phi :| phi in S;
if S == {phi} {// the mimimum of a singleton set is its only element
				forall psi | psi in S
				ensures leq_NNF_Formula(phi,psi);
				{ 
				//assert psi == phi;
				if !leq_NNF_Formula(phi,psi) { reflexive_NNF_Formula_Lemma(phi,psi); } 
				}
               } 
else if forall psi :: psi in S ==> leq_NNF_Formula(phi,psi) 
     { // we happened to pick the minimum of S
     } 
else {
     //assert exists sigma :: sigma in S && !leq_NNF_Formula(phi,sigma);
     //var sigma :| sigma in S && !leq_NNF_Formula(phi,sigma);
     var S' := S - {phi};
     minimum_exists_Lemma(S');
     var sigma' :| sigma' in S' && forall psi :: psi in S' ==> leq_NNF_Formula(sigma',psi);
    // the minimum of S' is the same as the miminum of S
     forall psi | psi in S
     ensures leq_NNF_Formula(sigma',psi)
		{
		if
		case psi in S' => //assert leq_NNF_Formula(sigma',psi);  
		case psi == phi =>
				var beta :| beta in S && !leq_NNF_Formula(phi, beta);  
				reflexive_NNF_Formula_Lemma(phi,beta);
				assert beta != phi;
				assert beta in S';  
				//assert leq_NNF_Formula(sigma',beta);
				//assert !leq_NNF_Formula(psi,beta);
				total_leq_NNF_Formula_Lemma(psi,beta);
				//assert leq_NNF_Formula(beta,psi);
				transitive_leq_NNF_Formula_Lemma(sigma',beta,psi);
				//assert leq_NNF_Formula(sigma',psi);
		}
  }
}

method printSet(S:set<NNF_Formula>)
{
if S == {} { print "{}"; }
else {
     if |S| == 1 { var phi :| phi in S; print(toString(phi));}
	 else { 
	      minimum_exists_Lemma(S);
          var phi :| phi in S && forall psi :: (psi in S && psi != phi) ==> leq_NNF_Formula(phi,psi);
	      print(toString(phi)); print ",";
		  var S' := S - {phi};
		  printSet(S');
		  }
     }
}

method printSetSeq(SS:set<seq<NNF_Formula>>)
{
if SS == {} { print "{}"; }
else {
     if |SS| == 1 { var S :| S in SS; print "{"; printSequent(S); print "}"; }
	 else { 
	      var S :| S in SS;
          print "{"; printSequent(S); print "},";
		  var SS' := SS - {S};
		  printSetSeq(SS');
		  }
     }
}

method printSetSeqP(SS:set<(seq<NNF_Formula>,Model)>)
{
if SS == {} { print "{}"; }
else {
     if |SS| == 1 { var S :| S in SS; print "("; printSequent(S.0); printModel(S.1); print ")"; }
	 else { 
	      var S :| S in SS;
          print "("; printSequent(S.0); printModel(S.1); print "),\n";
		  var SS' := SS - {S};
		  printSetSeqP(SS');
		  }
     }
}

method printSetSet(SS:set<set<NNF_Formula>>)
{
if SS == {} { print "{}"; }
else {
     if |SS| == 1 { var S :| S in SS; print "{"; printSet(S); print "}"; }
	 else { 
	      var S :| S in SS;
          print "{"; printSet(S); print "},";
		  var SS' := SS - {S};
		  printSetSet(SS');
		  }
     }
}
 
}