module Parsing_CTL_to_NNF_Sequents {
	
datatype CTL_Formula =   False
                       | True
					   | Var(prop:string) 
					   | Neg(f:CTL_Formula) 
					   | eX(f:CTL_Formula) 
					   | aX(f:CTL_Formula) 
	                   | eG(f:CTL_Formula) 
					   | aG(f:CTL_Formula) 
					   | eF(f:CTL_Formula)  
					   | aF(f:CTL_Formula) 
					   | eU(f1:CTL_Formula,f2:CTL_Formula) 
					   | aU(f1:CTL_Formula,f2:CTL_Formula) 
					   | eR(f1:CTL_Formula,f2:CTL_Formula) 
					   | aR(f1:CTL_Formula,f2:CTL_Formula) 
					   | Conj(f1:CTL_Formula,f2:CTL_Formula)
					   | Disj(f1:CTL_Formula,f2:CTL_Formula)
					   | Imp(f1:CTL_Formula,f2:CTL_Formula)
					   | Iff(f1:CTL_Formula,f2:CTL_Formula)	  

datatype NNF_Formula =   F 
                       | T
					   | V(prop:string) 
					   | NegV(prop:string) 
					   | EX(f:NNF_Formula) 
					   | AX(f:NNF_Formula) 
	                   | EG(f:NNF_Formula) 
					   | AG(f:NNF_Formula) 
					   | ER(f1:NNF_Formula,f2:NNF_Formula) 
					   | AR(f1:NNF_Formula,f2:NNF_Formula) 
					   | EF(f:NNF_Formula)  
					   | AF(f:NNF_Formula) 
					   | EU(f1:NNF_Formula,f2:NNF_Formula) 
					   | AU(f1:NNF_Formula,f2:NNF_Formula) 
					   | EUsel(f1:NNF_Formula,f2:NNF_Formula) 
					   | AUsel(f1:NNF_Formula,f2:NNF_Formula) 
					   | Or(f1:NNF_Formula,f2:NNF_Formula)
					   | And(f1:NNF_Formula,f2:NNF_Formula) 

function method family(alpha: NNF_Formula): nat {
  match alpha
  case F => 0
  case T => 1
  case V(_) => 2
  case NegV(_) => 3
  case AX(_) => 4
  case EX(_) => 5
  case AG(_) => 6
  case EG(_) => 7
  case AR(_, _) => 8
  case ER(_, _) => 9
  case AF(_) => 10
  case EF(_) => 11
  case AU(_, _) => 12
  case EU(_, _) => 13
  case AUsel(_, _) => 14
  case EUsel(_, _) => 15
  case Or(_, _) => 16
  case And(_, _) => 17
}

function method to_nnf(phi: CTL_Formula): NNF_Formula
decreases numberImp(phi), negDepth(phi)
{
if phi == False then F
else if phi == True then T
else if phi.Var? then V(phi.prop)
else if phi. Neg? then 
	 match phi.f
		case False => T
		case True => F
		case Var(p) =>  NegV(p)
		case Neg(alpha) => assert numberImp(phi) == numberImp(alpha);
		                   assert negDepth(phi) > negDepth(alpha);
						   to_nnf(alpha)
		case eX(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AX(to_nnf(Neg(alpha)))
		case aX(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EX(to_nnf(Neg(alpha)))
		case eG(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AF(to_nnf(Neg(alpha)))
		case aG(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EF(to_nnf(Neg(alpha)))
		case eF(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AG(to_nnf(Neg(alpha)))
		case aF(alpha) => assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EG(to_nnf(Neg(alpha)))
		case eR(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
                               assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       AU(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
		case aR(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       EU(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
		case eU(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       AR(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
		case aU(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       ER(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
		case Imp(alpha,beta) => assert numberImp(phi) > numberImp(alpha) + numberImp(Neg(beta));
		                        And(to_nnf(alpha),to_nnf(Neg(beta)))
		case Iff(alpha,beta) => assert numberImp(phi) > numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                        Or(And(to_nnf(alpha),to_nnf(Neg(beta))),And(to_nnf(beta),to_nnf(Neg(alpha))))
		case Conj(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                         assert negDepth(phi) > negDepth(Neg(alpha));
								 assert negDepth(phi) > negDepth(Neg(beta));
		                         Or(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
		case Disj(alpha,beta) => assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                         assert negDepth(phi) > negDepth(Neg(alpha));
								 assert negDepth(phi) > negDepth(Neg(beta));
		                         And(to_nnf(Neg(alpha)),to_nnf(Neg(beta)))
else if phi.eX? then EX(to_nnf(phi.f))
else if phi.aX? then AX(to_nnf(phi.f))
else if phi.eG? then EG(to_nnf(phi.f))
else if phi.aG? then AG(to_nnf(phi.f))
else if phi.eF? then EF(to_nnf(phi.f))
else if phi.aF? then AF(to_nnf(phi.f))
else if phi.eR? then ER(to_nnf(phi.f1),to_nnf(phi.f2))
else if phi.aR? then AR(to_nnf(phi.f1),to_nnf(phi.f2))
else if phi.eU? then EU(to_nnf(phi.f1),to_nnf(phi.f2))
else if phi.aU? then AU(to_nnf(phi.f1),to_nnf(phi.f2))
else if phi.Imp? then Or(to_nnf(Neg(phi.f1)),to_nnf(phi.f2))
else if phi.Iff? then Or(And(to_nnf(phi.f1),to_nnf(phi.f2)),And(to_nnf(Neg(phi.f1)),to_nnf(Neg(phi.f2))))
else if phi.Conj? then And(to_nnf(phi.f1),to_nnf(phi.f2))
else Or(to_nnf(phi.f1),to_nnf(phi.f2))
}

//Auxiliaries to prove termination of to_nnf

function numberImp (phi: CTL_Formula): nat {
if phi.Imp? then 1 + numberImp(phi.f1) + numberImp(phi.f2)
else if phi.Iff? then 2 + numberImp(phi.f1) + numberImp(phi.f2)
else if phi == False ||  phi == True || phi.Var? then 0
else if  phi.Neg? || phi.eX? || phi.aX? || phi.eG? || phi.aG? || phi.eF? || phi.aF? then numberImp(phi.f)
else numberImp(phi.f1) + numberImp(phi.f2)
}

function negDepth (phi: CTL_Formula): nat {
if phi == False ||  phi == True || phi.Var? then 0
else if phi.Neg? || phi.eX? || phi.aX? || phi.eG? || phi.aG? || phi.eF? || phi.aF? then 1 + negDepth(phi.f)
else 1 + negDepth(phi.f1) + negDepth(phi.f2)
}


// Negation in NNF

function method neg_in_nnf(sigma:NNF_Formula):NNF_Formula
{
match sigma
case F => T
case T => F
case V(p) => NegV(p)
case NegV(p) => V(p)
case And(phi,psi) => Or(neg_in_nnf(phi),neg_in_nnf(psi)) 
case Or(phi,psi) => And(neg_in_nnf(phi),neg_in_nnf(psi)) 
case EX(phi) => AX(neg_in_nnf(phi))
case AX(phi) => EX(neg_in_nnf(phi))
case EG(phi) => AF(neg_in_nnf(phi)) 
case AG(phi) => EF(neg_in_nnf(phi))
case EF(phi) => AG(neg_in_nnf(phi)) 
case AF(phi) => EG(neg_in_nnf(phi))
case EU(phi,psi) => AR(neg_in_nnf(phi),neg_in_nnf(psi)) 
case AU(phi,psi) => ER(neg_in_nnf(phi),neg_in_nnf(psi)) 
case ER(phi,psi) => AU(neg_in_nnf(phi),neg_in_nnf(psi)) 
case AR(phi,psi) => EU(neg_in_nnf(phi),neg_in_nnf(psi)) 
case EUsel(phi,psi) => AR(neg_in_nnf(phi),neg_in_nnf(psi)) 
case AUsel(phi,psi) => ER(neg_in_nnf(phi),neg_in_nnf(psi))
}

// TOKENIZER FOR GORE BENCHMARS

datatype Token = TokBinOp(op:string)
               | TokUnaOp(op:string)
               | TokLParen
               | TokRParen
               | TokAtom(atom:string)
			   | TokConstant(constant:string)
               | TokError

predicate method digit(c:char)
{
'0' <= c <= '9'
}

predicate method letter(c:char)
{
('A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_' || c == '\u0027')
}

function method takeLetterDigit(s:string):(string,string)
ensures |takeLetterDigit(s).1| <= |s|
{
if s == [] || (!letter(s[0]) && !digit(s[0])) then ([],s)
else var (s1,s2) := takeLetterDigit(s[1..]);
     ([s[0]]+s1,s2)
}

datatype Option<A> = Some(some: A) | None

method tokenize(s:string) returns (st: seq<Token>)
{
st := [];
var s' := s;
while s' != [] 
    decreases |s'|
    {
	if s'[0] == '(' { st := st + [TokLParen]; s' := s'[1..]; }
    else if s'[0] == ')' { st := st + [TokRParen]; s' := s'[1..]; }
    else if s'[0] == ' ' { s' := s'[1..]; }
    else if s'[0] in ['|','&','U','B'] { st := st + [TokBinOp([s'[0]])]; s' := s'[1..]; }
	else if s'[0] == '~' { st := st + [TokUnaOp([s'[0]])]; s' := s'[1..]; }
	else if |s'| > 1 && s'[..2] == "=>" { st := st + [TokBinOp(s'[..2])]; s' := s'[2..]; }
	else if |s'| > 1 && s'[..2] in ["EX","AX","EF","AF","EG","AG"] { st := st + [TokUnaOp(s'[..2])]; s' := s'[2..]; }
    else if |s'| > 2 && s'[..3] == "<=>" { st := st + [TokBinOp(s'[..3])]; s' := s'[3..]; }
	else if |s'| > 3 && s'[..4] == "True" { st := st + [TokConstant(s'[..4])]; s' := s'[4..]; }
	else if |s'| > 4 && s'[..5] == "False" { st := st + [TokConstant(s'[..5])]; s' := s'[5..]; }
	//This two cases should be here, otherwise unary operators AX, EX, ... are wrongly tokenized
	else if s'[0] in ['A','E'] { st := st + [TokUnaOp([s'[0]])]; s' := s'[1..]; }
	else if letter(s'[0]) { 
	        var (v,rest) := takeLetterDigit(s'[1..]);
			st := st + [TokAtom([s'[0]]+v)];
			assert |rest| <= |s'[1..]|;
			s' := rest;}
	else { print "Input is not a CTL Formula"; s' := [];}						  
	}
}

// PARSER string-Goré to CTL Formula

method parse (s:string) returns (phi:CTL_Formula)
{
var st := tokenize(s);
var form_st := form_iff(st);
if form_st.None? 
   || form_st.some.1 != [] 
     {print "Input is not a CTL_Formula";}
else {return form_st.some.0;}
}

function method lookAhead(st:seq<Token>):Token {
if st == [] then TokError else st[0]
}

function method accept(st:seq<Token>):Option<seq<Token>>
ensures accept(st).Some? ==> |accept(st).some| < |st|
{
if st == [] then None else Some(st[1..])
}

function method form_iff(st:seq<Token>):Option<(CTL_Formula,seq<Token>)>
decreases |st|,4
ensures form_iff(st).Some? ==> |form_iff(st).some.1| < |st|
{
var option1 := form_imp(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead(st');
	 if t.TokBinOp? && t.op == "<=>" 
	 then var a := accept(st');
	      if a.None? then None
		  else //assert |a.some| < |st'| <= |st|;
		       var option2 := form_iff(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                          Some((Iff(f1,f2),st''))
			   else None
	else option1
}

function method form_imp(st:seq<Token>):Option<(CTL_Formula,seq<Token>)>
decreases |st|, 3
ensures form_imp(st).Some? ==> |form_imp(st).some.1| < |st|
{
var option1 := form_or(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead(st');
	 if t.TokBinOp? && t.op == "=>" 
	 then var a := accept(st');
	      if a.None? then None
		  else var option2 := form_imp(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                         Some((Imp(f1,f2),st''))
			   else None
	else option1
}

function method form_or(st:seq<Token>):Option<(CTL_Formula,seq<Token>)>
decreases |st|, 2
ensures form_or(st).Some? ==> |form_or(st).some.1| < |st|
{
var option1 := form_and(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead(st');
	 if t.TokBinOp? && t.op == "|" 
	 then var a := accept(st');
	      if a.None? then None
		  else var option2 := form_or(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                         Some((Disj(f1,f2),st''))
			   else None
	else option1
}

function method form_and(st:seq<Token>):Option<(CTL_Formula,seq<Token>)>
decreases |st|, 1
ensures form_and(st).Some? ==> |form_and(st).some.1| < |st|
{
var option1 := form_rest(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead(st');
	 if t.TokBinOp? && t.op == "&" 
	 then var a := accept(st');
	      if a.None? then None
		  else var option2 := form_and(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                         Some((Conj(f1,f2),st''))
			   else None
	else option1
}

function method form_rest(st:seq<Token>):Option<(CTL_Formula,seq<Token>)>
decreases |st|, 0
ensures form_rest(st).Some? ==> |form_rest(st).some.1| < |st|
{
var t:= lookAhead(st);
if t.TokUnaOp? then
   var a := accept(st);
   if a.None? then None
   else if t.op == "EX" then var option := form_rest(a.some);
		                         if option.None? then None
	                             else var (f,st'):= option.some;
							          Some((eX(f),st'))
		else if t.op == "AX" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
							           Some((aX(f),st'))
		else if t.op == "EF" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((eF(f),st'))
		else if t.op == "AF" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								  Some((aF(f),st'))
		else if t.op == "EG" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((eG(f),st'))
		else if t.op == "AG" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((aG(f),st'))
		else if t.op == "~" then var option := form_rest(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((Neg(f),st'))
		else if t.op == "A" then var option := EorA(a.some);
								 if option.None? then None
								 else var (isU, f1, f2,st') := option.some;
									 if isU then Some((aU(f1,f2),st')) else Some((aR(f1,Neg(f2)),st')) 
		else if t.op == "E" then var option := EorA(a.some);
								 if option.None? then None
							     else var (isU, f1, f2,st') := option.some;
								    if isU then Some((eU(f1,f2),st')) else Some((eR(f1,Neg(f2)),st'))
		else None
else if t.TokLParen? then 
        var a := accept(st);
        if a.None? then None
        else //assert |a.some| < |st| ;
			 var option := form_iff(a.some);
			 if option.None? then None
			 else var (f,st') := option.some;
				  var t' := lookAhead(st');
				  if t'.TokRParen? then var a':= accept(st');
				                        if a'.None? then None else Some((f,a'.some))
				  else None
else if t.TokConstant? then 
        var a := accept(st);
        if a.None? then None
        else if t.constant == "True" then Some((True,a.some)) else Some((False,a.some))
else if t.TokAtom? then 
        var a := accept(st);
        if a.None? then None else Some((Var(t.atom),a.some))
else None                                     
}

function method EorA(st:seq<Token>):Option<(bool,CTL_Formula,CTL_Formula,seq<Token>)>
decreases |st|, 0
ensures EorA(st).Some? ==> |EorA(st).some.3| < |st|
{
var t:= lookAhead(st);
if t.TokLParen?  
then var a := accept(st);
     var option1 := form_iff(a.some);
     if option1.None? || !a.Some? then None
	 else var (f1,st') := option1.some;
		  var t':= lookAhead(st');
		  if t'.TokBinOp? && (t'.op == "U" || t'.op == "B") 
			    then var a':= accept(st');
				     if a'.None? then None
					 else var option2 := form_iff(a'.some);
					      if option2.None? then None
		                  else var (f2,st'') := option2.some;
						       var t'':= lookAhead(st'');
							   if t''.TokRParen? 
							   then var a'':= accept(st'');
							        if t'.op == "U" then Some((true,f1,f2,a''.some)) 
								                    else Some((false,f1,f2,a''.some))
							   else None
		 else None
else None
}

//  PARSER FOR NNF

method tokenizeNNF(s:string) returns (st: seq<Token>)
{
st := [];
var s' := s;
while s' != [] 
    decreases |s'|
    {
	if s'[0] == '(' { st := st + [TokLParen]; s' := s'[1..]; }
    else if s'[0] == ')' { st := st + [TokRParen]; s' := s'[1..]; }
    else if s'[0] == ' ' { s' := s'[1..]; }
    else if s'[0] in ['|','&','U','R'] { st := st + [TokBinOp([s'[0]])]; s' := s'[1..]; } 
	else if s'[0] == '~' { st := st + [TokUnaOp([s'[0]])]; s' := s'[1..]; }
	else if |s'| > 1 && s'[..2] == "=>" { st := st + [TokBinOp(s'[..2])]; s' := s'[2..]; }
	else if |s'| > 1 && s'[..2] in ["EX","AX","EF","AF","EG","AG"] { st := st + [TokUnaOp(s'[..2])]; s' := s'[2..]; }
    else if |s'| > 2 && s'[..3] == "<=>" { st := st + [TokBinOp(s'[..3])]; s' := s'[3..]; }
	else if |s'| > 3 && s'[..4] == "true" { st := st + [TokConstant(s'[..4])]; s' := s'[4..]; }
	else if |s'| > 4 && s'[..5] == "false" { st := st + [TokConstant(s'[..5])]; s' := s'[5..]; }
	//This two cases should be here, otherwise unary operators AX, EX, ... are wrongly tokenized
	else if s'[0] in ['A','E'] { st := st + [TokUnaOp([s'[0]])]; s' := s'[1..]; }
	else if letter(s'[0]) { 
	        var (v,rest) := takeLetterDigit(s'[1..]);
			st := st + [TokAtom([s'[0]]+v)];
			assert |rest| <= |s'[1..]|;
			s' := rest;}
	else { print "Input is not an NNF Formula"; s' := [];}						  
	}
}

// PARSER string-CTL-Formula to NNF Formula

method parseNNF (s:string) returns (phi:NNF_Formula)
{
var st := tokenizeNNF(s);
var form_st := form_or_NNF(st);
if form_st.None? 
   || form_st.some.1 != [] 
     {print "Input is not an NNF_Formula";}
else {return form_st.some.0;}
}

function method lookAhead_NNF(st:seq<Token>):Token {
if st == [] then TokError else st[0]
}

function method accept_NNF(st:seq<Token>):Option<seq<Token>>
ensures accept(st).Some? ==> |accept(st).some| < |st|
{
if st == [] then None else Some(st[1..])
}

function method form_or_NNF(st:seq<Token>):Option<(NNF_Formula,seq<Token>)>
decreases |st|, 2
ensures form_or_NNF(st).Some? ==> |form_or_NNF(st).some.1| < |st|
{
var option1 := form_and_NNF(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead_NNF(st');
	 if t.TokBinOp? && t.op == "|" 
	 then var a := accept_NNF(st');
	      if a.None? then None
		  else var option2 := form_or_NNF(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                             Some((Or(f1,f2),st''))
			   else None
	else option1
}

function method form_and_NNF(st:seq<Token>):Option<(NNF_Formula,seq<Token>)>
decreases |st|, 1
ensures form_and_NNF(st).Some? ==> |form_and_NNF(st).some.1| < |st|
{
var option1 := form_rest_NNF(st);
if option1.None? then None
else var (f1,st'):= option1.some;
	 var t := lookAhead_NNF(st');
	 if t.TokBinOp? && t.op == "&" 
	 then var a := accept_NNF(st');
	      if a.None? then None
		  else var option2 := form_and_NNF(a.some);
		       if option2.Some? then var (f2,st''):= option2.some;
		                         Some((And(f1,f2),st''))
			   else None
	else option1
}

function method form_rest_NNF(st:seq<Token>):Option<(NNF_Formula,seq<Token>)>
decreases |st|, 0
ensures form_rest_NNF(st).Some? ==> |form_rest_NNF(st).some.1| < |st|
{
var t:= lookAhead_NNF(st);
if t.TokUnaOp? then
   var a := accept_NNF(st);
   if a.None? then None
   else if t.op == "EX" then var option := form_rest_NNF(a.some);
		                         if option.None? then None
	                             else var (f,st'):= option.some;
							          Some((EX(f),st'))
		else if t.op == "AX" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
							           Some((AX(f),st'))
		else if t.op == "EF" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((EF(f),st'))
		else if t.op == "AF" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								  Some((AF(f),st'))
		else if t.op == "EG" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((EG(f),st'))
		else if t.op == "AG" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								       Some((AG(f),st'))
		else if t.op == "~" then var option := form_rest_NNF(a.some);
		                          if option.None? then None
	                              else var (f,st'):= option.some;
								    if f.V? then  Some((NegV(f.prop),st')) else None
		else if t.op == "A" then var option := EorA_NNF(a.some);
								 if option.None? then None
								 else var (isU, f1, f2,st') := option.some;
									  if isU then Some((AU(f1,f2),st')) else Some((AR(f1,f2),st'))
		else if t.op == "E" then var option := EorA_NNF(a.some);
								 if option.None? then None
							     else var (isU, f1, f2,st') := option.some;
								      if isU then Some((EU(f1,f2),st')) else Some((ER(f1,f2),st'))
		else None
else if t.TokLParen? then 
        var a := accept_NNF(st);
        if a.None? then None
        else //assert |a.some| < |st| ;
			 var option := form_or_NNF(a.some);
			 if option.None? then None
			 else var (f,st') := option.some;
				  var t' := lookAhead_NNF(st');
				  if t'.TokRParen? then var a':= accept_NNF(st');
				                        if a'.None? then None else Some((f,a'.some))
				  else None
else if t.TokConstant? then 
        var a := accept_NNF(st);
        if a.None? then None
        else if t.constant == "true" then Some((T,a.some)) else Some((F,a.some))
else if t.TokAtom? then 
        var a := accept_NNF(st);
        if a.None? then None else Some((V(t.atom),a.some))
else None                                     
}

//[Token.TokUnaOp(A), Token.TokLParen, Token.TokAtom(i), Token.TokBinOp(U), Token.TokAtom(a0), Token.TokRParen]

function method EorA_NNF(st:seq<Token>):Option<(bool,NNF_Formula,NNF_Formula,seq<Token>)>
decreases |st|, 0
ensures EorA_NNF(st).Some? ==> |EorA_NNF(st).some.3| < |st|
{
var t:= lookAhead_NNF(st);
if t.TokLParen?  
then var a := accept_NNF(st);
     var option1 := form_or_NNF(a.some);
     if option1.None? || !a.Some? then None
	 else var (f1,st') := option1.some;
		  var t':= lookAhead_NNF(st');
		  if t'.TokBinOp? && (t'.op == "U" || t'.op == "R") 
			    then var a':= accept_NNF(st');
				     if a'.None? then None
					 else var option2 := form_or_NNF(a'.some);
					      if option2.None? then None 
		                  else var (f2,st'') := option2.some;
						       var t'':= lookAhead_NNF(st'');
							   if t''.TokRParen? 
							   then var a'':= accept_NNF(st'');
							        if t'.op == "U" then Some((true,f1,f2,a''.some)) 
								                    else //assert t'.op == "R";
													     Some((false,f1,f2,a''.some))
							   else None
		 else None 
else None
}

// ORDER IN NNF FORMULAS

//String Ordering
predicate method leq_string(s1:string,s2:string) { 
s1 == "" || (s2 != "" && s1[0] <= s2[0] && ( s1[0] == s2[0] ==> leq_string(s1[1..],s2[1..])))
}

lemma antisym_leq_string_Lemma (s1:string, s2:string)
requires leq_string(s1,s2)  && leq_string(s2,s1) 
ensures s1 == s2
{
if s1 != "" && s2 != "" { antisym_leq_string_Lemma(s1[1..],s2[1..]); }
}

lemma transitive_leq_string_Lemma(s1:string, s2:string, s3:string)
requires leq_string(s1,s2)  && leq_string(s2,s3) 
ensures leq_string(s1,s3)
{
if s1 != "" && s2 != "" && s3 != "" { 
if leq_string(s1[1..],s2[1..])  && leq_string(s2[1..],s3[1..]) {
transitive_leq_string_Lemma(s1[1..],s2[1..],s3[1..]); 
}}
}

lemma total_leq_string_Lemma(s1:string, s2:string)
ensures leq_string(s1,s2)  || leq_string(s2,s1) 
{}

//NNF-Formulas Ordering
predicate method leq_NNF_Formula (alpha:NNF_Formula, beta:NNF_Formula)
{
if family(alpha) < family(beta) then true
else if family(alpha) > family(beta) then false
else if family(alpha) <= 1 then true
else if 2 <= family(alpha) <= 3 then leq_string(alpha.prop,beta.prop) 
else if 4 <= family(alpha) <= 7 || 10 <= family(alpha) <= 11 then leq_NNF_Formula(alpha.f,beta.f) 
else leq_NNF_Formula(alpha.f1,beta.f1) && (alpha.f1 == beta.f1 ==> leq_NNF_Formula(alpha.f2,beta.f2)) 
}

lemma antisym_leq_NNF_Formula_Lemma (alpha:NNF_Formula, beta:NNF_Formula)
requires leq_NNF_Formula(alpha,beta)  && leq_NNF_Formula(beta,alpha)
ensures alpha == beta
{
if alpha.V? || alpha.NegV? { if beta.V? || beta.NegV? {antisym_leq_string_Lemma(alpha.prop,beta.prop); }}
}

lemma total_leq_NNF_Formula_Lemma (alpha:NNF_Formula, beta:NNF_Formula)
ensures leq_NNF_Formula(alpha,beta) || leq_NNF_Formula(beta, alpha) 
{
if !leq_NNF_Formula(alpha,beta) && !leq_NNF_Formula(beta, alpha)  {
	if alpha.V? || alpha.NegV? { total_leq_string_Lemma(alpha.prop,beta.prop);}	
	}
}

lemma transitive_leq_NNF_Formula_Lemma (alpha:NNF_Formula, beta:NNF_Formula, gamma:NNF_Formula)
requires leq_NNF_Formula(alpha,beta)  && leq_NNF_Formula(beta,gamma)
ensures leq_NNF_Formula(alpha,gamma) 
{
if !leq_NNF_Formula(alpha,gamma) {
	if (alpha.V? && beta.V? && gamma.V?) || (alpha.NegV? && beta.NegV? && gamma.NegV?) { 
	   transitive_leq_string_Lemma(alpha.prop,beta.prop,gamma.prop); }
	else if (4 <= family(alpha) == family(beta) == family(gamma) <= 7)
	        || (10 <= family(alpha) == family(beta) == family(gamma) <= 11) {
	   transitive_leq_NNF_Formula_Lemma (alpha.f,beta.f,gamma.f); }
	 else if (8 <= family(alpha) == family(beta) == family(gamma) <= 9)
	        || (12 <= family(alpha) == family(beta) == family(gamma) <= 17) {
	   if !leq_NNF_Formula(alpha.f1,gamma.f1)  { transitive_leq_NNF_Formula_Lemma (alpha.f1,beta.f1,gamma.f1);}
			else { antisym_leq_NNF_Formula_Lemma (alpha.f1,beta.f1);
				   transitive_leq_NNF_Formula_Lemma (alpha.f2,beta.f2,gamma.f2);} } }
}

lemma reflexive_NNF_Formula_Lemma(alpha:NNF_Formula,beta:NNF_Formula)
requires !leq_NNF_Formula(alpha,beta)
ensures  alpha != beta
{
total_leq_NNF_Formula_Lemma(alpha,beta);
//assert leq_NNF_Formula(beta,alpha);
}

lemma reflexive_leq_NNF_Formula_Lemma()
ensures  forall alpha, beta :: alpha == beta ==> leq_NNF_Formula(alpha,beta) 
{
forall alpha, beta | alpha == beta ensures leq_NNF_Formula(alpha,beta) 
  { if !leq_NNF_Formula(alpha,beta) { reflexive_NNF_Formula_Lemma(alpha,beta); } }
}

// CONSTRUCTION OF ORDERED SEQUENTS (SEQUENCES OF FORMULAS) 
// WITH NO-REPS AND EVENTUALITIES SUBSUMPTION

predicate method pure_prop(phi:NNF_Formula)
{
(phi == F ||  phi == T || phi.V? || phi.NegV?) 
||
((phi.Or? || phi.And?) && pure_prop(phi.f1) && pure_prop(phi.f2))
}

function method literals (phi:NNF_Formula):nat
requires pure_prop(phi)
{
if phi == F ||  phi == T || phi.V? || phi.NegV? then 1
else literals(phi.f1) + literals(phi.f2)
}

predicate method is_literal(phi:NNF_Formula)
{
phi == F ||  phi == T || phi.V? || phi.NegV?	
}

predicate method is_unary(phi:NNF_Formula)
{
phi.AX? || phi.EX? || phi.AG? || phi.EG? || phi.AF? || phi.EF? 
}

predicate method is_binary(phi:NNF_Formula)
{
phi.AR? || phi.ER? || phi.AU? || phi.EU? || phi.AUsel? || phi.EUsel? || phi.Or? || phi.And? 
}

/*
predicate method leq_in_Seq(alpha:NNF_Formula,beta:NNF_Formula)
{
(family(alpha) > family(beta)) 
|| 
(family(alpha) == family(beta) && 
    (
	(is_literal(alpha) && leq_NNF_Formula(alpha, beta))
	||
	(is_unary(alpha) && 
	     (
		 (pure_prop(alpha.f) &&
		   (!pure_prop(beta.f) 
		     || 
			(pure_prop(beta.f) &&  
			    (literals(alpha.f) < literals(beta.f) 
		         || 
		        (literals(alpha.f)==literals(beta.f) && leq_NNF_Formula(alpha, beta))))
			))
		 ||
		 leq_NNF_Formula(alpha,beta)
	     ) 
	)
	||
	(is_binary(alpha) && 
	     ((
		  pure_prop(alpha.f1) && pure_prop(alpha.f2) &&
		     (
				(!pure_prop(beta.f1) || !pure_prop(beta.f2))
				|| 
				(
				pure_prop(beta.f1) && pure_prop(beta.f2) && 
					(
					literals(alpha.f1)+literals(alpha.f2) < literals(beta.f1)+literals(beta.f2)
						|| 
					(literals(alpha.f1)+literals(alpha.f2) == literals(beta.f1)+literals(beta.f2)
						&&
						leq_NNF_Formula(alpha,beta))
					)
				)
			 )
		 )
		 ||
		 leq_NNF_Formula(alpha, beta) 
	    ))
	)
)
}
*/

predicate method leq_in_Seq(alpha:NNF_Formula,beta:NNF_Formula)
{
if family(alpha) > family(beta) then true
else if family(alpha) == family(beta) then 
	if is_literal(alpha) then leq_NNF_Formula(alpha,beta)
	else if is_unary(alpha) then 
			if pure_prop(alpha.f) then
				if !pure_prop(beta.f) then true
				else literals(alpha.f) < literals(beta.f) 
						|| 
					(literals(alpha.f)==literals(beta.f) && leq_NNF_Formula(alpha,beta))
			else if pure_prop(beta.f) then false
			else leq_NNF_Formula(alpha,beta)
	else //assert is_binary(alpha);
		if pure_prop(alpha.f1) && pure_prop(alpha.f2) then
				if !pure_prop(beta.f1) || !pure_prop(beta.f2) then true
				else literals(alpha.f1)+literals(alpha.f2) < literals(beta.f1)+literals(beta.f2)
						|| 
					(literals(alpha.f1)+literals(alpha.f2) == literals(beta.f1)+literals(beta.f2) 
					&& leq_NNF_Formula(alpha,beta) )
		else if pure_prop(beta.f1) && pure_prop(beta.f2) then false
		else leq_NNF_Formula(alpha,beta)
else false
}


lemma total_leq_in_Seq_Lemma()
ensures forall alpha,beta :: (leq_in_Seq(alpha,beta) || leq_in_Seq(beta, alpha))
{
forall alpha, beta {total_leq_NNF_Formula_Lemma(alpha,beta);}	
}

lemma antisym_leq_in_Seq_Lemma() 
ensures forall alpha,beta :: (leq_in_Seq(alpha,beta)  && leq_in_Seq(beta,alpha)) ==> alpha == beta
{
forall alpha,beta | leq_in_Seq(alpha,beta)  && leq_in_Seq(beta,alpha)
	ensures alpha == beta 
	{ 
		if leq_NNF_Formula(alpha,beta)  && leq_NNF_Formula(beta,alpha)
			{antisym_leq_NNF_Formula_Lemma(alpha,beta);}
	}
}

lemma transitive_leq_in_Seq_Lemma() //(alpha:NNF_Formula, beta:NNF_Formula, gamma:NNF_Formula)
//requires leq_in_Seq(alpha,beta)  && leq_in_Seq(beta,gamma)
ensures forall alpha,beta,gamma :: (leq_in_Seq(alpha,beta)  && leq_in_Seq(beta,gamma)) ==> leq_in_Seq(alpha,gamma) 
{
forall alpha,beta,gamma | leq_in_Seq(alpha,beta)  && leq_in_Seq(beta,gamma)
	ensures leq_in_Seq(alpha,gamma)
	{
	if !leq_in_Seq(alpha,gamma) {
		if family(alpha) == family(beta) == family(gamma) {
			transitive_leq_NNF_Formula_Lemma (alpha,beta,gamma);	
			assert false;
	}}}
}

lemma reflexive_leq_in_Seq_Lemma()
ensures  forall alpha, beta :: alpha == beta ==> leq_in_Seq(alpha,beta) 
{
reflexive_leq_NNF_Formula_Lemma();
}

predicate method is_ordered (Sigma:seq<NNF_Formula>)
{
|Sigma| > 1 ==> (leq_in_Seq(Sigma[0],Sigma[1]) && Sigma[0] != Sigma[1] && is_ordered(Sigma[1..]) )
}

lemma orderedL_Lemma (Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
ensures forall i, j :: 0 <= i < j < |Sigma| ==> (leq_in_Seq(Sigma[i],Sigma[j]) && Sigma[i] != Sigma[j])
{
if |Sigma| > 1  
	{ 
	//assert leq_in_Seq(Sigma[0],Sigma[1]);
	//assert Sigma[0] != Sigma[1];
	orderedL_Lemma(Sigma[1..]);
	//assert forall i, j :: 0 <= i < j < |Sigma[1..]| ==> (leq_in_Seq(Sigma[1..][i], Sigma[1..][j]) && Sigma[1..][i] != Sigma[1..][j]); //I.H.
	//assert forall i, j :: 1 <= i < j < |Sigma| ==> (leq_in_Seq(Sigma[i], Sigma[j]) && Sigma[i] != Sigma[j]); //I.H.
	//assume forall j :: 1 <= j < |Sigma| ==> (leq_in_Seq(Sigma[0], Sigma[j]) && Sigma[0] != Sigma[j]); //
	if exists j :: 1 <= j < |Sigma| && (!leq_in_Seq(Sigma[0], Sigma[j]) || Sigma[0] == Sigma[j])
	   { 
	   var j :| 1 <= j < |Sigma| && (!leq_in_Seq(Sigma[0], Sigma[j]) || Sigma[0] == Sigma[j]);
	   if !leq_in_Seq(Sigma[0], Sigma[j]) {
				total_leq_in_Seq_Lemma();
				//assert leq_in_Seq(Sigma[j], Sigma[0]);
				transitive_leq_in_Seq_Lemma();
				//assert leq_in_Seq(Sigma[j], Sigma[1]);
				//assert Sigma[j] == Sigma[1];
				//assert false;
				}
		else {
			 //assert Sigma[j] == Sigma[0]  && j >1;
			 //assert leq_in_Seq(Sigma[j],Sigma[1]);
			 antisym_leq_in_Seq_Lemma();
			 //assert Sigma[j] == Sigma[1];
			 //assert false;
			 }
		}			
	}
}


lemma orderedR_Lemma(Sigma:seq<NNF_Formula>)
requires forall i, j :: 0 <= i < j < |Sigma| ==> (leq_in_Seq(Sigma[i],Sigma[j]) && Sigma[i] != Sigma[j])
ensures is_ordered(Sigma)
{}

lemma ordered_Lemma(Sigma:seq<NNF_Formula>)
ensures is_ordered(Sigma) <==> (forall i, j :: 0 <= i < j < |Sigma| ==> (leq_in_Seq(Sigma[i],Sigma[j]) && Sigma[i] != Sigma[j]))
{
if is_ordered(Sigma)  {orderedL_Lemma(Sigma);}
if forall i, j :: 0 <= i < j < |Sigma| ==> (leq_in_Seq(Sigma[i],Sigma[j]) && Sigma[i] != Sigma[j]) 
                      {orderedR_Lemma(Sigma);}
}

lemma subseq_ordered_Lemma(Sigma:seq<NNF_Formula>,j:nat)
requires j < |Sigma| && is_ordered(Sigma)
ensures is_ordered(Sigma[..j]+Sigma[j+1..])
{
ordered_Lemma(Sigma);
ordered_Lemma(Sigma[..j]+Sigma[j+1..]);
}

//Ordered Subsequence of an ordered sequence

predicate method subseq_ord (Sigma:seq<NNF_Formula>,Sigma':seq<NNF_Formula>)
//requires is_ordered(Sigma) && is_ordered(Sigma')
{
if Sigma == [] then true
else if Sigma' == [] then false
else if Sigma[0] == Sigma'[0] then subseq_ord(Sigma[1..],Sigma'[1..])
else if leq_in_Seq(Sigma'[0],Sigma[0]) then subseq_ord(Sigma,Sigma'[1..])
else //assert !leq_in_Seq(Sigma'[0],Sigma[0]);
     false
}

// Search in an ordered sequence

predicate method in_ord (phi: NNF_Formula,Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma) 
{
if Sigma == [] then false
else if Sigma[0] == phi then true
else if leq_in_Seq(Sigma[0],phi) then in_ord(phi,Sigma[1..])
else //assert Sigma[0] != phi && !leq_in_Seq(Sigma[0],phi);
     false
}

//Merging ordered sequences

function method merge (s1:seq<NNF_Formula>, s2:seq<NNF_Formula>):seq<NNF_Formula>
requires is_ordered(s1) && is_ordered(s2)
decreases |s1|,|s2|
{
if s1 == [] then s2
else if s2 == [] then s1
else if s1[0] == s2[0] then [s1[0]] + merge(s1[1..],s2[1..])
else if leq_in_Seq(s1[0],s2[0]) then [s1[0]] + merge(s1[1..],s2)
else [s2[0]] + merge(s1,s2[1..])
}

lemma merge_Lemma(s1:seq<NNF_Formula>, s2:seq<NNF_Formula>)
requires is_ordered(s1) && is_ordered(s2)
ensures is_ordered(merge(s1,s2))
decreases |s1|,|s2|
{

if s1 != [] && s2 != [] && s1[0] != s2[0] {
	if leq_in_Seq(s1[0],s2[0]) {
		total_leq_in_Seq_Lemma();
		//assert leq_in_Seq(s2[0],s1[0]);
		merge_Lemma(s1[1..], s2);
	}
	else {
		total_leq_in_Seq_Lemma();
		assert leq_in_Seq(s2[0],s1[0]);
		merge_Lemma(s1, s2[1..]);
	}
}
}


// Insertion with subsumption in ordered Sequents of NNF_Formulas

predicate method is_selected_Ev(sigma:NNF_Formula) {
sigma.AUsel? || sigma.EUsel? }

predicate method is_non_selected_Ev(sigma:NNF_Formula) {
sigma.AU? || sigma.EU? || sigma.AF? || sigma.EF? }

predicate method is_Ev(sigma:NNF_Formula) {
is_selected_Ev(sigma) || is_non_selected_Ev(sigma) }

predicate method is_unary_Ev(sigma:NNF_Formula) {
sigma.AF? || sigma.EF? }

predicate method is_binary_Ev(sigma:NNF_Formula) {
sigma.AUsel? || sigma.EUsel? || sigma.AU? || sigma.EU? }

predicate method is_QUQF_i(sigma:NNF_Formula,phi:NNF_Formula) {
is_Ev(phi) && 
((is_unary_Ev(phi) && (phi.f == sigma || is_QUQF_i(sigma,phi.f)))
   ||
(is_binary_Ev(phi) && (phi.f2 == sigma || is_QUQF_i(sigma,phi.f2))))
}

predicate method is_left_stronger_EU(phi1:NNF_Formula,phi2:NNF_Formula) {
(phi1.EUsel? || phi1.EU?) && 
((phi2.EF? && (phi2.f == phi1.f2)) ||
 (phi2.EU? && (phi1.f2 == phi2.f2 && (phi2.f1 == T || (phi1.f1.And? && phi1.f1.f1 == phi2.f1)))))
}

predicate method is_left_stronger_AU(phi1:NNF_Formula,phi2:NNF_Formula) {
(phi1.AUsel? || phi1.AU?) && 
((phi2.AF? && (phi2.f == phi1.f2)) ||
 (phi2.AU? && (phi1.f2 == phi2.f2 && (phi2.f1 == T || (phi1.f1.And? && phi1.f1.f1 == phi2.f1)))))
}

predicate method is_next_step_variant(phi1:NNF_Formula,phi2:NNF_Formula) {
(phi1.EX? && (phi2.EF? || phi2.EU?) && is_left_stronger_EU(phi1.f,phi2))
||
(phi1.AX? && (phi2.AF? || phi2.AU?) && is_left_stronger_AU(phi1.f,phi2))
}

predicate method subsumes(phi1:NNF_Formula,phi2:NNF_Formula)
//phi1 subsumes phi2
{
is_next_step_variant(phi1,phi2)
||
is_QUQF_i(phi1,phi2)
||
is_left_stronger_EU(phi1,phi2)
||
is_left_stronger_AU(phi1,phi2)
|| //The following are included to gain efficiency
(phi1.AG? && phi2.AR? && phi1.f == phi2.f2)
|| 
(phi1.AX? && phi2.EX? && phi1.f == phi2.f)
||
(phi1.AF? && phi1.f.And? && phi2.AF? && phi2.f == phi1.f.f1)
||
(phi1.EG? && phi2.EG? && phi2.f.Or? && (phi1.f == phi2.f.f1 || phi1.f == phi2.f.f2))
}

function method subsume_all (phi:NNF_Formula, Sigma:seq<NNF_Formula>):(Sigma':seq<NNF_Formula>)
ensures |Sigma'| <= |Sigma|
{
if Sigma == [] then []
else if subsumes(phi,Sigma[0]) && neg_in_nnf(Sigma[0]) !in Sigma then  subsume_all(phi,Sigma[1..])
else [Sigma[0]] + subsume_all(phi,Sigma[1..])
}

lemma subsume_all_Lemma(phi:NNF_Formula,Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
ensures forall sigma:: sigma in subsume_all(phi,Sigma) ==> sigma in Sigma
ensures is_ordered(subsume_all(phi,Sigma))
{
if Sigma != [] && (!subsumes(phi,Sigma[0]) || neg_in_nnf(Sigma[0]) in Sigma)
    {
	subsume_all_Lemma(phi,Sigma[1..]);
	assert subsume_all(phi,Sigma[1..]) == [] || subsume_all(phi,Sigma[1..])[0] in Sigma[1..]; //by I.H.
	ordered_Lemma(Sigma);
	//assert is_ordered([Sigma[0]] + subsume_all(phi,Sigma[1..]));
	}
}  

predicate method is_subsumed(phi1:NNF_Formula,phi2:NNF_Formula)
{
subsumes(phi2,phi1)
}

predicate method is_subsumed_Ev (phi:NNF_Formula, Sigma:seq<NNF_Formula>)
{
exists j :: 0 <= j < |Sigma| && is_subsumed(phi,Sigma[j])
}

function method insert_in_place(phi:NNF_Formula,Sigma:seq<NNF_Formula>): (Sigma':seq<NNF_Formula>) 
//preserves order and prevent duplicates 
{
if phi == T then Sigma
else if Sigma == [] then [phi]
else if phi == Sigma[0] then Sigma
else if leq_in_Seq(phi,Sigma[0]) then [phi] + Sigma
else [Sigma[0]] + insert_in_place(phi, Sigma[1..])
}

lemma insert_in_place_Lemma(phi:NNF_Formula,Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
//ensures |insert_in_place(phi,Sigma)| >= 1
//        ==> (insert_in_place(phi,Sigma)[0] == phi || insert_in_place(phi,Sigma)[0] == Sigma[0])
ensures is_ordered(insert_in_place(phi,Sigma))
{
if phi != T  && Sigma != [] && phi != Sigma[0] && !leq_in_Seq(phi, Sigma[0]) 
   { 
	total_leq_in_Seq_Lemma();
	insert_in_place_Lemma(phi, Sigma[1..]);
   }
}

function method insert(phi:NNF_Formula,Sigma:seq<NNF_Formula>): (Sigma':seq<NNF_Formula>) 
// Inserts a formula phi in a sequent Sigma preserving the order, 
// preventing duplications (and addition of constant true), 
// and making (partial) subsumption of eventualities.
decreases |Sigma|
{
if phi == T then Sigma
else  var SubSigma := subsume_all(phi,Sigma);
      if !(exists psi :: psi in SubSigma && psi == neg_in_nnf(phi)) &&
		 //The formulas in the negated context, can be subsumed
		 //by the selected eventuality, preventing contradictions.
		 is_subsumed_Ev(phi, SubSigma) 
	  then SubSigma
      else insert_in_place(phi, SubSigma)
}

lemma insert_Lemma(phi:NNF_Formula,Sigma:seq<NNF_Formula>)
requires is_ordered(Sigma)
ensures is_ordered(insert(phi,Sigma))
decreases |Sigma|
{
if phi != T { 
     var SubSigma := subsume_all(phi,Sigma);
     subsume_all_Lemma(phi,Sigma);
     if !is_subsumed_Ev(phi, SubSigma) || 
	    exists psi :: psi in SubSigma && psi == neg_in_nnf(phi)
		{ insert_in_place_Lemma(phi,SubSigma);} }
}

lemma insert_preserves_order_Lemma()
ensures forall phi,Sigma ::  is_ordered(Sigma)  ==> (is_ordered(insert(phi,Sigma))) 
{
forall phi,Sigma | is_ordered(Sigma) 
       ensures is_ordered(insert(phi,Sigma)) 
      { insert_Lemma(phi,Sigma); }
}



// HANDLING AND PRINTING THE INPUT

// From un-ordered sequents of CTL_Formula to Orderd sequents of NNF_Formula

function method seqCTL_to_ord_seqNNF(Sigma: seq<CTL_Formula>): seq<NNF_Formula> {
if Sigma == [] then []
else insert(to_nnf(Sigma[|Sigma|-1]),seqCTL_to_ord_seqNNF(Sigma[..|Sigma|-1]))
}

lemma order_to_nnf_Lemma(Sigma:seq<CTL_Formula>)
ensures is_ordered(seqCTL_to_ord_seqNNF(Sigma))
{
if Sigma != [] {
	order_to_nnf_Lemma(Sigma[..|Sigma|-1]);
	insert_Lemma(to_nnf(Sigma[|Sigma|-1]),seqCTL_to_ord_seqNNF(Sigma[..|Sigma|-1]));
	}
}

// SPLITING THE INPUT INTO INVARIANTS AND NON-INVARIANTS

method seqNNF_to_2ord_seqNNF(Sigma: seq<NNF_Formula>) returns (Inv:seq<NNF_Formula>,Init:seq<NNF_Formula>)
ensures is_ordered(Inv)
ensures is_ordered(Init)
{
if Sigma == [] { return [],[]; }
else {
     var InvR, InitR;
	 InvR,InitR := seqNNF_to_2ord_seqNNF(Sigma[1..]);
     if Sigma[0].AG? {insert_Lemma(Sigma[0],InvR); 
	                  return insert(Sigma[0],InvR),InitR; }
     else { insert_Lemma(Sigma[0],InitR);
	        return InvR,insert(Sigma[0],InitR); }
	 }
}

// TRANSLATING A CTL-FORMULA (SYNTAX: Goré's BENCHMARKS) INTO AN ORDERED SEQUENCE OF NNF-FORMULAS

function numberConj (phi: CTL_Formula): nat {
if phi.Conj? then 1 + numberConj(phi.f1) + numberConj(phi.f2)
else if phi == False ||  phi == True || phi.Var? then 0
else if  phi.Neg? || phi.eX? || phi.aX? || phi.eG? || phi.aG? || phi.eF? || phi.aF? then numberConj(phi.f)
else numberConj(phi.f1) + numberConj(phi.f2)
}

function method to_nnf_sink_AG(phi: CTL_Formula): NNF_Formula
decreases numberConj(phi), numberImp(phi), negDepth(phi)
{
if phi == False then F
else if phi == True then T
else if phi.Var? then V(phi.prop)
else if phi. Neg? then 
	 match phi.f
		case False => T
		case True => F
		case Var(p) =>  NegV(p)
		case Neg(alpha) => assert numberConj(phi) == numberConj(alpha);
		                   assert numberImp(phi) == numberImp(alpha);
		                   assert negDepth(phi) > negDepth(alpha);
						   to_nnf_sink_AG(alpha)
		case eX(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AX(to_nnf_sink_AG(Neg(alpha)))
		case aX(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EX(to_nnf_sink_AG(Neg(alpha)))
		case eG(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AF(to_nnf_sink_AG(Neg(alpha)))
		case aG(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EF(to_nnf_sink_AG(Neg(alpha)))
		case eF(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  AG(to_nnf_sink_AG(Neg(alpha)))
		case aF(alpha) => assert numberConj(phi) == numberConj(Neg(alpha));
		                  assert numberImp(phi) == numberImp(Neg(alpha));
		                  assert negDepth(phi) > negDepth(Neg(alpha));
		                  EG(to_nnf_sink_AG(Neg(alpha)))
		case eR(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                       assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
                               assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       AU(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
		case aR(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                       assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       EU(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
		case eU(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                       assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       AR(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
		case aU(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                       assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                       assert negDepth(phi) > negDepth(Neg(alpha));
							   assert negDepth(phi) > negDepth(Neg(beta));
		                       ER(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
		case Imp(alpha,beta) => assert numberConj(phi) == numberConj(alpha) + numberConj(Neg(beta));
		                        assert numberImp(phi) > numberImp(alpha) + numberImp(Neg(beta));
		                        And(to_nnf_sink_AG(alpha),to_nnf_sink_AG(Neg(beta)))
		case Iff(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                        assert numberImp(phi) > numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                        Or(And(to_nnf_sink_AG(alpha),to_nnf_sink_AG(Neg(beta))),And(to_nnf_sink_AG(beta),to_nnf_sink_AG(Neg(alpha))))
		case Conj(alpha,beta) => assert numberConj(phi) > numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                         assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                         assert negDepth(phi) > negDepth(Neg(alpha));
								 assert negDepth(phi) > negDepth(Neg(beta));
		                         Or(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
		case Disj(alpha,beta) => assert numberConj(phi) == numberConj(Neg(alpha)) + numberConj(Neg(beta));
		                         assert numberImp(phi) == numberImp(Neg(alpha)) + numberImp(Neg(beta));
		                         assert negDepth(phi) > negDepth(Neg(alpha));
								 assert negDepth(phi) > negDepth(Neg(beta));
		                         And(to_nnf_sink_AG(Neg(alpha)),to_nnf_sink_AG(Neg(beta)))
else if phi.eX? then EX(to_nnf_sink_AG(phi.f))
else if phi.aX? then AX(to_nnf_sink_AG(phi.f))
else if phi.eG? then EG(to_nnf_sink_AG(phi.f))
else if phi.aG? then if !phi.f.Conj? then AG(to_nnf_sink_AG(phi.f))
                     else  assert numberConj(aG(phi.f)) > numberConj(aG(phi.f.f1));
						   assert numberConj(aG(phi.f)) > numberConj(aG(phi.f.f2));
					       And(to_nnf_sink_AG(aG(phi.f.f1)),to_nnf_sink_AG(aG(phi.f.f2)))
else if phi.eF? then EF(to_nnf_sink_AG(phi.f))
else if phi.aF? then AF(to_nnf_sink_AG(phi.f))
else if phi.eR? then ER(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
else if phi.aR? then AR(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
else if phi.eU? then EU(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
else if phi.aU? then AU(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
else if phi.Imp? then Or(to_nnf_sink_AG(Neg(phi.f1)),to_nnf_sink_AG(phi.f2))
else if phi.Iff? then Or(And(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2)),And(to_nnf_sink_AG(Neg(phi.f1)),to_nnf_sink_AG(Neg(phi.f2))))
else if phi.Conj? then And(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
else // phi.Or? 
     if to_nnf_sink_AG(phi.f1) == F then to_nnf_sink_AG(phi.f2)
     else if to_nnf_sink_AG(phi.f2) == F then to_nnf_sink_AG(phi.f1)
     else  Or(to_nnf_sink_AG(phi.f1),to_nnf_sink_AG(phi.f2))
}

method splitConj(phi: NNF_Formula) returns (All:seq<NNF_Formula>)
ensures is_ordered(All) 
{
All:= [];
if !phi.And? {  insert_Lemma(phi,All); 
	            All := insert(phi,All);
            }
else { var Allf1 := splitConj(phi.f1);
       var Allf2 := splitConj(phi.f2);
	   merge_Lemma(Allf1,Allf2);
	   All := merge(Allf1,Allf2);
     }
}

method Gore2OrderedSequent(s:string) returns (All:seq<NNF_Formula>)
ensures is_ordered(All)
{
var phiCTL := parse(s);
var phiNNF := to_nnf_sink_AG(phiCTL);
All := splitConj(phiNNF);	
}

// PRINTING THE INPUT in CTL

predicate method is_literalCTL(phi:CTL_Formula) {
phi == True || phi == False || phi.Var? || (phi.Neg? && phi.f.Var?)
}

function method toStringCTL(sigma:CTL_Formula):string
{
if sigma.Conj? || sigma.Disj? || sigma.Imp? || sigma.Iff? || sigma.eU? || sigma.aU? || sigma.eR? || sigma.aR?
then var s1 := if is_literalCTL(sigma.f1) then toStringCTL(sigma.f1) else "(" + toStringCTL(sigma.f1) + ")";
     var s2:= if is_literalCTL(sigma.f2) then toStringCTL(sigma.f2) else "(" + toStringCTL(sigma.f2) + ")";
	 match sigma
	 case Conj(phi,psi) => s1 + "&" + s2
     case Disj(phi,psi) =>  s1 + "|" + s2
	 case aU(phi,psi) => "A(" + s1 + "U" + s2 + ")"
	 case eU(phi,psi) => "E(" + s1 + "U" + s2 + ")"
	 case Imp(phi,psi) => s1 + " -> " + s2 
	 case Iff(phi,psi) => s1 + " <-> " + s2 
	 case aR(phi,psi) => "A(" + s1 + "R" + s2 + ")"
	 case eR(phi,psi) => "E(" + s1 + "R" + s2 + ")"
else if sigma.Neg? || sigma.eX? || sigma.aX? || sigma.eF? || sigma.aF? || sigma.eG? || sigma.aG? 
then var s := if is_literalCTL(sigma.f) then toStringCTL(sigma.f) else "(" + toStringCTL(sigma.f) + ")";
     match sigma
	 case Neg(phi) => "~" +s
	 case aX(phi) => "AX" + s 
	 case eX(phi) => "EX" + s 
	 case aG(phi) => "AG" + s 
	 case eG(phi) => "EG" + s
	 case aF(phi) => "AF" + s
	 case eF(phi) => "EF" + s
else match sigma
     case False => "false"
     case True => "true"
     case Var(n) => n
}

method printSequentCTL(Sigma:seq<CTL_Formula>)
{
if Sigma == [] { print ""; }
else if |Sigma| == 1
     {
	  print toStringCTL(Sigma[0]);
	  }
else {
	  print toStringCTL(Sigma[0]); print "\n";
	  printSequentCTL(Sigma[1..]);
	  }
}

// PRINTING THE INPUT in NNF

/*
predicate method is_literal(phi:NNF_Formula) {
family(phi) <= 3
}
*/

function method toString(sigma:NNF_Formula):string
{
if sigma.And? || sigma.Or? || sigma.EUsel? || sigma.AUsel? || sigma.EU? || sigma.AU? || sigma.ER? || sigma.AR?
then var s1 := if is_literal(sigma.f1) then toString(sigma.f1) else "(" + toString(sigma.f1) + ")";
     var s2:= if is_literal(sigma.f2) then toString(sigma.f2) else "(" + toString(sigma.f2) + ")";
	 match sigma
	 case And(phi,psi) => s1 + "&" + s2
     case Or(phi,psi) =>  s1 + "|" + s2
	 case AU(phi,psi) => "A(" + s1 + "U" + s2 + ")"
	 case EU(phi,psi) => "E(" + s1 + "U" + s2 + ")"
	 case AUsel(phi,psi) => "#A(" + s1 + "U" + s2 + ")"
	 case EUsel(phi,psi) => "#E(" + s1 + "U" + s2 + ")"
	 case AR(phi,psi) => "A(" + s1 + "R" + s2 + ")"
	 case ER(phi,psi) => "E(" + s1 + "R" + s2 + ")"
else if sigma.EX? || sigma.AX? || sigma.EF? || sigma.AF? || sigma.EG? || sigma.AG? || sigma.ER? || sigma.AR?
then var s := if is_literal(sigma.f) then toString(sigma.f) else "(" + toString(sigma.f) + ")";
     match sigma
	 case AX(phi) => "AX" + s 
	 case EX(phi) => "EX" + s 
	 case AG(phi) => "AG" + s 
	 case EG(phi) => "EG" + s
	 case AF(phi) => "AF" + s
	 case EF(phi) => "EF" + s
else match sigma
     case F => "false"
     case T => "true"
     case V(n) => n
     case NegV(n) => "~" + n 
}

method printSequentinLines(Sigma:seq<NNF_Formula>)
{
if Sigma == [] {}
else if |Sigma| == 1
     {
	  print toString(Sigma[0]);
	  }
else {
	  print toString(Sigma[0]); print "\n";
	  printSequentinLines(Sigma[1..]);
	  }
}

}
