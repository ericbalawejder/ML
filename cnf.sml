(* For use in CSC540 Project. From Dr. Wyatt's cnf-sample-code.sml *)
       
(* set the depth of an object (list) to print *) 
Control.Print.printDepth  := 200;
(* set the length of an object (list) to print *)
Control.Print.printLength := 200;        

(* DEFINE THE LOGICAL CONNECTIVES *)
infix -->;  (* NB: "->" is reserved for tycon statements involving functions*) 
infix v;
infix &;
infix <->;

(* DATA TYPE FOR A SENTENCE *) 
datatype sentence =  P | Q | R | S | T             (* allowable sent. vars    *) 
                   | ~ of sentence                 (* negation:      ~P       *) 
                   | v of sentence * sentence      (* disjunction:   P v Q    *) 
                   | & of sentence * sentence      (* conjunction:   P & Q    *) 
                   | --> of sentence * sentence    (* conditional:   P --> Q  *) 
                   | <-> of sentence * sentence;   (* biconditional: P <-> Q  *) 

(* REMOVE ARROWS -- removeArrows *) 
fun removeArrows(~f)      = ~(removeArrows(f))  
  | removeArrows(f & g)   = removeArrows(f) & removeArrows(g)
  | removeArrows(f v g)   = removeArrows(f) v removeArrows(g)
  | removeArrows(f --> g) = ~(removeArrows(f)) v (removeArrows(g))
  | removeArrows(f <-> g) = ((removeArrows(f) & removeArrows(g)) v 
	(removeArrows(~f) & removeArrows(~g)))
  | removeArrows(f)       = f;

(* BRING IN NEGATION, REMOVING DOUBLE NEGATIONS AS WE GO  *) 
fun bringInNegation(~(~f))    = bringInNegation(f)
  | bringInNegation(f & g)    = bringInNegation(f) & bringInNegation(g)
  | bringInNegation(f v g)    = bringInNegation(f) v bringInNegation(g)
  | bringInNegation(~(f & g)) = bringInNegation(~f) v bringInNegation(~g)
  | bringInNegation(~(f v g)) = bringInNegation(~f) & bringInNegation(~g)
  | bringInNegation(f)        = f;

(* DISTRIBUTE THE DISJUNCTION IN THE CONJUNCTIONS *) 
fun distributeDisjInConj(f v (g & h)) = (distributeDisjInConj(f v g) & distributeDisjInConj(f v h))
  | distributeDisjInConj((g & h) v f) = (distributeDisjInConj(g v f) & distributeDisjInConj(h v f))
  | distributeDisjInConj(f v g) =  distributeDisjInConj f v distributeDisjInConj g
  | distributeDisjInConj(f & g) =  distributeDisjInConj f & distributeDisjInConj g
  | distributeDisjInConj f = f;

(* PRINTS OUT CNF WITHOUT ENCLOSING PARENTHESIS*)
fun show2(f & g) = (show2(f); print " & "; show2(g))
  | show2(f v g) = (show2(f); print " v "; show2(g))
  | show2(f --> g) = (show2(f); print " -> "; show2(g))
  | show2(f <-> g) = (show2(f); print " <-> "; show2(g))
  | show2(~ f) = (print "-"; show2(f))
  | show2(P) = (print "P")
  | show2(Q) = (print "Q")
  | show2(R) = (print "R")
  | show2(S) = (print "S")
  | show2(T) = (print "T");

(* TOP LEVEL FUNCTIONS *)
fun show(f & g) = (print "(" ; show2(f); print ") & ("; show2(g); print ")")
  | show(f v g) = (print "(" ; show2(f); print ") v ("; show2(g); print ")")
  | show(f --> g) = (print "("; show2(f); print ") -> ("; show2(g); print ")")
  | show(f <-> g) = (print "("; show2(f); print ") <-> ("; show2(g); print ")")
  | show(~ f) = (print "-"; show2(f); print "")
  | show(P) = (print "P")
  | show(Q) = (print "Q")
  | show(R) = (print "R")
  | show(S) = (print "S")
  | show(T) = (print "T");

fun cnf (s) = (distributeDisjInConj(bringInNegation(removeArrows(s))));


fun run s  =  (print "\nSentence is: "; 
               show s; 
               print "\n Its CNF is: ";
               show(cnf s); 
               print "\n\n");

fun printNStr(s,0) = ()
  | printNStr(s,n) = (print s; printNStr(s,n-1));

fun go1(_,_,nil) = print "\n"
  | go1(i,n,s::ss) = if i>n 
                         then () 
                     else (print "\n";
                           if i>=10 then printNStr(" ",69) else printNStr(" ",70);
                           print "Example F";
                           print(Int.toString i);
                           run s; 
                           printNStr("=", 80);
                           go1(i+1,n,ss));

(* TOP LEVEL DRIVING FUNCTION *)
fun go s =  let 
                val count = length s
            in
                (printNStr("=",80);
                 go1(1,count,s) )
            end;

(*---------------------------------------------------------------------------*) 
(* TESTING EXAMPLES *) 

val f1 = P;
val f2 = ~(P);
val f3 = ~(~(P));
val f4 = ~(~(~(P)));
val f5 = P v ~ P;
val f6 = P --> Q;
val f7 = P <-> Q;
val f8 = (P v Q) --> P;
val f9 = (S & T) v (Q & R);
val f10 = ~S & ~T;
val f11 = ~(P --> (~Q --> ~P));
val f12 = (P --> Q) & (Q --> R);
val f13 = ((P --> Q) &  (Q --> R))  -->  (P --> R);
val f14 = ~(((P --> ~Q) v (~P & ~Q)));
val f15 = ((P & Q) --> P);
val f16 = (P & Q) v (R & S);
val f17 = ((P --> Q) --> (~Q --> ~P));
val f18 = ((P --> ~Q) v (~P & ~Q));
val f19 = ((P --> Q) <-> (~Q --> ~P));
val f20 = ~((P --> ~Q) <-> (~P & ~Q));
val f21 = ~((P --> ~Q)  v  (~P & ~Q));
val f22 = ~(~(((P --> Q) & (Q --> R)) --> (P --> R)));
val f23 = (P --> Q) v (Q --> R);
val f24 = ((P --> Q) &  (Q --> R))  -->  (P --> R);
val f25 = ((P & Q) v (~ P & ~ R)) v ((S & T v (~ Q & ~ P)));

val tests = [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,
	     f18,f19,f20,f21,f22,f23,f24,f25];


(* END END END *)
(*---------------------------------------------------------------------------*) 
