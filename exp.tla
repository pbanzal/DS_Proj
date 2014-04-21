----- MODULE Exp -------
EXTENDS Naturals, TLC
CONSTANT Keys
VARIABLE f

TypeOK ==   /\ Keys \subseteq STRING 
            /\ f \in [Keys -> Nat]

Init == f = [n \in Keys |-> IF n = "a" THEN 1 ELSE IF n = "b" THEN 2 ELSE 3]

Inc(x) == x' = x+1

Do == /\ Inc(f["a"])
      /\ UNCHANGED f
      
Spec == Init /\ [Do]_<<f>> 
==========================