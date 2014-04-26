----- MODULE Calculator -------
EXTENDS Naturals, TLC
CONSTANT Keys
VARIABLE d

Init == d = 1

Inc(x) == x' = x+1

Next == /\ d' = d + 2
        /\ Inc(d)
        /\ Print(d,TRUE)
        /\ Print("***************",TRUE)
        
        
        Spec ==  [Next]_<<d>>



==========================

