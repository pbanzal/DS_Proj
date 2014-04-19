------------------------------- MODULE TestRC -------------------------------
EXTENDS RC


VARIABLES p1, p2, q1, q2
 
Init == /\ p1 = [id |-> 1, sendQueue |-> <<>>, inQueue |-> <<>>]
        /\ p2 = [id |-> 2, sendQueue |-> <<>>, inQueue |-> <<>>]
        /\ q1 = <<>>
        /\ q2 = <<>>
       
constraint == Len(q1) \leq 1 /\ Len(q2) \leq 1 /\ Len(p1.inQueue) \leq 1  /\ Len(p2.inQueue) \leq 1
 
TypeInv == /\ p1 \in Proc!Process
           /\ p2 \in Proc!Process

Next == \/ /\ \E m \in RMessage : Send(m, p1) 
           /\ UNCHANGED <<p2,q1,q2>> 
        \/ /\ \E m \in RMessage : Send(m, p2)
           /\ UNCHANGED <<p1,q1,q2>>
        \/ /\ Recv(q1, p1)
           /\ UNCHANGED <<p2,q2>>
        \/ /\ Recv(q2, p2)
           /\ UNCHANGED <<p1,q1>>
        
TestRC == Init /\ [][Next]_<<p1, p2, q1, q2>>

THEOREM TestRC => []TypeInv 

=============================================================================
\* Modification History
\* Last modified Sat Apr 19 19:40:56 EDT 2014 by praseem
\* Created Sat Apr 19 19:04:04 EDT 2014 by praseem
