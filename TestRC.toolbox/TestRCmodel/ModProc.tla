------------------------------ MODULE ModProc ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data
 
Process == [id: Nat, sendQueue: Seq(Data), inQueue: Seq(Data)]
=============================================================================

Init == /\ p1 = [id |-> 1, sendQueue -> <<>>, inQueue |-> <<>>]
        /\ p2 = [id |-> 2, sendQueue -> <<>>, inQueue |-> <<>>]
        
        /\ p1 \in Proc!Process
        /\ p2 \in Proc!Process

                          
Next == \/ \E p \in Proc!Process, msg \in RMessage : Send(msg, p)
        \/ \E p \in Proc!Process, dQueue \in Seq(RMessage) : Recv(dQueue, p)
        
RC == [][Next]_<<>>
