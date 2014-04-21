------------------------------- MODULE TestRC -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT ProcessId, Message, newRcvQ(_)

proc == INSTANCE ModProc 

ASSUME \A pid \in ProcessId: newRcvQ(pid) \in Seq(Message)

rChannel(pid) == INSTANCE RC WITH Data <- Message, rcvQ <- newRcvQ(pid) 
 
(*constraint == \A p \in Processes : Len(p.inQueue) \leq 1*)

CB(msg) == /\ msg \in Message 
           \*/\ Print(msg, TRUE)   

Next == \E pid \in ProcessId:
            /\ \/ \E m \in Message : rChannel(pid)!Send(m)
               \/ rChannel(pid)!Recv(CB)
          \*  /\ Processes' = [Processes EXCEPT ![pid] = [id |-> @.id, seqNoRB |-> @.seqNoRB, inQueue |-> @.inQueue]]
          
TestRC == init /\ [][Next]_<<Processes>>


=============================================================================
\* Modification History
\* Last modified Sun Apr 20 18:59:53 EDT 2014 by praseem
\* Created Sat Apr 19 19:04:04 EDT 2014 by praseem
