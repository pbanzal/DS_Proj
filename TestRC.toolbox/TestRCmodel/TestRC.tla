------------------------------- MODULE TestRC -------------------------------
EXTENDS RC, Naturals, Sequences, TLC  

CONSTANT ProcessId

\* LOCAL Process == {[id |-> x, seqNoRB |-> 0, inQueue |-> <<>>] : x \in ProcessId}
VARIABLE Processes, rp

\* x == INSTANCE RC WITH Data <- MsgSet

init == /\ Processes = [procId \in ProcessId |-> [id |-> procId, seqNoRB |-> 0, inQueue |-> <<>>]]
        /\ rp = [id |-> 0, seqNoRB |-> 0, inQueue |-> <<>>]
 
constraint == \A p \in Processes : Len(p.inQueue) \leq 1

CB(msg) == /\ msg \in Data
           \*/\ Print(msg, TRUE)   

Next == \E pid \in ProcessId:
            /\ \/ \E m \in Data : Send(m, Processes[pid])
               \/ Recv(CB, Processes[pid])
            /\ Processes' = [Processes EXCEPT ![pid] = [id |-> @.id, seqNoRB |-> @.seqNoRB, inQueue |-> @.inQueue]]
          
TestRC == init /\ [][Next]_<<Processes, rp>>


=============================================================================
\* Modification History
\* Last modified Sun Apr 20 17:29:02 EDT 2014 by praseem
\* Created Sat Apr 19 19:04:04 EDT 2014 by praseem
