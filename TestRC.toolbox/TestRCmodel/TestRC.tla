------------------------------- MODULE TestRC -------------------------------
EXTENDS RC, Naturals, Sequences, TLC  

CONSTANT ProcessId

\* LOCAL Process == {[id |-> x, seqNoRB |-> 0, inQueue |-> <<>>] : x \in ProcessId}
VARIABLE Processes

\* x == INSTANCE RC WITH Data <- MsgSet

init == /\ Processes = [procId \in ProcessId |-> [id |-> procId, seqNoRB |-> 0, inQueue |-> <<>>]]
 
constraint == \A p \in Processes : Len(p.inQueue) \leq 1

CB(msg) == /\ msg \in Data
           \*/\ Print(msg, TRUE)   

Next == \E pid \in ProcessId:
            /\ \/ LET curP == Processes[pid] IN 
                    /\ \E m \in Data : Send(m, curP)
                    /\ Processes' = [Processes EXCEPT ![pid] = [id |-> curP.id, seqNoRB |-> curP.seqNoRB, inQueue |-> curP.inQueue]]            
               \* \/ Recv(CB, Processes[pid])
           \*  /\ UNCHANGED Processes 
          \*  /\ Processes' = [Processes EXCEPT ![pid] = [id |-> @.id, seqNoRB |-> @.seqNoRB, inQueue |-> @.inQueue]]
          
TestRC == init /\ [][Next]_<<Processes>>


=============================================================================
\* Modification History
\* Last modified Sun Apr 20 18:20:23 EDT 2014 by praseem
\* Created Sat Apr 19 19:04:04 EDT 2014 by praseem
