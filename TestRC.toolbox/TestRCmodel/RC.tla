--------------------------------- MODULE RC ---------------------------------
EXTENDS  Naturals, Sequences, ModProc

CONSTANT RMessage 

Proc == INSTANCE ModProc WITH Data <- [content: RMessage, seqNo: Nat]

Send(msg, p) == /\ msg \in RMessage
                /\ p \in Proc!Process
                /\ p' = [p EXCEPT !.inQueue = Append(@, [content |-> msg, seqNo |-> 1])]
                   
Recv(deliverQueue, p) ==  /\ p \in Proc!Process
                          /\ deliverQueue \in Seq(RMessage)
                          /\ p.inQueue # <<>>
                          /\ deliverQueue' = Append(deliverQueue, Head(p.inQueue).content)
                          /\ p' = [p EXCEPT !.inQueue = Tail(@)]

=============================================================================