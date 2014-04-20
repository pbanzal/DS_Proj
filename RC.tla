--------------------------------- MODULE RC ---------------------------------
EXTENDS  Naturals, Sequences, ModProc

CONSTANT Data 

Proc == INSTANCE ModProc WITH RMessage <- [content: Data]

Send(msg, p) == /\ msg \in Data
                /\ p \in Proc!Process
                /\ p' = [p EXCEPT !.inQueue = Append(@, [content |-> msg])]
                   
Recv(deliverQueue, p) ==  /\ p \in Proc!Process
                          /\ deliverQueue \in Seq(Data)
                          /\ p.inQueue # <<>>
                          /\ deliverQueue = <<>>
                          /\ deliverQueue' = Append(deliverQueue, Head(p.inQueue).content)
                          /\ p' = [p EXCEPT !.inQueue = Tail(@)]

=============================================================================
