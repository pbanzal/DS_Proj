--------------------------------- MODULE RC ---------------------------------
EXTENDS  Naturals, Sequences, TLC

CONSTANT Data

Proc == INSTANCE ModProc WITH RMessage <- [content: Data]


Send(msg, p) == /\ msg \in Data
                        /\ p \in Proc!Process
                        /\ p' = [p EXCEPT !.inQueue = Append(@, [content |-> msg])]
                        /\ Print(p.inQueue , TRUE)
                   
Recv(CB(_), p) ==   /\ p \in Proc!Process
                    /\ p.inQueue # <<>>
                    /\ CB(Head(p.inQueue).content)
                    /\ p' = [p EXCEPT !.inQueue = Tail(@)]
                          

RecvQ(deliverQueue, p) == /\ p \in Proc!Process
                          /\ deliverQueue \in Seq(Data)
                          /\ p.inQueue # <<>>
                          /\ deliverQueue = <<>>
                          /\ deliverQueue' = Append(deliverQueue, Head(p.inQueue).content)
                          /\ p' = [p EXCEPT !.inQueue = Tail(@)]

=============================================================================
