--------------------------------- MODULE RC ---------------------------------
EXTENDS  Naturals, Sequences, TLC

CONSTANT Data
VARIABLE rcvQ

RMessage == [content:Data]

init == rcvQ = <<>>

Send(msg) == /\ msg \in Data
             /\ rcvQ' = Append(rcvQ, [content: msg])
                   
Recv(CB(_)) ==  /\ rcvQ # <<>>
                /\ CB(Head(rcvQ).content)
                /\ rcvQ' = Tail(rcvQ)
                
=============================================================================
