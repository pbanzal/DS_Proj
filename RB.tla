--------------------------------- MODULE RB ---------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Processes, Messages

VARIABLES msgQ, dMsgQ

State == <<msgQ, dMsgQ>>

\* Messages == [src: Processes, data : Domain \cup {""} ]

Init == /\ msgQ = [p \in Processes |-> {}]
        /\ dMsgQ = [p \in Processes |-> {}] 

TypeCheck == msgQ \in [Processes -> Seq(Messages)]

Send(msg, p) == /\ msgQ' =  IF \neg(msg \in msgQ[p]) 
                         THEN  [msgQ EXCEPT ![p] = msgQ[p] \cup {msg}] 
                         ELSE  msgQ
                /\ UNCHANGED dMsgQ
                                     
RBroadcast(msg) == /\ msg \in Messages
                   /\ \A p \in Processes : Send(msg, p)

Deliver(p,msg) ==  /\ dMsgQ' =  IF \neg(msg \in dMsgQ[p]) 
                                THEN [dMsgQ EXCEPT ![p] = dMsgQ[p] \cup {msg}] 
                                ELSE dMsgQ
                   /\ UNCHANGED msgQ
                  \* /\ IF \neg(msg \in dMsgQ[p]) 
                  \*                    THEN RBroadcast(msg) ---> If we add this, only 1 state is created.
                  \*                    ELSE UNCHANGED State

\*RDeliver ==  \A p \in Processes : Deliver(p,m)     

\*Next == (\A msg \in Messages : RBroadcast(msg)) \/ RDeliver
Next == \/ (\E msg \in Messages : RBroadcast(msg)) 
        \/ (\E p \in Processes, m \in Messages : Deliver(p,m))
\* Next == \A msg \in Messages : Print(msg, TRUE)

\* RB should be that, a message if delivered should be a message.
\* Also, it should say that, a delivered message should be send by someone

SafetyOne == \

RB == \* Add box next, typeInvariant etc
