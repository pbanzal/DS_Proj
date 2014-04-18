--------------------------------- MODULE RB ---------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Processes, Domain, Messages

VARIABLES msgQ, dMsgQ

State == <<msgQ, dMsgQ>>

\* Messages == [src: Processes, data : Domain \cup {""} ]

Init == /\ msgQ = [p \in Processes |-> <<>>]
        /\ dMsgQ = [p \in Processes |-> <<>>] 

TypeCheck == msgQ \in [Processes -> Seq(Messages)]

Send(msg, p) == msgQ' = IF \neg(msg \in msgQ[p]) 
                        THEN [msgQ EXCEPT ![p] = Append(msgQ[p], msg)] 
                        ELSE UNCHANGED msgQ
                                      
RBroadcast(msg) == /\ msg \in Messages
                   \* /\ \A p \in Processes : Send(msg, p)

Deliver(p) == \A msg \in msgQ[p] : /\ dMsgQ' =  IF \neg(msg \in dMsgQ[p]) 
                                                THEN [dMsgQ EXCEPT ![p] = Append(dMsgQ[p], msg)] 
                                                ELSE dMsgQ
                                   /\ IF \neg(msg \in dMsgQ[p]) 
                                      THEN RBroadcast(msg)
                                      ELSE UNCHANGED State

RDeliver == /\ \A p \in Processes : Deliver(p)     

Next == (\A msg \in Messages : RBroadcast(msg)) \/ RDeliver
\* Next == \A msg \in Messages : Print(msg, TRUE)

RB == Init
=============================================================================
\* Modification History
\* Last modified Fri Apr 18 17:58:47 EDT 2014 by praseem
\* Created Fri Apr 18 14:17:44 EDT 2014 by praseem
