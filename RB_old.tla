--------------------------------- MODULE RB ---------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Processes, Messages
CONSTANT qLen

VARIABLES msgQ, dMsgQ, msgBag

\* qConstraint == \A p \in Processes : Len(msgQ[p]) \leq qLen

Init == /\ msgQ = [p \in Processes |-> <<>>]
        /\ msgBag = [p \in Processes |-> {}]
        /\ dMsgQ = [p \in Processes |-> <<>>] 

TypeCheck == msgQ \in [Processes -> Seq(Messages)]

Broadcast(msg, initialSrc, p) == /\ msgQ' = [msgQ EXCEPT ![p] = Append(msgQ[p],<<msg, initialSrc>>)]
                                            
                       
ReliableBroadcast(msg, src) == /\ msg \in Messages
                               /\ src \in Processes
                               /\ \A p \in Processes \ {src} : Broadcast(msg, src, p) \* Send to all processes than itself
                               /\ DeliverMsg(msg, src)
                               
DeliverMsg(msg, src) == /\ msg \in Messages
                        /\ src \in Processes
                        /\ 
                   
Deliver(p) ==  /\ msgQ[p] # << >>
               /\ dMsgQ' =  IF Head(msgQ[p]) \notin msgBag[p] 
                            THEN [dMsgQ EXCEPT ![p] = Append(dMsgQ[p], Head(msgQ[p]) ) ] \* Deliver to itself
                            ELSE dMsgQ
               /\ IF Head(msgQ[p]) \notin msgBag[p] 
                  THEN RBroadcast(Head(msgQ[p]), p) 
                            ELSE dMsgQ
               /\ msgQ' = [msgQ EXCEPT ![p] = Tail(msgQ[p])] \* Remove from receiver Q
                

Next == \/ (\E msg \in Messages,src \in Processes: RBroadcast(msg, src, src) )  
        \/ (\E p \in Processes : Deliver(p))
      

RB == Init /\ [][Next]_<<msgQ,dMsgQ>> /\ TypeCheck


========================
\* END