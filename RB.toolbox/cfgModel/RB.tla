--------------------------------- MODULE RB ---------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Processes, Messages
CONSTANT qLen

VARIABLES msgQ, dMsgQ
qConstraint == \A p \in Processes : Len(msgQ[p]) \leq qLen

State == <<msgQ, dMsgQ>>

\* Messages == [src: Processes, data : Domain \cup {""} ]

Init == /\ msgQ = [p \in Processes |-> <<>>]
        /\ dMsgQ = [p \in Processes |-> <<>>] 

TypeCheck == msgQ \in [Processes -> Seq(Messages)]

Send(msg, p) == msgQ' = [msgQ EXCEPT ![p] = Append(msgQ[p],msg)]                         
                
                                     
RBroadcast(msg,src) == /\ msg \in Messages
                       /\ src \in Processes
                       /\ \A p \in Processes\{src} : Send(msg, p) \* Send to all processes than itself
                       /\ dMsgQ' = [dMsgQ EXCEPT ![src] = Append(dMsgQ[src], msg)] \* Deliver to itself
                   
Deliver(p) ==  /\ msgQ[p] # << >> 
               /\ dMsgQ' = [dMsgQ EXCEPT ![p] = Append(dMsgQ[p], Head(msgQ[p]) ) ] \* Deliver to itself
               /\ msgQ' = [msgQ EXCEPT ![p] = Tail(msgQ[p])] \* Remove from receiver Q
               /\ RBroadcast(Head(msgQ[p]),p) 

Next == \/ (\E msg \in Messages,src \in Processes: RBroadcast(msg,src) )  
          
       \/ (\E p \in Processes : Deliver(p))
      

RB == Init /\ [][Next]_<<msgQ,dMsgQ>> /\ TypeCheck

========================