---------------------------- MODULE RBsingleFile ----------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC

CONSTANTS 
    Message, 
    processes

VARIABLES 
     processMap


RBMessage == [content: Message, sendId: Nat, seqNo: Nat]
RMessage == [content: RBMessage]

Send(pMap, p, msg) == /\ msg \in RBMessage
                      /\ pMap' = [pMap EXCEPT ![p].rcvQ = Append(@, [content: msg])]
                   
Recv(CB(_), pMap, p) ==  /\ pMap[p].rcvQ # <<>>
                         /\ CB(Head(pMap[p].rcvQ).content)
                         /\ pMap' = [pMap EXCEPT ![p].rcvQ = Tail(@)]

InitProcesses == processMap = \A p \in processes: [p -> [rcvQ: {}, id: p, seqNo: 0, rbBag: {}]]  
                 
init == InitProcesses

Broadcast(msg, curP) == /\ msg \in Message
                        /\ curP \in processes
                        /\ \A p \in processes: 
                               Send( processMap, 
                                     p, 
                                     [content |-> msg, sendId |-> curP.id, seqNo |-> curP.seqNo])
                        /\ processMap' = [processMap EXCEPT ![curP].seqNo = @ + 1]

Forward(pMap, p, msg) == /\ msg \in RBMessage
                         /\ \A dstP \in processes\{p}: Send(pMap, dstP, msg)
                        
Deliver(CB(_), curP) == /\ curP \in processes
                        /\ LET newCB(currMsg) == /\ currMsg \in RBMessage
                                                 /\ IF currMsg \notin processMap[curP].rbBag 
                                                    THEN  
                                                        /\ processMap' = [processMap EXCEPT ![curP].rbBag = @ \cup currMsg]
                                                        /\ Forward(processMap, curP, currMsg) 
                                                        /\ CB(currMsg.content)
                                                    ELSE 
                                                        UNCHANGED processMap
                           IN Recv(newCB, processMap, curP) 
=============================================================================
\* Modification History
\* Last modified Mon Apr 21 14:16:37 EDT 2014 by praseem
\* Created Mon Apr 21 12:43:41 EDT 2014 by praseem
