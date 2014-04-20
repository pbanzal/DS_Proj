--------------------------------- MODULE RB ---------------------------------
EXTENDS RC, Integers, Sequences, TLC

CONSTANTS procSet, RBdata

VARIABLES mapProcMsg
 
RBproc == INSTANCE ModProc WITH RBMessage <- [content: RBdata, seqNo: Nat, src: Nat]     
RChannel == INSTANCE RC WITH Data <- RBMessage 

TypeInv == /\ procSet \subseteq Proc!Process
           /\ mapProcMsg \in [procSet -> SUBSET RBMessage]

Init == /\ \A p \in procSet: mapProcMsg[p] = {}

Broadcast(msg, p) ==  /\ msg \in RBdata
                      /\ LET currentMsg == [content |->msg, seqNo |-> p.seqNoRB, src |-> p.id] 
                         IN  \A dstP \in procSet: RChannel!Send(currentMsg, dstP)
                      /\ p' = [p EXCEPT !.seqNoRB = @+1] 
                      /\ UNCHANGED mapProcMsg
                      
Forward(msg) == /\ msg \in RBMessage
                /\ \A dstP \in procSet: RChannel!Send(msg, dstP)
                
Deliver(deliverQ, p) == /\ p \in RBproc!Process
                        /\ deliverQ \in Seq(RBdata)
                        /\ deliverQ = <<>>
                        /\ RChannel!Recv(p.rbQueue, p)
                        /\ LET currMsg == Head(p.rbQueue) IN
                           IF currMsg \notin mapProcMsg[p]
                           THEN  /\ deliverQ' = <<currMsg>>
                                 /\ mapProcMsg' = [mapProcMsg EXCEPT ![p] = @ \cup currMsg]
                                 /\ Forward(currMsg) 
                                 /\ p' = [p EXCEPT !.rbQueue = Tail(@)]
                           ELSE UNCHANGED mapProcMsg 
                                  
=============================================================================
\* Modification History
\* Last modified Sat Apr 19 23:24:16 EDT 2014 by praseem
\* Created Sat Apr 19 21:31:06 EDT 2014 by praseem
