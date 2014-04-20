--------------------------------- MODULE RB ---------------------------------
EXTENDS RC, Integers, Sequences, TLC

CONSTANTS procSet, RBdata

VARIABLES mapProcMsg (* mapProcMsg is a maps process p with set of messages RBDelivered by p *) 

RBMessage == [content: RBdata, seqNo: Nat, src: Nat] 
RBproc == INSTANCE ModProc     
RChannel == INSTANCE RC WITH Data <- RBMessage  

TypeInv == /\ procSet \subseteq Proc!Process
           /\ mapProcMsg \in [procSet -> SUBSET RBMessage]

Init == /\ \A p \in procSet: mapProcMsg[p] = {}

RBBroadcast(msg, p) ==  /\ msg \in RBdata
                      /\ LET currentMsg == [content |->msg, seqNo |-> p.seqNoRB, src |-> p.id] 
                         IN  \A dstP \in procSet: RChannel!Send(currentMsg, dstP)
                      /\ p' = [p EXCEPT !.seqNoRB = @+1] 
                      /\ UNCHANGED mapProcMsg
                      
LOCAL Forward(msg) == /\ msg \in RBMessage
                /\ \A dstP \in procSet: RChannel!Send(msg, dstP)

RBDeliver(deliverCB(_), p) == /\ p \in RBproc!Process
                             /\ LET newCB(currMsg) == /\ currMsg \in RBMessage
                                                      /\ IF currMsg \notin mapProcMsg[p]
                                                         THEN  /\ mapProcMsg' = [mapProcMsg EXCEPT ![p] = @ \cup currMsg]
                                                               /\ Forward(currMsg) 
                                                               /\ deliverCB(currMsg.content)
                                                         ELSE UNCHANGED mapProcMsg
                               IN RChannel!Recv(newCB, p)

                           
=============================================================================

(*                
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
*)