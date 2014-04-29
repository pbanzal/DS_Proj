-------------------------------- MODULE CAB --------------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC,
    FiniteSets

CONSTANTS 
    Message,
    processes,
    crashedProc

VARIABLES 
     rcQ,
     rbQ,
     bQ,
     crashed,
     seqNoQ,
     procProcSeqRcv,
     procProcSeqSnd,
     deliveredSet,
     MessageQueue,
     prevDlvrs,
     suspects, 
     causalDelivered
     

\*CMessage == [content : Message, sendId : processes]
\*CausalMessage == [content: Message, prevDlvMsgs : SUBSET CMessage, sendId : processes]
CausalMessage == [content: Message, sendId : processes]
RBMessage == [content: CausalMessage, sendId : processes]
RMessage == [content : RBMessage, sendId: processes, seqNo: Nat]


Debug(msg,level) == IF level > 3 THEN Print(msg, TRUE) ELSE TRUE

Init == /\ rcQ = [p \in processes |-> {}]
        /\ bQ = [p \in processes |-> {}]
        /\ crashed = [p \in processes |-> IF p \in crashedProc 
                                          THEN TRUE
                                          ELSE FALSE]
        /\ rbQ = [p \in processes |-> <<>>]
        /\ seqNoQ = [p \in processes |-> 0]
        /\ procProcSeqRcv = [pi \in processes |-> [pj \in processes |-> 0]]
        /\ procProcSeqSnd = [pi \in processes |-> [pj \in processes |-> 0]]
        /\ deliveredSet = [p \in processes |-> {}]
        /\ MessageQueue = [p \in processes |-> <<0,1>>]  
        /\ prevDlvrs = [p \in processes |-> {}] 
        /\ suspects = [p \in processes |-> {}]
        /\ causalDelivered = [p \in processes |-> {}]
        
      
        


(* -------- Broadcast ------------- *)

Broadcast(msg, pid) ==  /\ Debug("START Broadcast............."\cup pid, 1)
                        /\ msg \in Message
                        /\ pid \in processes
                        /\  IF msg \notin bQ[pid]
                            THEN
                                /\ Debug("Broadcast pid: " \cup pid \cup " msg: " \cup msg, 1)
                                /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @ + 1]
                                /\ IF crashed[pid] = TRUE
                                   THEN
                                        \E p \in processes: 
                                            /\ crashed[p] = FALSE
                                            /\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> [content |->  msg, sendId |-> pid], prevDlvMsgs |-> prevDlvrs[pid], sendId |-> pid, seqNo |-> procProcSeqSnd[pid][p]]}]
                                            /\ procProcSeqSnd' = [procProcSeqSnd EXCEPT ![pid][p] = @ + 1]
                                   ELSE 
                                        /\ rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid], prevDlvMsgs |-> prevDlvrs[pid], sendId |-> pid, seqNo |-> procProcSeqSnd[pid][p]]}]
                                        /\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid THEN procProcSeqSnd[pi][pj] + 1 ELSE procProcSeqSnd[pi][pj]]]   
                                /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {msg} ]           
                            ELSE
                                /\ UNCHANGED <<bQ,rcQ,seqNoQ,procProcSeqSnd>>
                        /\ UNCHANGED <<rbQ,deliveredSet,crashed,procProcSeqRcv,suspects,causalDelivered>>
                        
                        
CABroadcast(msg, pid) == /\ Broadcast(msg , pid) 
                         \*/\ Broadcast([content |-> msg, sendId |-> pid] , pid) 

                         /\ prevDlvrs' = [prevDlvrs EXCEPT ![pid] = {}]
 
Deliver(CB(_,_), pid) ==    /\ Debug("START Deliver............."\cup pid, 1)
                            /\ pid \in processes
                            /\ LET newCB(currMsg) ==   IF currMsg.content \notin deliveredSet[pid] THEN
                                                                /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg.content}]
                                                                /\  IF currMsg.content.sendId # pid THEN 
                                                                        /\ rcQ' = [dstP \in processes |-> 
                                                                                        IF dstP # pid THEN 
                                                                                             rcQ[dstP] \cup {[content |-> currMsg.content, prevDlvMsgs |-> currMsg. prevDlvMsgs, sendId |-> pid, seqNo |-> procProcSeqSnd[pid][dstP]]}
                                                                                        ELSE 
                                                                                            rcQ[pid]  \ {currMsg}]
                                                                        /\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid 
                                                                                                                                            THEN
                                                                                                                                                IF pj # pid THEN 
                                                                                                                                                    procProcSeqSnd[pi][pj] + 1
                                                                                                                                                ELSE
                                                                                                                                                    procProcSeqSnd[pi][pj]  
                                                                                                                                            ELSE procProcSeqSnd[pi][pj]]]
                                                                        /\ UNCHANGED <<bQ,seqNoQ,crashed>>
                                                                    ELSE
                                                                        /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}]
                                                                        /\ UNCHANGED <<bQ,seqNoQ,crashed,procProcSeqSnd>>
                                                                /\ CB(currMsg,pid) 
                                                       ELSE 
                                                                /\ Debug("ELSE PART", 1)
                                                                /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                                /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed,procProcSeqSnd>>
                                                                
                               IN    /\ rcQ[pid] # {}
                                     
                                     /\  IF crashed[pid] = FALSE THEN 
                                                \E x \in rcQ[pid] : 
                                                   
                                                    /\ \A m1 \in rcQ[pid] : x.sendId \leq m1.sendId  
                                                    /\ x.seqNo = procProcSeqRcv[pid][x.sendId]
                                                    
                                                    /\ newCB(x)
                                                    /\ procProcSeqRcv' = [procProcSeqRcv EXCEPT ![pid][x.sendId] = @ + 1]
                                               
                                         ELSE 
                                                \E x \in rcQ[pid] : 
                                                    /\ x.seqNo = procProcSeqRcv[pid][x.sendId]
                                               
                                                    /\ newCB(x)
                                                    /\ procProcSeqRcv' = [procProcSeqRcv EXCEPT ![pid][x.sendId] = @ + 1]
                                        
  
                               (*IN   /\ rcQ[pid] # {}
                                    /\ \E elem \in rcQ[pid] : 
                                            /\ elem.seqNo = procProcSeqRcv[pid][elem.sendId]
                                            /\ newCB(elem)
                                            /\ procProcSeqRcv' = [procProcSeqRcv EXCEPT ![pid][elem.sendId] = @ + 1]*)
                               
                                                     
               
(*Deliver(CB(_,_), pid) ==    /\ Debug("START Deliver............."\cup pid, 1)
                            /\ pid \in processes
                            /\ LET newCB(currMsg) ==   /\ IF pid \in crashedProc THEN
                                                            IF currMsg.content \notin deliveredSet[pid] THEN
                                                                \*/\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg.content}]
                                                                /\ deliveredSet' = [x \in processes |-> deliveredSet[x] \cup {currMsg.content}] \*ATOMIC
                                                                (*/\  IF currMsg.sendId # pid THEN 
                                                                        (*/\ rcQ' = [dstP \in processes |-> 
                                                                                        IF dstP # pid THEN 
                                                                                            rcQ[dstP] \cup {[content |-> currMsg.content, prevDlvMsgs |-> currMsg. prevDlvMsgs, sendId |-> pid, seqNo |-> procProcSeqSnd[pid][dstP]]}
                                                                                        ELSE 
                                                                                            rcQ[pid]  \ {currMsg}]*)
                                                                        /\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid 
                                                                                                                                            THEN
                                                                                                                                                IF pj # pid THEN 
                                                                                                                                                    procProcSeqSnd[pi][pj] + 1
                                                                                                                                                ELSE
                                                                                                                                                    procProcSeqSnd[pi][pj]  
                                                                                                                                            ELSE procProcSeqSnd[pi][pj]]]
                                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ,crashed>>
                                                                    ELSE
                                                                        /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}]
                                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ,crashed,procProcSeqSnd>>*)
                                                                /\ rcQ' = [x \in processes |-> rcQ[x] \ {currMsg}] 
                                                                \*/\ CB(currMsg,pid)
                                                                /\ rbQ' = [x \in processes |-> Append(rbQ[x],currMsg)] 
                                                                /\ UNCHANGED <<bQ,seqNoQ,crashed,procProcSeqSnd>>
                                                            ELSE 
                                                                /\ Debug("ELSE PART", 1)
                                                                /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                                /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed,procProcSeqSnd,suspects,causalDelivered,prevDlvrs>>
                               
                                                          ELSE
                                                            IF currMsg.content \notin deliveredSet[pid] THEN
                                                                \*/\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg.content}]
                                                                /\ deliveredSet' = [x \in processes|-> IF  x \in processes\crashedProc THEN deliveredSet[x] \cup {currMsg.content} ELSE deliveredSet[x]] \*ATOMIC
                                                                (*/\  IF currMsg.sendId # pid THEN 
                                                                        (*/\ rcQ' = [dstP \in processes |-> 
                                                                                        IF dstP # pid THEN 
                                                                                            rcQ[dstP] \cup {[content |-> currMsg.content, prevDlvMsgs |-> currMsg. prevDlvMsgs, sendId |-> pid, seqNo |-> procProcSeqSnd[pid][dstP]]}
                                                                                        ELSE 
                                                                                            rcQ[pid]  \ {currMsg}]*)
                                                                        /\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid 
                                                                                                                                            THEN
                                                                                                                                                IF pj # pid THEN 
                                                                                                                                                    procProcSeqSnd[pi][pj] + 1
                                                                                                                                                ELSE
                                                                                                                                                    procProcSeqSnd[pi][pj]  
                                                                                                                                            ELSE procProcSeqSnd[pi][pj]]]
                                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ,crashed>>
                                                                    ELSE
                                                                        /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}]
                                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ,crashed,procProcSeqSnd>>*)
                                                                /\ rcQ' = [x \in processes |-> IF  x \in processes\crashedProc THEN rcQ[x] \ {currMsg} ELSE rcQ[x] ] 
                                                                /\ rbQ' = [x \in processes |-> IF  x \in processes\crashedProc THEN Append(rbQ[x],currMsg) ELSE rbQ[x]] 
                                                                /\ UNCHANGED <<bQ,seqNoQ,crashed,procProcSeqSnd>>
                                                            ELSE 
                                                                /\ Debug("ELSE PART", 1)
                                                                /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                                /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed,procProcSeqSnd,suspects,causalDelivered,prevDlvrs>>
                                                                                         
                               
                               IN   /\ rcQ[pid] # {}
                                    /\ \E elem \in rcQ[pid] : 
                                            /\ elem.seqNo = procProcSeqRcv[pid][elem.sendId]
                                            /\ newCB(elem)
                                            /\ procProcSeqRcv' = [procProcSeqRcv EXCEPT ![pid][elem.sendId] = @ + 1]
                                        
                             
*)
                          
myCallBackForCausal(m,p) ==   /\ Debug("Delivered by Causal", 2) 
                              /\ Debug(m, 1) 
                              \*/\ causalDelivered' = [causalDelivered EXCEPT ![p] = Append(@,m)]
                              /\ causalDelivered' = [causalDelivered EXCEPT ![p] = @ \cup {m}]
                          


CADeliver(CB(_,_), pid) == /\ rbQ[pid] # <<>>
                           /\ IF suspects[pid] # {} THEN Print(suspects,TRUE) ELSE TRUE
                           /\ LET msg == Head(rbQ[pid]) IN
                                IF msg.content.sendId \notin suspects[pid] THEN
                                    IF \A prevMsg \in msg.prevDlvMsgs : prevMsg.content \in deliveredSet[pid] 
                                    \*IF \A prevMsg \in prevDlvrs[msg.sendId] : prevMsg \in prevDlvrs[pid]
                                    THEN 
                                        /\ CB(msg.content,pid)
                                        /\ prevDlvrs' = [prevDlvrs EXCEPT ![pid] = @ \cup {msg}]
                                        /\ rbQ' = [rbQ EXCEPT ![pid] = Tail(@)]
                                        /\ UNCHANGED <<rcQ,deliveredSet,seqNoQ,bQ,crashed,procProcSeqSnd,procProcSeqRcv,suspects>>
                                    ELSE 
                                        /\ suspects' = [suspects EXCEPT ![pid] = @ \cup {msg.sendId}]
                                        /\ rbQ' = [rbQ EXCEPT ![pid] = Tail(@)]
                                        /\ UNCHANGED <<rcQ,deliveredSet,seqNoQ,bQ,crashed,procProcSeqSnd,procProcSeqRcv,prevDlvrs,causalDelivered>>
                                ELSE 
                                     UNCHANGED <<prevDlvrs,causalDelivered,suspects>>  
                                    
(*CADeliver2(CB(_,_), pid,msg) == IF msg.content.sendId \notin suspects[pid] THEN
                                    IF \A prevMsg \in msg.prevDlvMsgs : prevMsg.content \in deliveredSet[pid] 
                                    \*IF \A prevMsg \in prevDlvrs[msg.sendId] : prevMsg \in prevDlvrs[pid]
                                    THEN 
                                        /\ CB(msg.content,pid)
                                        /\ prevDlvrs' = [prevDlvrs EXCEPT ![pid] = @ \cup {msg}]
                                        \*/\ rbQ' = [rbQ EXCEPT ![pid] = Tail(@)]
                                        \*/\ UNCHANGED <<rcQ,deliveredSet,seqNoQ,bQ,crashed,procProcSeqSnd,procProcSeqRcv,suspects,rbQ>>
                                        /\ UNCHANGED <<suspects>>
                                    ELSE 
                                        /\ suspects' = [suspects EXCEPT ![pid] = @ \cup {msg.content.sendId}]
                                        \*/\ rbQ' = [rbQ EXCEPT ![pid] = Tail(@)]
                                        \*/\ UNCHANGED <<rcQ,deliveredSet,seqNoQ,bQ,crashed,procProcSeqSnd,procProcSeqRcv,prevDlvrs,causalDelivered,rbQ>>
                                        /\ UNCHANGED <<prevDlvrs,causalDelivered>> 
                                ELSE 
                                   UNCHANGED <<prevDlvrs,causalDelivered,suspects>>   *)         

myCallBackForRB(m,p) ==   /\ Debug("Delivered by RB", 2) 
                          /\ Debug(m, 1) 
                          /\ rbQ' = [rbQ EXCEPT ![p] = Append(@,m)]
                          \*/\ CADeliver(myCallBackForCausal, p)
                          \*/\ CADeliver2(myCallBackForCausal, p, m)
                                           
Next ==  \E pid \in processes: 
             \/ /\ MessageQueue[pid] # <<>>
                /\ CABroadcast(Head(MessageQueue[pid]),pid)
                \*/\ Broadcast(Head(MessageQueue[pid]),pid)
                /\ MessageQueue' = [MessageQueue EXCEPT ![pid] = Tail(@)] 
             \/ /\ Deliver(myCallBackForRB, pid)
                /\ UNCHANGED<<MessageQueue,prevDlvrs,causalDelivered,suspects>> 
             \/ /\ CADeliver(myCallBackForCausal, pid)
                /\ UNCHANGED<<MessageQueue>> 

state == <<rcQ, rbQ, bQ, crashed, seqNoQ, deliveredSet>>
             
NoCreationFIFO == (\A pid, bPid \in processes: \A msg \in Message:
                                ([content |->  msg, sendId |-> bPid] \in deliveredSet[pid]) =>  msg \in bQ[bPid])
                                
NoCreationCausal == (\A pid, bPid \in processes: \A msg \in Message:
                        ([content |->  msg, sendId |-> bPid] \in causalDelivered[pid]) =>  msg \in bQ[bPid])

BasicValidityFIFO ==  (\A pi \in processes:
                        \A pj \in processes\crashedProc:
                          \A m \in Message:
                             (m \in bQ[pi]) ~> ([content |->  m, sendId |-> pi] \in deliveredSet[pj]))
                             
BasicValidityCausal ==  (\A pi \in processes:
                        \A pj \in processes\crashedProc:
                          \A m \in Message:
                             (m \in bQ[pi]) ~> ([content |->  m, sendId |-> pi] \in causalDelivered[pj]))
                             
AgreementFIFO ==  (\A bp, pi,pj \in processes\crashedProc : 
                 \A m \in Message:
                    ([content |->  m, sendId |-> bp] \in deliveredSet[pi]) ~> ([content |->  m, sendId |-> bp]  \in deliveredSet[pj]) )      
                    
AgreementCausal ==  (\A bp, pi,pj \in processes\crashedProc : 
                 \A m \in Message:
                    ([content |->  m, sendId |-> bp] \in causalDelivered[pi]) ~> ([content |->  m, sendId |-> bp]  \in causalDelivered[pj]) )                       

UniformAgreementFIFO ==  (\A bp, pi,pj \in processes : 
                 \A m \in Message:
                    ([content |->  m, sendId |-> bp] \in deliveredSet[pi]) ~> ([content |->  m, sendId |-> bp]  \in deliveredSet[pj]) ) 
                    
UniformAgreementCausal ==  (\A bp, pi,pj \in processes : 
                 \A m \in Message:
                    ([content |->  m, sendId |-> bp] \in causalDelivered[pi]) ~> ([content |->  m, sendId |-> bp]  \in causalDelivered[pj]) )                       
                      


(*FIFOProperty == (\A mi \in Message: \A pi,pj \in processes\crashedProc: 
                        [content |-> mi, sendId |-> pi] \in deliveredSet[pj] => \A mj \in 0..mi: [content |-> mj, sendId |-> pi] \in deliveredSet[pj])

UniformFIFOProperty == (\A mi \in Message: \A pi,pj \in processes: 
                        [content |-> mi, sendId |-> pi] \in deliveredSet[pj] => \A mj \in 0..mi: [content |-> mj, sendId |-> pi] \in deliveredSet[pj])
            
*)                                         
Liveness ==   \A pid \in processes,m \in Message : 
                                WF_state(\/ CABroadcast(m,pid) 
                                         \*\/ Broadcast(m,pid) 
                                         \/ Deliver(myCallBackForRB,pid)
                                         \/ CADeliver(myCallBackForCausal, pid))
                                         \*\/ CADeliver2(myCallBackForCausal, pid, m))
           
RBSpec ==   /\ Init 
            /\ [][Next]_<<rcQ,bQ,rbQ,seqNoQ,deliveredSet,crashed,procProcSeqSnd,procProcSeqRcv,MessageQueue,prevDlvrs,suspects,causalDelivered>>
            /\ Liveness
=============================================================================

=============================================================================
\* Modification History
\* Last modified Tue Apr 29 08:33:43 EDT 2014 by Suvidha
\* Created Sun Apr 27 16:37:37 EDT 2014 by Suvidha
