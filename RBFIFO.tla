-------------------------------- MODULE RBFIFO --------------------------------
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
     deliveredSet

RBMessage == [content: Message, sendId : processes]\*, seqNo:{0}]
RMessage == [content : RBMessage, sendId: processes, seqNo: Nat]

Debug(msg,level) == IF level > 1 THEN Print(msg, TRUE) ELSE TRUE

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
        
Perms == Permutations(rcQ)

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
                                            /\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> [content |->  msg, sendId |-> pid], sendId |-> pid, seqNo |-> procProcSeqSnd[pid][p]]}]
                                            \*/\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid THEN IF pj = p THEN procProcSeqSnd[pi][pj] + 1 ELSE procProcSeqSnd[pi][pj] ELSE procProcSeqSnd[pi][pj]]]
                                            /\ procProcSeqSnd' = [procProcSeqSnd EXCEPT ![pid][p] = @ + 1]
                                   ELSE 
                                        /\ rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid], sendId |-> pid, seqNo |-> procProcSeqSnd[pid][p]]}]
                                        /\ procProcSeqSnd' = [pi \in processes |-> [pj \in processes |-> IF pi = pid THEN procProcSeqSnd[pi][pj] + 1 ELSE procProcSeqSnd[pi][pj]]]   
                                /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {msg} ]           
                            ELSE
                                /\ UNCHANGED <<bQ,rcQ,seqNoQ,procProcSeqSnd>>
                        /\ UNCHANGED <<rbQ,deliveredSet,crashed,procProcSeqRcv>>
               
Deliver(CB(_,_), pid) ==    /\ Debug("START Deliver............."\cup pid, 1)
                            /\ pid \in processes
                            /\ LET newCB(currMsg) ==  /\    IF currMsg.content \notin deliveredSet[pid] THEN
                                                                /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg.content}]
                                                                /\  IF currMsg.content.sendId # pid THEN 
                                                                        /\ rcQ' = [dstP \in processes |-> 
                                                                                        IF dstP # pid THEN 
                                                                                            rcQ[dstP] \cup {[content |-> currMsg.content, sendId |-> pid, seqNo |-> procProcSeqSnd[pid][dstP]]}
                                                                                        ELSE 
                                                                                            rcQ[pid]  \ {currMsg}]
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
                                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ,crashed,procProcSeqSnd>>
                                                                /\ CB(currMsg.content.content,pid) 
                                                            ELSE 
                                                                \* Remove frm rcQ 
                                                                /\ Debug("ELSE PART", 1)
                                                                /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                                /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed,procProcSeqSnd>>
                               IN   /\ rcQ[pid] # {}
                                    /\  IF crashed[pid] = FALSE THEN 
                                            LET elem == CHOOSE x \in rcQ[pid] : x.seqNo = procProcSeqRcv[pid][x.sendId]
                                            IN  /\ newCB(elem)
                                                /\ procProcSeqRcv' = [procProcSeqRcv EXCEPT ![pid][elem.sendId] = @ + 1]
                                        ELSE 
                                            LET elem == CHOOSE x \in rcQ[pid] : TRUE
                                            IN  /\ newCB(elem)
                                                /\ UNCHANGED <<procProcSeqRcv>>
                             
myCallBackForRB(m,p) ==   /\ Debug("Delivered by RB", 1) 
                          /\ Debug(m, 1) 
                          \*/\ rbQ' = [rbQ  EXCEPT ![p] = Append(@,m)]
                                           
Next ==  \E pid \in processes: 
             \/ \E m \in Message : Broadcast(m,pid)
             \/ Deliver(myCallBackForRB, pid)

\*NoCreation == [](\A pid \in processes: \A msg \in deliveredSet[pid] : \E bPid \in processes : msg \in bQ[bPid])
             
state == <<rcQ, rbQ, bQ, crashed, seqNoQ, deliveredSet>>             
NoCreation == (\A pid, bPid \in processes: \A msg \in Message:
                                ([content |->  msg, sendId |-> bPid] \in deliveredSet[pid]) =>  msg \in bQ[bPid])
                             
BasicValidityv1 ==  (\A pi \in processes:
                        \A pj \in processes\crashedProc:
                          \A m \in Message:
                             (m \in bQ[pi]) ~> ([content |->  m, sendId |-> pi] \in deliveredSet[pj]))
                             
\* Agreement : If one correct process delivers a message m, then every correct process eventually delivers m.                             
Agreement ==  (\A bp, pi,pj \in processes\crashedProc : 
                 \A m \in Message:
                    ([content |->  m, sendId |-> bp] \in deliveredSet[pi]) ~> ([content |->  m, sendId |-> bp]  \in deliveredSet[pj]) )                       

FIFOProperty == (\A mi \in Message: \A pi,pj \in processes\crashedProc: 
                        [content |-> mi, sendId |-> pi] \in deliveredSet[pj] => \A mj \in 0..mi: [content |-> mj, sendId |-> pi] \in deliveredSet[pj])
            
                                         
Liveness ==   \A pid \in processes,m \in Message : \/ WF_state(Broadcast(m,pid) \/ Deliver(myCallBackForRB,pid))
\*\/ WF_state(Broadcast(pid,m)) 
\*\/ WF_state(Deliver(myCallBackForRB,pid))       
             
           
RBSpec ==   /\ Init 
            /\ [][Next]_<<rcQ,bQ,rbQ,seqNoQ,deliveredSet,crashed,procProcSeqSnd,procProcSeqRcv>>
            /\ Liveness
            
=============================================================================
