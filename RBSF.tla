-------------------------------- MODULE RBSF --------------------------------
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
     deliveredSet

RBMessage == [content: Message, sendId : processes]\*, seqNo:{0}]
RMessage == [content: RBMessage]
RCMessage == [content : Message]

Debug(msg,level) == IF level > 1 THEN Print(msg, TRUE) ELSE TRUE

Init == /\ rcQ = [p \in processes |-> {}]
        /\ bQ = [p \in processes |-> {}]
        /\ crashed = [p \in processes |-> IF p \in crashedProc 
                                          THEN {TRUE}
                                          ELSE {FALSE}]
        /\ rbQ = [p \in processes |-> <<>>]
        /\ seqNoQ = [p \in processes |-> 0]
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
                                /\ IF crashed[pid] = {TRUE} 
                                   THEN
                                        \E p \in processes: 
                                            /\ crashed[p] = {FALSE}
                                            /\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> [content |->  msg, sendId |-> pid]]}] \*, seqNo |-> seqNoQ[pid]])
                                   ELSE 
                                        rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid]]}] \*, seqNo |-> seqNoQ[pid]])
                                /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {msg} ]           
                                /\ Debug("Broadcast Done" \cup rcQ \cup pid \cup rcQ', 1)
                                /\ rcQ' \in [processes -> SUBSET RMessage]
                            ELSE
                                /\ UNCHANGED <<bQ,rcQ,seqNoQ>>
                        /\ UNCHANGED <<rbQ,deliveredSet,crashed>>
               
Deliver(CB(_,_), pid) ==  /\ Debug("START Deliver............."\cup pid, 1)
                        /\ pid \in processes
                        \* /\ rcQ' \in [processes -> SUBSET RMessage]
                        /\  IF crashed[pid] # {TRUE}
                            THEN
                            /\ LET newCB(currMsg)== IF currMsg \notin deliveredSet[pid] 
                                                    THEN
                                                    /\ Debug("deliveredSet" \cup deliveredSet, 1)  
                                                    /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg}]
                                                    /\ rcQ' = [dstP \in processes |-> 
                                                                    IF dstP # pid
                                                                    THEN rcQ[dstP] \cup {currMsg}
                                                                    ELSE rcQ[pid]  \ {currMsg}]
                                                    /\ CB(currMsg.content.content,pid) 
                                                    /\ UNCHANGED <<bQ,seqNoQ,crashed>>
                                                    ELSE 
                                                    \* Remove frm rcQ 
                                                    /\ Debug("ELSE PART", 1)
                                                    /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                    /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed>>
                               IN /\ rcQ[pid] # {}
                                  /\ LET elem == CHOOSE x \in rcQ[pid] : TRUE 
                                     IN   /\ newCB(elem)
                                          \*/\ newCB(Head(rcQ[pid]))
                            ELSE
                            UNCHANGED <<rcQ,rbQ,bQ,crashed,seqNoQ,deliveredSet>>
                            
myCallBackForRB(m,p) ==   /\ Debug("Delivered by RB", 1) 
                        /\ Debug(m, 1) 
                        /\ rbQ' = [rbQ  EXCEPT ![p] = Append(@,m)]
                                           
Next ==  \E pid \in processes: 
             \/ \E m \in Message : Broadcast(m,pid)
             \/ Deliver(myCallBackForRB, pid)

\*NoCreation == [](\A pid \in processes: \A msg \in deliveredSet[pid] : \E bPid \in processes : msg \in bQ[bPid])
             
state == <<rcQ, rbQ, bQ, crashed, seqNoQ, deliveredSet>>             
NoCreation == [](\A pid \in processes: 
                    \A msg \in Message: 
                        ([content |-> [content |->  msg, sendId |-> pid]] \in deliveredSet[pid]) =>
                             \E bPid \in processes : msg \in bQ[bPid])
                             
BasicValidityv1 == []  (\A pi,pj \in processes:
                          \A m \in Message:
                             (m \in bQ[pi]) ~> ([content |-> [content |->  m, sendId |-> pi]] \in deliveredSet[pj]))
                             
(*Validityv2 == [] (\A pi,pj \in processes : 
                    \A m \in Message:
                        (m \in bQ[pi]) ~> (/\ SF_state(Deliver(myCallBackForRB,pj)) 
                                           /\ WF_state(myCallBackForRB(m,pj))))*)
                             
\* Agreement : If one correct process delivers a message m, then every correct process eventually delivers m.                             
Agreement == [] (\A bp, pi,pj \in processes\crashedProc : 
                 \A m \in Message:
                    ([content |-> [content |->  m, sendId |-> bp]] \in deliveredSet[pi]) ~> ([content |-> [content |->  m, sendId |-> bp]]  \in deliveredSet[pj]) )                       
                             

                         
Liveness ==   \A pid \in processes,m \in Message : \/ WF_state(Broadcast(pid,m) \/ Deliver(myCallBackForRB,pid))
\*\/ WF_state(Broadcast(pid,m)) 
\*                                                   \/ WF_state(Deliver(myCallBackForRB,pid))       
             
           
RBSpec ==   /\ Init 
            /\ [][Next]_<<rcQ,bQ,rbQ,seqNoQ,deliveredSet,crashed>>
            /\ Liveness
            
                        
=============================================================================
