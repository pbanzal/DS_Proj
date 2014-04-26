-------------------------------- MODULE RBSF --------------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC,
    FiniteSets

CONSTANTS 
    Message, 
    processes,
    crashedProc,
    qLen

VARIABLES 
     rcQ,
     rbQ,
     bQ,
     crashed,
     seqNoQ,
     deliveredSet

state == <<rcQ, rbQ, bQ, crashed, seqNoQ, deliveredSet>>

RBMessage == [content: Message, sendId : processes, seqNo:(0 .. qLen)]
RMessage == [content: RBMessage]
RCMessage == [content : Message]

Debug(msg,level) == IF level > 1 THEN Print(msg, TRUE) ELSE TRUE

Init == /\ rcQ = [p \in processes |-> {}]
        /\ bQ = [p \in processes |-> {}]
        /\ crashed = [p \in processes |-> IF p \in crashedProc 
                                          THEN {TRUE}
                                          ELSE {FALSE}]
        /\ rbQ = [p \in processes |-> {}]
        /\ seqNoQ = [p \in processes |-> 0]
        /\ deliveredSet = [p \in processes |-> {}]   
        
Perms == Permutations(rcQ)

(* -------- Broadcast ------------- *)

Broadcast(msg, pid) ==  /\ msg \in Message
                        /\ pid \in processes
                        /\ Debug(Cardinality(bQ[pid]),2)
                        /\ Cardinality(bQ[pid]) \leq qLen
                        /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @ + 1]
                        /\ IF crashed[pid] = {TRUE} THEN
                               \E p \in processes: 
                                    /\ crashed[p] = {FALSE}
                                    /\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]
                           ELSE 
                               rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]
                        /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]         
                        /\ UNCHANGED <<rbQ,deliveredSet,crashed>>
               
Deliver(CB(_,_), pid) ==  /\ rcQ[pid] # {}
                          /\ pid \in processes
                          /\ IF crashed[pid] # {TRUE} THEN
                               LET newCB(currMsg) ==  /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg}]
                                                      /\ rcQ' = [dstP \in processes |-> 
                                                                    IF dstP # pid
                                                                    THEN rcQ[dstP] \cup {currMsg}
                                                                    ELSE rcQ[pid]  \ {currMsg}]
                                                      /\ CB(currMsg.content.content,pid) 
                               IN  
                                   LET elem == CHOOSE x \in rcQ[pid] : TRUE
                                   IN
                                        IF elem \notin deliveredSet[pid] THEN 
                                           /\ newCB(elem)
                                           /\ UNCHANGED <<bQ,seqNoQ,crashed>>
                                        ELSE   
                                           /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {elem}] 
                                           /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed>>
                             ELSE UNCHANGED <<rcQ,rbQ,bQ,crashed,seqNoQ,deliveredSet>>            
                            
myCallBackForRB(m,pid) ==   /\ Debug(m, 1)  
                            /\ rbQ' = [rbQ EXCEPT ![pid] = @ \cup {m}]
                              
isDelivered(m,pid) == /\ m \in deliveredSet[pid]
\*dummyAssertion == /\ \A p \in processes : \A m \in deliveredSet[p] :  m \notin rcQ[p]                           
                                           
Next ==  /\ \E pid \in processes: 
             \/ \E m \in Message : Broadcast(m,pid)
             \/ Deliver(myCallBackForRB, pid)
             
\* Message delivered is message broadcast.             
NoCreation == (\A pDel \in processes: \A msg \in deliveredSet[pDel]: \E pBrd \in processes: msg \in bQ[pBrd])

\* Validity   : If pi and pj are correct then every message broadcast by pi is eventually delivered by pj.
BasicValidityv1 == \A pi,pj \in processes\crashedProc: \A m \in bQ[pi]: (Broadcast(m, pi) /\ isDelivered(m,pj))
                                                         
\*Validityv2 == \A pi,pj \in processes\crashedProc : 
\*                \A m \in bQ[pi] : SF_state(Deliver(myCallBackForRB,pj)) /\ SF_state(myCallBackForRB(m,pj))
                
(*Enable Property for Validity -  Every broadcast(m) of correct pi enables a receive(m) of all correct pj which 
                                  further enables Deliver which further enables callback.*)

\*EnableProperty == \A pi,pj \in processes\crashedProc : (bQ[pi] # {}) ~> (rcQ[pj] # {})
EnableRcv(pi) == rcQ[pi] # {}

\* Agreement : If one correct process delivers a message m, then every correct process eventually delivers m. 
\* Agreement == \E pi \in processes\crashedProc : <><<Deliver(myCallBackForRB, pi)>>_state ~> \A pj \in processes\{crashedProc \cup {pi}} : <><<Deliver(myCallBackForRB, pj)>>_state

Agreement == \A pi,pj \in processes\crashedProc : 
                \A m \in deliveredSet[pi] :
                  \/ m \in deliveredSet[pj]
                  \/ <><<myCallBackForRB(m, pj)>>_state
    
TotalLiveness == /\ NoCreation 
                 \*/\ EnableProperty
                 \*/\ Validityv2
                 \*/\ []Agreement
            
RBSpec ==   /\ Init 
            /\ [][Next]_<<rcQ,rbQ,seqNoQ,deliveredSet,bQ,crashed>>
            /\ TotalLiveness
                        
=============================================================================