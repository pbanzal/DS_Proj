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

Broadcast(msg, pid) ==  \*/\ Debug("START Broadcast............."\cup pid, 1)
                        /\ msg \in Message
                        /\ pid \in processes
                        /\ Debug(Cardinality(bQ[pid]),2)
                        /\ Cardinality(bQ[pid]) \leq qLen
                        \*/\  IF msg \notin bQ[pid]
                        \*THEN
                        \*/\ Debug("Broadcast pid: " \cup pid \cup " msg: " \cup msg, 1)
                        /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @ + 1]
                        /\ IF crashed[pid] = {TRUE} THEN
                               \E p \in processes: 
                                    /\ crashed[p] = {FALSE}
                                    /\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]
                           ELSE 
                               rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]
                        /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {[content |-> [content |->  msg, sendId |-> pid, seqNo |-> seqNoQ[pid]]]}]         
                        \*/\ Debug("Broadcast Done" \cup rcQ \cup pid \cup rcQ', 1)
                        
                            
                        /\ UNCHANGED <<rbQ,deliveredSet,crashed>>
               
Deliver(CB(_,_), pid) ==  /\ rcQ[pid] # {}
                          
                          /\ pid \in processes
                          \* /\ rcQ' \in [processes -> SUBSET RMessage]
                          /\ IF crashed[pid] # {TRUE} THEN
                               LET newCB(currMsg) ==  \*IF currMsg \notin deliveredSet[pid] THEN
                                                            
                                                       
                                                     
                                                      /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg}]
                                                      
                                                      /\ rcQ' = [dstP \in processes |-> 
                                                                    IF dstP # pid
                                                                    THEN rcQ[dstP] \cup {currMsg}
                                                                    ELSE rcQ[pid]  \ {currMsg}]
                                                      /\ CB(currMsg.content.content,pid) 
                                                     
                                                            
                                                      \*ELSE 
                                                      \* Remove frm rcQ 
                                                      \*/\ Debug("ELSE PART", 1)
                                                      \*/\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                      \*/\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed>>
                               IN  LET elem == CHOOSE x \in rcQ[pid] : TRUE 
                                     IN             IF elem \notin deliveredSet[pid] THEN 
                                                       \*/\ rbQ' \in [processes -> SUBSET Message]
                                                        
                                                       /\ newCB(elem)
                                                       /\ UNCHANGED <<bQ,seqNoQ,crashed>>
                                                    ELSE   
                                                      
                                                       /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {elem}] 
                                                       /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ,crashed>>
                                         
                             ELSE UNCHANGED <<rcQ,rbQ,bQ,crashed,seqNoQ,deliveredSet>>            
                            
myCallBackForRB(m,pid) ==   /\ Debug(m, 1)  
                            /\ rbQ' = [rbQ EXCEPT ![pid] = @ \cup {m}]  
 
\*dummyAssertion == /\ \A p \in processes : \A m \in deliveredSet[p] :  m \notin rcQ[p]                           
                                           
Next ==  /\ \E pid \in processes: 
             \/ \E m \in Message : Broadcast(m,pid)
             \/ Deliver(myCallBackForRB, pid)
             

\* Message delivered is message broadcast.             
NoCreation == \A pid \in processes: \A msg \in deliveredSet[pid] : msg \in bQ[pid]

\* Validity   : If pi and pj are correct then every message broadcast by pi is eventually delivered by pj.
BasicValidityv1 == \A pi \in processes\{crashed}:
                        \A pj \in processes\{crashed}, m \in bQ[pi] : (m \in bQ[pi]) ~> (m \in deliveredSet[pj])

Validityv2 == \A pi,pj \in processes\{crashed} : 
                \A m \in bQ[pi] : SF_state(Deliver(myCallBackForRB,pj)) /\ SF_state(myCallBackForRB(m,pj))
                
(*Enable Property for Validity -  Every broadcast(m) of correct pi enables a receive(m) of all correct pj which 
                                                                        further enables Deliver which further enables callback.*)

\*EnableProperty == \A pi,pj \in processes\{crashed} : (bQ[pi] # {}) ~> (rcQ[pj] # {})
EnableRcv(pi) == rcQ[pi] # {}

\* Agreement : If one correct process delivers a message m, then every correct process eventually delivers m. 
\*Agreement == \E pi \in processes\{crashed} : <><<Deliver(myCallBackForRB, pi)>>_state ~> \A pj \in processes\{crashed \cup {pi}} : <><<Deliver(myCallBackForRB, pj)>>_state
Agreement == \A pi,pj \in processes\{crashed} : 
                \A m \in deliveredSet[pi] :
                  \/ m \in deliveredSet[pj]
                  \/ <><<myCallBackForRB(m, pj)>>_state
    
TotalLiveness == /\ NoCreation 
                 \*/\ EnableProperty
                 /\ BasicValidityv1
                 /\ Validityv2
                 /\ []Agreement
            
RBSpec ==   /\ Init 
            /\ [][Next]_<<rcQ,rbQ,seqNoQ,deliveredSet,bQ,crashed>>
            /\ TotalLiveness
                        
=============================================================================