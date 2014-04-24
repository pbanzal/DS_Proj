-------------------------------- MODULE RBSF --------------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC,
    FiniteSets

CONSTANTS 
    Message, 
    processes,
    qLen
    

VARIABLES 
     rcQ,
     rbQ,
     bQ,
     seqNoQ,
     deliveredSet
     

RBMessage == [content: Message, sendId : processes]\*, seqNo:{0}]
RMessage == [content: RBMessage]
RCMessage == [content : Message]


Debug(msg,level) == IF level > 1 THEN Print(msg, TRUE) ELSE TRUE

Init == /\ rcQ = [p \in processes |-> {}]
        /\ bQ = [p \in processes |-> {}]
        /\ rbQ = [p \in processes |-> <<>>]
        /\ seqNoQ = [p \in processes |-> 0]
        /\ deliveredSet = [p \in processes |-> {}]   
        
Perms == Permutations(rcQ)

(* ---------- Reliable Channel -------------- *)
       
Send(p, msg) == \*/\ msg \in Message
                \*/\ Print("StartSEnd",TRUE)
                \*/\ rcQ' \in [processes -> SUBSET RMessage]
                \*/\ Print(msg,TRUE)
                \*/\ rcQ' = [rcQ EXCEPT ![p] = @ \cup {[content |-> msg]}]
                /\ rcQ'[p] = rcQ[p] \cup {[content |-> msg]}
                
Recv(CB(_), p) ==  /\ rcQ[p] # {}
                   /\ LET elem == CHOOSE x \in rcQ[p] : TRUE IN
                        /\ CB(elem.content)
                        /\ rcQ' = [rcQ EXCEPT ![p] = @ \ {elem} ]
                        \*/\ rcQ'[p] = rcQ[p]\{elem}
                        
myCallBackForRC(m) == /\ Debug("Received by Channel", 1)
                           
NextForRC == /\ rcQ' \in [processes -> SUBSET RCMessage]
             /\ \E pid \in processes:
                \/ \E m \in Message : Send(pid,m)
                \/ Recv(myCallBackForRC,pid)
             /\ UNCHANGED <<rbQ,seqNoQ,deliveredSet>>
                
MyTestRC == Init /\ [][NextForRC]_<<rbQ,seqNoQ,deliveredSet>>
        
(* -------- Broadcast ------------- *)

Broadcast(msg, pid) ==  /\ Debug("START Broadcast............."\cup pid, 1)
                        /\ msg \in Message
                        /\ pid \in processes
                        \* /\ seqNoQ[pid] \leq 0
                        /\  IF msg \notin bQ[pid]
                            THEN
                                /\ Debug("Broadcast pid: " \cup pid \cup " msg: " \cup msg, 1)
                                /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @ + 1]
                                /\ rcQ' = [p \in processes |-> rcQ[p] \cup {[content |-> [content |->  msg, sendId |-> pid]]}] \*, seqNo |-> seqNoQ[pid]])
                                /\ bQ' = [bQ EXCEPT ![pid] = @ \cup {msg} ]           
                                /\ Debug("Broadcast Done" \cup rcQ \cup pid \cup rcQ', 1)
                                /\ rcQ' \in [processes -> SUBSET RMessage]
                                /\ UNCHANGED <<rbQ,deliveredSet>>
                            ELSE
                                /\ UNCHANGED <<rbQ,bQ,rcQ,deliveredSet,seqNoQ>>
               
Forward(p, msg) ==  /\ Debug("Forward Start", 1)
                    \* /\ msg \in RBMessage
                    /\ \A dstP \in processes\{p}: rcQ'[p] = rcQ[p] \cup {msg}   
                    /\ Debug("Forward End", 1)
                                          
               
Deliver(CB(_), pid) ==  /\ Debug("START Deliver............."\cup pid, 1)
                        /\ pid \in processes
                        \* /\ rcQ' \in [processes -> SUBSET RMessage]
                        /\ LET newCB(currMsg) ==    \*/\ currMsg \in RBMessage
                                                        IF currMsg \notin deliveredSet[pid] 
                                                        THEN
                                                        /\ Debug("deliveredSet" \cup deliveredSet, 1)  
                                                        /\ deliveredSet' = [deliveredSet EXCEPT ![pid] = @ \cup {currMsg}]  \* Add to delivered set
                                                        \* Put in other processes rcQ (Forward) + Remove from current rcv
                                                        (*/\ dstP \in processes: 
                                                                IF dstP # pid
                                                                \*THEN rcQ[dstP] = rcQ[dstP] \cup {currMsg}
                                                                \*ELSE rcQ[pid] = rcQ[pid] \ {currMsg}
                                                                THEN rcQ' = [rcQ EXCEPT ![dstP]= @ \cup {currMsg}]
                                                                ELSE rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}]
                                                         *)
                                                        /\ rcQ' = [dstP \in processes |-> 
                                                                                IF dstP # pid
                                                                                THEN rcQ[dstP] \cup {currMsg}
                                                                                ELSE rcQ[pid]  \ {currMsg}]
                                                        \* /\ Forward(pid,currMsg)
                                                        \*/\ Debug("Rmv from rcQ", 2)
                                                        \*/\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                                        
                                                        \* Callback
                                                        /\ CB(currMsg.content) 
                                                        /\ UNCHANGED <<rbQ,bQ,seqNoQ>>
                                                    
                                                        ELSE 
                                                        \* Remove frm rcQ 
                                                        /\ Debug("ELSE PART", 1)
                                                        /\ rcQ' = [rcQ EXCEPT ![pid] = @ \ {currMsg}] 
                                                        /\ UNCHANGED <<deliveredSet,rbQ,seqNoQ,bQ>>
                               IN   /\ rcQ[pid] # {}
                                
                                    /\ LET elem == CHOOSE x \in rcQ[pid] : TRUE IN
                                        /\ Debug("String chosen" \cup elem,1)
                                        /\ Debug(elem,1)
                                   
                                        /\ newCB(elem)
                                        \*/\ newCB(Head(rcQ[pid]))
                                        /\ Debug("rcq" \cup rcQ, 1)
                                        /\ Debug("DELIVERED", 2)

myCallBackForRB(m) ==   /\ Debug("Delivered by RB", 2) 
                        /\ Debug(m, 2)    
                                           
NextForRB ==  \E pid \in processes: 
                \/ \E m \in Message : Broadcast(m,pid)
                \/ Deliver(myCallBackForRB, pid)
               
             
RBSpec ==   /\ Init 
            /\ [][NextForRB]_<<rcQ,rbQ,seqNoQ,deliveredSet>>
                        
=============================================================================