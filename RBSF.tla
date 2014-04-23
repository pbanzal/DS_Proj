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
     rcQ,rbQ,seqNoQ,delSet
     

RBMessage == [content: Message, sendId : processes]\*, seqNo:{0}]
RMessage == [content: RBMessage]
RCMessage == [content : Message]


Debug(msg,level) == IF level > 1 THEN Print(msg, TRUE) ELSE  TRUE

Init == /\ rcQ = [p \in processes |-> {}]
        /\ rbQ = [p \in processes |-> <<>>]
        /\ seqNoQ = [p \in processes |-> 0]
        /\ delSet = [p \in processes |-> {}]   
        
Perms == Permutations(rcQ)
       
       
Send(p, msg) == \*/\ msg \in Message
                \*/\ Print("StartSEnd",TRUE)
                \*/\ rcQ' \in [processes -> SUBSET RMessage]
                \*/\ Print(msg,TRUE)
                /\ rcQ'[p] = rcQ[p] \cup {[content |-> msg]}
                
                \*/\ Print("DoneSEnd",TRUE)
               
Forward(p, msg) ==  /\ Debug("Forward Start", 1)
                    \* /\ msg \in RBMessage
                    \*/\ \A dstP \in processes\{p}: Send(dstP, msg)   
                    /\ Debug("Forward End", 1)
                   
Recv(CB(_), p) ==  /\ rcQ[p] # {}
                   /\ LET elem == CHOOSE x \in rcQ[p] : TRUE IN
                        /\ CB(elem.content)
                        /\ rcQ'[p] = rcQ[p]\{elem}
                        
                        
myCallBackForRC(m) == /\ Debug("Received by Channel", 1)
                           
NextForRC == /\ rcQ' \in [processes -> SUBSET RCMessage]
             /\ \E pid \in processes:
                \/ \E m \in Message : Send(pid,m)
                \/ Recv(myCallBackForRC,pid)
             /\ UNCHANGED <<rbQ,seqNoQ,delSet>>
                
MyTestRC == Init /\ [][NextForRC]_<<rbQ,seqNoQ,delSet>>
        
Broadcast(msg, pid) ==  /\ Debug("_____________________________________START............."\cup pid,2)
                        /\ msg \in Message
                        /\ pid \in processes
                        /\ seqNoQ[pid] \leq 0
                        /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @+1]
                        /\ Debug("Broadcast Start" \cup rcQ,2)
                        /\ rcQ' \in [processes -> SUBSET RMessage]
                        
                        /\ \A p \in processes : Send(p,[content |->  msg, sendId |-> pid])\*, seqNo |-> seqNoQ[pid]])           
                        /\ Debug("Broadcast Done" \cup rcQ \cup pid \cup rcQ',2)
                       
                        /\ UNCHANGED <<rbQ,delSet>>
                       
               
Deliver(CB(_), pid) ==  /\ Debug("_____________________________________START............."\cup pid,2)
                        /\ pid \in processes
                        /\ rcQ' \in [processes -> SUBSET RMessage]
                        /\ Debug("delset" \cup delSet,2)
                        /\ LET newCB(currMsg) ==    \*/\ currMsg \in RBMessage
                                                        IF currMsg \notin delSet[pid] THEN  
                                                        /\ delSet' = [delSet EXCEPT ![pid] = @ \cup {currMsg}]  \* Add to delivered set
                                                        \* Put in other processes rcQ (Forward) + Remove from current rcv
                                                        /\ Forward(pid,currMsg)
                                                        \*/\ Debug("Rmv from rcQ", 2)
                                                        /\ rcQ'[pid] = rcQ[pid]\{currMsg} 
                                                                        
                                                        \* Callback
                                                        /\ CB(currMsg.content) 
                                                        /\ UNCHANGED <<rbQ,seqNoQ>>
                                                    
                                                        ELSE 
                                                        \* Remove frm rcQ 
                                                        /\ Debug("ELSE PART", 2)
                                                        /\ rcQ'[pid] = rcQ[pid]\{currMsg}
                                                        /\ UNCHANGED <<delSet,rbQ,seqNoQ>>
                               IN   /\ rcQ[pid] # {}
                                
                                    /\ LET elem == CHOOSE x \in rcQ[pid] : TRUE IN
                                        /\ Debug("String chosen" \cup elem,1)
                                        /\ Debug(elem,1)
                                   
                                        /\ newCB(elem)
                                        \*/\ newCB(Head(rcQ[pid]))
                                        /\ Debug("rcq" \cup rcQ,2)
                                        /\ Debug("DELIVERED",2)

myCallBackForRB(m) ==   /\ Debug("Delivered by RB",2) 
                        /\ Debug(m, 2)                       

NextForRB ==  \E pid \in processes: 
                \/ \E m \in Message :
                  \/ Broadcast(m,pid)
                \/ Deliver(myCallBackForRB,pid)
               
             
RBSpec ==   /\ Init 
            /\ [][NextForRB]_<<rcQ,rbQ,seqNoQ,delSet>>

(*

(*Send(p, msg) == \*/\ msg \in Message
                /\ Print("StartSEnd",TRUE)
                /\ Print(processMap[p].rcvQ,TRUE)
                /\ Print(msg,TRUE)
                /\ processMap' = [processMap EXCEPT ![p].rcvQ = Append(@, [content |-> msg])]
                /\ Print("DoneSEnd",TRUE)
                   
Recv(CB(_), p) ==  /\ processMap[p].rcvQ # <<>>
                         /\ CB(Head(processMap[p].rcvQ).content)
                         /\ processMap' = [processMap EXCEPT ![p].rcvQ = Tail(@)]*)

(* /\ LET tmpQ == [p \in processes\{pid} |-> Append(rcQ[p], currMsg)] IN
                                                           /\ tmpQ = [tmpQ EXCEPT ![pid] ] = Tail(@)]
                                                           /\ rcQ' = tmpQ
                                                          *)      
myCallBackForRC(m) == Print(m, TRUE)
                           
NextForRC == /\ \E pid \in processes:
                \/ \E m \in Message : Send(pid,m)
                \/ Recv(myCallBackForRC,pid)
                
MyTestRC == init /\ [][NextForRC]_<<processMap>>*)

(*
Broadcast(msg, pid) == /\ msg \in Message
                       /\ pid \in processes
                       /\ Print("Broadcast Start",TRUE)
                       /\ 
                        processMap' = [p \in processes |-> [rcvQ |-> Append(processMap[p].rcvQ,
                                                                [content |-> [content |->  msg, sendId |-> processMap[pid].id, seqNo |-> processMap[pid].seqNo]]), 
                                                              id |-> p, 
                                                              seqNo |-> IF p =  pid THEN  processMap[p].seqNo + 1 ELSE processMap[p].seqNo, 
                                                              rbBag |-> {}]]  
                        \*/\ \A p \in processes: 
                        \*       Send(p, 
                        \*             [content |-> msg, sendId |-> processMap[pid].id, seqNo |-> processMap[pid].seqNo])
                        /\ Print("Broadcast Done",TRUE)
                        \*/\ processMap' = [processMap EXCEPT ![pid].seqNo = @ + 1]

Forward(p, msg) == \*/\ msg \in RBMessage
                   /\ \A dstP \in processes\{p}: Send(dstP, msg)
                        
Deliver(CB(_), pid) == /\ pid \in processes
                        /\ LET newCB(currMsg) == \*/\ currMsg \in RBMessage
                                                 /\ IF currMsg \notin processMap[pid].rbBag 
                                                    THEN  
                                                        \*/\ processMap' = [processMap EXCEPT ![pid].rbBag = @ \cup currMsg]
                                                        /\ Forward(pid, currMsg) 
                                                        /\ CB(currMsg.content)
                                                    ELSE 
                                                        UNCHANGED processMap
                           IN Recv(newCB,pid) 
                         /\ Print("DELIVERED",TRUE)
                           
myCallBackForRB(m) == Print(m, TRUE)

NextForRB == /\ \E pid \in processes:
                 \E m \in Message : Broadcast(m,pid)
               \/ Deliver(myCallBackForRB,pid)
 *)                          
=============================================================================
\* Modification History
\* Last modified Wed Apr 23 10:14:34 EDT 2014 by Suvidha
\* Created Mon Apr 21 17:38:12 EDT 2014 by Suvidha
