-------------------------------- MODULE RBSF --------------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC

CONSTANTS 
    Message, 
    processes
    

VARIABLES 
     rcQ,rbQ,seqNoQ,delSet,tmpQ
     

RBMessage == [content: Message, sendId : processes]\*, seqNo:1]
RMessage == [content: RBMessage]
aseq == Seq(RMessage)
                 
Init == \*/\ rcQ \ [p \in processes |-> <<>>]
        /\ rcQ \in [processes -> Seq(RMessage)]
        /\ rbQ = [p \in processes |-> <<>>]
        /\ seqNoQ = [p \in processes |-> 0]
        /\ delSet = [p \in processes |-> {}]
        /\ tmpQ = rcQ
       
        
(*Send(p, msg) == \*/\ msg \in Message
                /\ Print("StartSEnd",TRUE)
                
                /\ Print(msg,TRUE)
               \* /\ Print(Seq(RMessage), TRUE)
               \* /\ rcQ' \in [processes -> {Seq(RMessage)}]
                
               /\ rcQ'[p] =  Append(rcQ[p], [content |-> msg])
              \*  /\ \A p \in processes : VARIABLE tmpRcQ[p]*)
               (* /\ Print("DoneSEnd",TRUE)
                   
Recv(CB(_), p) ==  /\ processMap[p].rcvQ # <<>>
                         /\ CB(Head(processMap[p].rcvQ).content)
                         /\ processMap' = [processMap EXCEPT ![p].rcvQ = Tail(@)]*)
        
Broadcast(msg, pid) == /\ msg \in Message
                       /\ pid \in processes
                       \*/\ Print("Broadcast Start",TRUE)
                       /\ rcQ \in [processes -> Seq(RMessage)]
                      \*/\ \A p \in processes : tmpQ[p] =  Append(rcQ[p], [content |-> msg])
                       (*Send(p,[content |->  msg, 
                                                      sendId |-> pid])*)(*, 
                                                      seqNo |-> seqNoQ[pid]])    *)           
                       (*/\ rcQ' = [p \in processes |-> IF TRUE 
                                                      THEN Append(rcQ[p],  [content |->  msg, 
                                                                       sendId |-> pid, 
                                                                       seqNo |-> seqNoQ[pid]])
                                                       ELSE Append(rcQ[p], [content |->  msg, 
                                                                       sendId |-> pid, 
                                                                       seqNo |-> seqNoQ[pid]])]*)
                       \*/\ rcQ' = rcQ
                       /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @+1]
                       /\ UNCHANGED <<rbQ,delSet>>
                       \*/\ Print("Broadcast Done",TRUE)
 (*LET tmpQ1 == [pr \in processes |-> rcQ]
                                             IN 
                                                /\ Send(p,msg)
                                                /\ LET tmpQ2 == [rcvQ EXCEPT ![p] = locChannel] IN
                                                    tmpQ2 = [       *)                       
Deliver(CB(_), pid) == /\ pid \in processes
                       /\ LET newCB(currMsg) == /\ currMsg \in RBMessage
                                                /\ IF currMsg \notin delSet[pid]
                                                   THEN  
                                                    
                                                        \* Add to delivered set
                                                        /\ delSet' = [delSet EXCEPT ![pid] = @ \cup {currMsg}] 
                                                      
                                                       \* Put in other processes rcQ (Forward) + Remove from current rcQ
                                                       /\ rcQ' = [p \in processes |-> 
                                                                                IF p=pid 
                                                                                THEN 
                                                                                    Tail(rcQ[p])
                                                                                ELSE 
                                                                                    Append(rcQ[p], currMsg)]
                                                      
                                                       \* Callback
                                                        /\ CB(currMsg.content) 
                                                        /\ UNCHANGED <<rbQ,seqNoQ>>
                                                    
                                                    ELSE 
                                                        \* Remove frm rcQ 
                                                        /\ rcQ' = [rcQ EXCEPT ![pid] = Tail(@)] 
                                                        /\ UNCHANGED <<delSet,rbQ,seqNoQ>>
                           IN   /\ rcQ[pid] # <<>>
                                /\ newCB(Head(rcQ[pid]))
                                /\ Print("DELIVERED",TRUE)

myCallBackForRB(m) == Print(m, TRUE)                       

NextForRB ==  \E pid \in processes:
                 \/  \E m \in Message : Broadcast(m,pid)
               \* \/ Deliver(myCallBackForRB,pid)
             
RBSpec == Init /\ [][NextForRB]_<<rcQ,rbQ,seqNoQ,delSet>>

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
\* Last modified Tue Apr 22 20:31:57 EDT 2014 by Suvidha
\* Created Mon Apr 21 17:38:12 EDT 2014 by Suvidha
