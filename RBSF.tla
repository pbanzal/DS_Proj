-------------------------------- MODULE RBSF --------------------------------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC

CONSTANTS 
    Message, 
    processes
    

VARIABLES 
     processMap
     

RBMessage == [content: Message, sendId : processes, seqNo: Nat]
RMessage == [content: RBMessage]

Send(p, msg) == \*/\ msg \in Message
                /\ Print("StartSEnd",TRUE)
                /\ Print(processMap[p].rcvQ,TRUE)
                /\ Print(msg,TRUE)
                /\ processMap' = [processMap EXCEPT ![p].rcvQ = Append(@, [content |-> msg])]
                /\ Print("DoneSEnd",TRUE)
                   
Recv(CB(_), p) ==  /\ processMap[p].rcvQ # <<>>
                         /\ CB(Head(processMap[p].rcvQ).content)
                         /\ processMap' = [processMap EXCEPT ![p].rcvQ = Tail(@)]

InitProcesses == processMap = [p \in processes |-> [rcvQ |-> <<>>, id |-> p, seqNo |-> 0, rbBag |-> {}]]  
                 
init == InitProcesses


myCallBackForRC(m) == Print(m, TRUE)
                           
NextForRC == /\ \E pid \in processes:
                \/ \E m \in Message : Send(pid,m)
                \/ Recv(myCallBackForRC,pid)
                
MyTestRC == init /\ [][NextForRC]_<<processMap>>

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
\* Last modified Mon Apr 21 20:25:23 EDT 2014 by Suvidha
\* Created Mon Apr 21 17:38:12 EDT 2014 by Suvidha
