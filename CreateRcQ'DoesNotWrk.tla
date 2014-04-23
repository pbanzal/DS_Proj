----- MODULE r -------
EXTENDS  
    Naturals, 
    Sequences, 
    TLC,
    FiniteSets

CONSTANTS 
    Message, 
    processes
    
    

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
        
       
Send(p, msg) == rcQ'[p] = rcQ[p] \cup {[content |-> msg]}
                

Broadcast(msg, pid) ==  /\  Debug("_____________________________________START............."\cup pid,2)
                        /\ msg \in Message
                        /\ pid \in processes
                        /\ seqNoQ[pid] \leq 0
                        /\ seqNoQ' = [seqNoQ EXCEPT ![pid] = @+1]
                        /\ rcQ' \in [processes -> SUBSET RMessage]
                        
                        /\ Debug("Broadcast Start" \cup rcQ',2)
                        \*/\ rcQ' = [rcQ EXCEPT  ![pid] = rcQ[pid] \cup {[content |-> msg]}]
                      
                       
                        /\ \A p \in processes : Send(p,[content |->  msg, sendId |-> pid])\*, seqNo |-> seqNoQ[pid]])           
                        /\ Debug("Broadcast Done"\cup rcQ',2)
                       
                        /\ UNCHANGED <<rbQ,delSet>>
                       
NextForRB ==  \E pid \in processes:
              \/  \E m \in Message : Broadcast(m,pid)
               
               
             
RBSpec == Init /\ [][NextForRB]_<<rcQ,rbQ,seqNoQ,delSet>>



==========================

