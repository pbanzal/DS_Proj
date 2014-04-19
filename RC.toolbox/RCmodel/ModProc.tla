------------------------------ MODULE ModProc ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data
 
Process == [id: Nat, sendQueue: Seq(Data), inQueue: Seq(Data)]
=============================================================================
