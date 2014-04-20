------------------------------ MODULE ModProc ------------------------------
EXTENDS Naturals, Sequences

CONSTANT RMessage
 
Process == [id: Nat, seqNoRB: Nat, inQueue: Seq(RMessage)] 
=============================================================================

