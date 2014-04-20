------------------------------ MODULE ModProc ------------------------------
EXTENDS Naturals, Sequences

CONSTANT RMessage, RBMessage
 
Process == [id: Nat, seqNoRB: Nat, inQueue: Seq(RMessage), rbQueue: Seq(RBMessage)]
=============================================================================

