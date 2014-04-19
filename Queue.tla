------------------------------- MODULE Queue -------------------------------
EXTENDS Sequences
CONSTANT Message
VARIABLES in, out, q

NullMsg == CHOOSE msg : msg \notin Message 

Init == q = <<>> /\ in = NullMsg /\ out = NullMsg 

Enq(m) ==   /\ in # m
            /\ 

=============================================================================
\* Modification History
\* Last modified Sat Apr 19 15:09:56 EDT 2014 by praseem
\* Created Sat Apr 19 15:04:34 EDT 2014 by praseem
