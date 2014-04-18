---- MODULE MC ----
EXTENDS RB, TLC

\* CONSTANT definitions @modelParameterConstants:0Domain
const_1397858332124210000 == 
{"A", "B", "C", "D"}
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1397858332135211000 == 
{1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:2Messages
const_1397858332146212000 == 
{1,2,3,4,5}
----

\* INIT definition @modelBehaviorInit:0
init_1397858332157213000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1397858332168214000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1397858332179215000 ==
RB
----
=============================================================================
\* Modification History
\* Created Fri Apr 18 17:58:52 EDT 2014 by praseem
