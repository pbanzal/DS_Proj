---- MODULE MC ----
EXTENDS RBSF, TLC

\* CONSTANT definitions @modelParameterConstants:0processes
const_139852998607070000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1Message
const_139852998608171000 == 
{"M1"}
----

\* CONSTANT definitions @modelParameterConstants:2crashedProc
const_139852998609272000 == 
{}
----

\* INIT definition @modelBehaviorInit:0
init_139852998610373000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_139852998611474000 ==
[Next]_<<rcQ,rbQ,seqNoQ,deliveredSet,bQ,crashed>>
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_139852998612575000 ==
NoCreation
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_139852998613576000 ==
BasicValidityv1
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_139852998614677000 ==
Agreement
----
=============================================================================
\* Modification History
\* Created Sat Apr 26 12:33:06 EDT 2014 by praseem
