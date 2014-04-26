---- MODULE MC ----
EXTENDS RBSF, TLC

\* CONSTANT definitions @modelParameterConstants:0processes
const_1398461290125527000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1Message
const_1398461290136528000 == 
{"M1"}
----

\* CONSTANT definitions @modelParameterConstants:2crashedProc
const_1398461290147529000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:3qLen
const_1398461290158530000 == 
0
----

\* INIT definition @modelBehaviorInit:0
init_1398461290169531000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1398461290180532000 ==
[Next]_<<rcQ,rbQ,seqNoQ,deliveredSet,bQ,crashed>>
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1398461290191533000 ==
TotalLiveness
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1398461290202534000 ==
BasicValidityv1
----
=============================================================================
\* Modification History
\* Created Fri Apr 25 17:28:10 EDT 2014 by praseem
