---- MODULE MC ----
EXTENDS RBFIFO, TLC

\* CONSTANT definitions @modelParameterConstants:0crashedProc
const_1398551363617250000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:1processes
const_1398551363628251000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2Message
const_1398551363639252000 == 
{1}
----

\* INIT definition @modelBehaviorInit:0
init_1398551363651253000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1398551363662254000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1398551363673255000 ==
FIFOProperty
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1398551363684256000 ==
NoCreation
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1398551363695257000 ==
Agreement
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1398551363706258000 ==
BasicValidityv1
----
=============================================================================
\* Modification History
\* Created Sat Apr 26 18:29:23 EDT 2014 by praseem
