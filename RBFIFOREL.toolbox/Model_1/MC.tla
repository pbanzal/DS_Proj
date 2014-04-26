---- MODULE MC ----
EXTENDS RBFIFOREL, TLC

\* CONSTANT definitions @modelParameterConstants:0crashedProc
const_1398551707836259000 == 
{2}
----

\* CONSTANT definitions @modelParameterConstants:1processes
const_1398551707847260000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:2Message
const_1398551707858261000 == 
{0,1}
----

\* INIT definition @modelBehaviorInit:0
init_1398551707869262000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1398551707880263000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1398551707891264000 ==
FIFOProperty
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1398551707902265000 ==
NoCreation
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1398551707913266000 ==
Agreement
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1398551707924267000 ==
BasicValidityv1
----
=============================================================================
\* Modification History
\* Created Sat Apr 26 18:35:07 EDT 2014 by praseem
