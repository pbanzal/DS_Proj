---- MODULE MC ----
EXTENDS RBFIFO, TLC

\* CONSTANT definitions @modelParameterConstants:0crashedProc
const_1398548439867326000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:1processes
const_1398548439878327000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2Message
const_1398548439889328000 == 
{1}
----

\* INIT definition @modelBehaviorInit:0
init_1398548439901329000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1398548439912330000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1398548439922331000 ==
FIFOProperty
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1398548439933332000 ==
NoCreation
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1398548439945333000 ==
Agreement
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1398548439956334000 ==
BasicValidityv1
----
=============================================================================
\* Modification History
\* Created Sat Apr 26 17:40:39 EDT 2014 by praseem
