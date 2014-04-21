---- MODULE MC ----
EXTENDS TestRC, TLC

\* CONSTANT definitions @modelParameterConstants:0ProcessId
const_1398032426790147000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:1Data
const_1398032426800148000 == 
{0}
----

\* INIT definition @modelBehaviorNoSpec:0
init_1398032426812149000 ==
FALSE/\Processes = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1398032426823150000 ==
FALSE/\Processes' = Processes
----
=============================================================================
\* Modification History
\* Created Sun Apr 20 18:20:26 EDT 2014 by praseem
