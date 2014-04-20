---- MODULE MC ----
EXTENDS TestRC, TLC

\* CONSTANT definitions @modelParameterConstants:0ProcessId
const_1398029347400107000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:1Data
const_1398029347411108000 == 
{0}
----

\* INIT definition @modelBehaviorNoSpec:0
init_1398029347422109000 ==
FALSE/\rp = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1398029347433110000 ==
FALSE/\rp' = rp
----
=============================================================================
\* Modification History
\* Created Sun Apr 20 17:29:07 EDT 2014 by praseem
