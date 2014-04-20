---- MODULE MC ----
EXTENDS RB, TLC

\* CONSTANT definitions @modelParameterConstants:0Processes
const_139793606723651000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1qLen
const_139793606724752000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2Messages
const_139793606725853000 == 
{1,2}
----

\* INIT definition @modelBehaviorNoSpec:0
init_139793606726954000 ==
FALSE/\dMsgQ = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_139793606727955000 ==
FALSE/\dMsgQ' = dMsgQ
----
=============================================================================
\* Modification History
\* Created Sat Apr 19 15:34:27 EDT 2014 by praseem
