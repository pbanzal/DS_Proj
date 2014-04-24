---- MODULE MC ----
EXTENDS RBSF, TLC

\* CONSTANT definitions @modelParameterConstants:0processes
const_1398354867775232000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1qLen
const_1398354867786233000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2Message
const_1398354867797234000 == 
{"M1", "M2", "M3"}
----

\* INIT definition @modelBehaviorInit:0
init_1398354867807235000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1398354867819236000 ==
NextForRB
----
=============================================================================
\* Modification History
\* Created Thu Apr 24 11:54:27 EDT 2014 by praseem
