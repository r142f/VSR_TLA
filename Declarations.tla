---------------------------- MODULE Declarations ----------------------------
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT
    Requests,       \* set of commands sent by client
    NumReplicas,    \* number of replicas
    MaxViewNumber,  \* maximum view number
    MaxNumFailures  \* maximum number of failures
    
VARIABLE 
    replicas, \* replicas[r] is the state of replica r
    nonce,     \* number of failures at the moment (needed for Recovery protocol)
    committedLogs \* sequence of committed logs, used for checking consistency

=============================================================================
\* Modification History
\* Last modified Fri Dec 16 21:22:14 MSK 2022 by sandman
\* Created Thu Dec 01 23:43:40 MSK 2022 by sandman
