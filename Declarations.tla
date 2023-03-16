---------------------------- MODULE Declarations ----------------------------
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT
    Requests,       \* set of commands sent by client
    NumReplicas,    \* num/ber of replicas
    MaxViewNumber,  \* maximum view number
    MaxNumFailures, \* maximum number of failures
    MaxEpochNumber, \* max epoch number
    MaxConfigSize   \* max config size
        
VARIABLE 
    replicas, \* replicas[r] is the state of replica r
    nonce,     \* number of failures at the moment (needed for Recovery protocol)
    vcCount,   \* number of viewchanges called directly
    committedLogs \* sequence of committed logs, used for checking consistency

=============================================================================
\* Modification History
\* Last modified Tue Feb 14 13:16:01 MSK 2023 by sandman
\* Created Thu Dec 01 23:43:40 MSK 2022 by sandman
