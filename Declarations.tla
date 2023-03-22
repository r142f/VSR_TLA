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
    replicas,  \* replicas[r] is the state of replica r
    nonce,     \* number of failures at the moment (needed for Recovery protocol)
    vcCount    \* number of viewchanges called directly

=============================================================================
\* Modification History
\* Last modified Mon Mar 20 02:56:04 MSK 2023 by sandman
\* Created Thu Dec 01 23:43:40 MSK 2022 by sandman
