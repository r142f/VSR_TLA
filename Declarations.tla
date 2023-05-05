---------------------------- MODULE Declarations ----------------------------
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT
    Requests,       \* set of commands sent by client
    NumReplicas,    \* number of replicas
    MaxViewNumber,  \* maximum view number
    MaxNumFailures, \* maximum number of failures
    MaxEpochNumber, \* max epoch number
    MinConfigSize,  \* min config size
    MaxConfigSize,  \* max config size
    NULL            \* null value
    
ASSUME 
    /\ MinConfigSize <= NumReplicas
    /\ MaxConfigSize <= NumReplicas
    /\ MinConfigSize <= MaxConfigSize
        
VARIABLE 
    replicas,  \* replicas[r] is the state of replica r
    nonce,     \* number of failures at the moment
    vcCount    \* number of view changes called after timeout occurs

=============================================================================
\* Modification History
\* Last modified Fri May 05 16:13:49 MSK 2023 by sandman
\* Created Thu Dec 01 23:43:40 MSK 2022 by sandman
