-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE Types
LOCAL INSTANCE NormalProtocol

CheckFailDuringReconfiguration(r) ==
   \/ \E i \in 1..Len(replicas):
     /\ replicas[i].status /= "shut down"
     /\ IsPrimary(i)
     /\ Len(replicas[i].logs) > 0
     /\ replicas[i].logs[Len(replicas[i].logs)] \in ENMetaLogType
     /\ 
        LET
            config == replicas[i].logs[Len(replicas[i].logs)].config
            f_config == LET fs == {f_i \in 0..Len(config): 2*f_i + 1 <= Len(config)}
                 IN CHOOSE f_i \in fs: 
                    \A f_j \in fs:
                        f_i >= f_j
        IN Cardinality({_r \in Range(config): replicas[_r].status = "recovering"}) < f_config
   \/ ~ \E i \in 1..Len(replicas):
     /\ replicas[i].status /= "shut down"
     /\ IsPrimary(i)
     /\ Len(replicas[i].logs) > 0
     /\ replicas[i].logs[Len(replicas[i].logs)] \in ENMetaLogType

FailAndSendRecovery(r) == \* See 4.3.1 of the paper.
    /\ nonce < MaxNumFailures
    /\ replicas[r].status /= "recovering"
    /\ Cardinality({_r \in Range(replicas[r].config): replicas[_r].status = "recovering"}) < f(r)
    /\ CheckFailDuringReconfiguration(r)
    /\ ExistsMaxEpochR
    /\ Cardinality({_r \in Range(replicas[MaxEpochR].config): replicas[_r].status = "recovering"}) < f(MaxEpochR)
    \* needed to prevent situation when last primary fails during view change
    \* on practice view-change can always proceed to the next primary if the current fails
    /\ replicas[r].config[(MaxViewNumber % ConfigSize(r)) + 1] /= r
    /\ replicas' = 
     [
         replicas EXCEPT ![r] = [
             status                     |-> "recovering",
             viewNumber                 |-> replicas[r].viewNumber,
             epochNumber                |-> replicas[r].epochNumber,
             opNumber                   |-> 0,
             commitNumber               |-> 0,
             logs                       |-> replicas[r].logs,
             batch                      |-> <<>>,
             lastNonce                  |-> nonce,
             oldConfig                  |-> <<>>,
             config                     |-> <<>>
         ]
     ]
    /\ nonce' = nonce + 1

HandleRecoveryResponse(r) == \* See 4.3.3 of the paper.
    /\ replicas[r].status = "recovering"
    /\ LET
        latestViewNumber ==
            CHOOSE viewNumber \in 0..MaxViewNumber:
                /\ \A i \in 1..NumReplicas: \* TODO
                    /\ replicas[i].viewNumber <= viewNumber

        primary == replicas[(latestViewNumber % NumReplicas) + 1]         
       IN
        /\ primary.status = "normal"
        /\ primary.viewNumber = latestViewNumber
        /\ primary.viewNumber >= replicas[r].viewNumber
        /\ replicas' = 
             [
                 replicas EXCEPT ![r] = [
                     status                     |-> "normal",
                     viewNumber                 |-> primary.viewNumber,
                     epochNumber                |-> primary.epochNumber,
                     opNumber                   |-> primary.opNumber,
                     commitNumber               |-> primary.commitNumber,
                     logs                       |-> primary.logs,
                     batch                      |-> <<>>,
                     lastNonce                  |-> replicas[r].lastNonce,
                     oldConfig                  |-> primary.oldConfig,
                     config                     |-> primary.config
                 ]
             ]
    /\ UNCHANGED <<nonce>>
     
RecoveryProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "shut down"
       /\ \/ FailAndSendRecovery(r)
          \/ HandleRecoveryResponse(r)
    /\ UNCHANGED <<committedLogs>>

=============================================================================
\* Modification History
\* Last modified Tue Jan 24 16:45:11 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman
