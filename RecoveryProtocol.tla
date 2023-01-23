-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE NormalProtocol

FailAndSendRecovery(r) == \* See 4.3.1 of the paper.
    /\ nonce < MaxNumFailures
    /\ replicas[r].status /= "recovering"
    /\ Cardinality({_r \in Range(replicas[r].config): replicas[_r].status = "recovering"}) < f(r)
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
\* Last modified Mon Jan 23 00:11:08 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman
