-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE NormalProtocol

FailAndSendRecovery(r) == \* See 4.3.1 of the paper.
    /\ nonce < MaxNumFailures
    /\ Cardinality({_r \in 1..Len(replicas): replicas[_r].status = "recovering"}) < f
    \* needed to prevent situation when last primary fails during view change
    \* on practice view-change can always proceed to the next primary if the current fails
    /\ (MaxViewNumber % NumReplicas) + 1 /= r
    /\ replicas' = 
     [
         replicas EXCEPT ![r] = [
             status                     |-> "recovering",
             viewNumber                 |-> replicas[r].viewNumber,
\*             latestViewNumberWithNormal |-> 0,
             opNumber                   |-> 0,
             commitNumber               |-> 0,
             logs                       |-> replicas[r].logs,
             batch                      |-> <<>>,
             lastNonce                  |-> nonce
         ]
     ]
    /\ nonce' = nonce + 1

HandleRecoveryResponse(r) == \* See 4.3.3 of the paper.
    /\ replicas[r].status = "recovering"
    /\ LET
        latestViewNumber ==
            CHOOSE viewNumber \in 0..MaxViewNumber:
                /\ \A i \in 1..NumReplicas:
                    replicas[i].viewNumber <= viewNumber

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
                     opNumber                   |-> primary.opNumber,
                     commitNumber               |-> primary.commitNumber,
                     logs                       |-> primary.logs,
                     batch                      |-> <<>>,
                     lastNonce                  |-> replicas[r].lastNonce
                 ]
             ]
    /\ UNCHANGED <<nonce>>
     
RecoveryProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       \/ FailAndSendRecovery(r)
       \/ HandleRecoveryResponse(r)
    /\ UNCHANGED <<committedLogs>>

=============================================================================
\* Modification History
\* Last modified Wed Jan 04 20:10:18 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman
