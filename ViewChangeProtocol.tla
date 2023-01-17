------------------------- MODULE ViewChangeProtocol -------------------------
EXTENDS Declarations
    
LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE NormalProtocol

GracefulDemote(r) == 
    /\ replicas[r].viewNumber < MaxViewNumber
    /\ IsPrimary(r)
    /\ replicas[r].opNumber = replicas[r].commitNumber
    /\ replicas' = [
        replicas EXCEPT ![r].viewNumber = @ + 1,
                        ![r].status     = "view-change"
       ]
    /\ UNCHANGED <<committedLogs>>

StartViewChange(r) == \* See 4.2.1 of the paper. E_1
    /\ replicas[r].viewNumber < MaxViewNumber
    /\ ~ IsPrimary(r)
    /\ replicas' = [
        replicas EXCEPT ![r].viewNumber = @ + 1,
                        ![r].status     = "view-change"
       ]
    /\ UNCHANGED <<committedLogs>>
    
HandleStartViewChange(r) ==
    \* See 4.2.1's end of the paper. 
       /\ \E i \in 1..NumReplicas:
           /\ replicas[i].viewNumber > replicas[r].viewNumber
           /\ replicas' = [
                replicas EXCEPT ![r].viewNumber = replicas[i].viewNumber,
                                ![r].status     = "view-change"
               ]
           /\ UNCHANGED <<committedLogs>>

    \* See 4.2.2 of the paper. Send "DoViewChange" msg was here

GetLastNormalViewNumber(replica) == 
    IF \E i \in 1..Len(replica.logs): replica.logs[i] \in VNMetaLogType
    THEN
        CHOOSE viewNumber \in 1..MaxViewNumber:
            \A i \in 1..Len(replica.logs):
                replica.logs[i] \in VNMetaLogType => replica.logs[i].viewNumber <= viewNumber
    ELSE 0

HandleDoViewChange(r) == \* See 4.2.3 of the paper. E_m и M_c
        LET 
            viewNumbers == {
                viewNumber \in 0..MaxViewNumber:
                    /\ Cardinality({
                            i \in 1..NumReplicas:
                               /\ replicas[i].viewNumber = viewNumber
                               /\ replicas[i].status /= "recovering"
                          }) > f
                    /\ \/ /\ replicas[r].status = "normal"
                          /\ replicas[r].viewNumber + 1 = viewNumber
                          /\ (viewNumber % NumReplicas) + 1 = r
                       \/ /\ replicas[r].status = "view-change"
                          /\ replicas[r].viewNumber = viewNumber
                          /\ (viewNumber % NumReplicas) + 1 = r
            }
        IN
           /\ viewNumbers /= {}
           /\ LET
                viewNumber == 
                    CHOOSE viewNumber \in 0..MaxViewNumber:
                        \A x \in viewNumbers:
                            viewNumber >= x
                doViewChangeReplicas == 
                    {
                        replica \in {
                            replicas[i]:i \in 1..NumReplicas
                        }: /\ replica.viewNumber = viewNumber
                           /\ replica.status /= "recovering"
                    }
                replicaWithNewLogs ==
                    CHOOSE replica \in doViewChangeReplicas:
                        \A replica_i \in doViewChangeReplicas:
                            \/ GetLastNormalViewNumber(replica) > GetLastNormalViewNumber(replica_i)
                            \/ /\ GetLastNormalViewNumber(replica) = GetLastNormalViewNumber(replica_i)
                               /\ replica.opNumber >= replica_i.opNumber
                logs == replicaWithNewLogs.logs
                opNumber == Len(logs)
                replicaWithNewCommitNumber ==
                    CHOOSE replica \in doViewChangeReplicas:
                        \A replica_i \in doViewChangeReplicas:
                            replica.commitNumber >= replica_i.commitNumber
              IN
                /\ viewNumber % NumReplicas = r - 1 
                /\ \/ /\ replicas[r].status = "normal"
                      /\ replicas[r].viewNumber < viewNumber
                   \/ /\ replicas[r].status = "view-change"
                      /\ replicas[r].viewNumber = viewNumber
                /\ replicas' = [
                    replicas EXCEPT ![r] = [
                        status                     |-> "normal",
                        viewNumber                 |-> viewNumber,
                        opNumber                   |-> opNumber + 1,
                        commitNumber               |-> replicaWithNewCommitNumber.commitNumber,
                        logs                       |-> Append(logs, [viewNumber |-> viewNumber]),
                        batch                      |-> <<>>,
                        lastNonce                  |-> replicas[r].lastNonce
                    ]
                   ]
                  /\ UNCHANGED <<committedLogs>>

HandleStartView(r) == \* See 4.2.5 of the paper. R_c
    /\ \E i \in 1..NumReplicas:
        /\ \/ /\ replicas[r].status = "view-change"
              /\ replicas[i].status = "normal"
              /\ IsPrimary(i)
              /\ replicas[i].viewNumber = replicas[r].viewNumber
           \/ /\ replicas[r].status = "normal"
              /\ replicas[i].status = "normal"
              /\ (replicas[i].viewNumber % NumReplicas) + 1 >= i
              /\ replicas[r].viewNumber < replicas[i].viewNumber 
        /\
            LET logIdxWithVNMetaLog == GetIdx(replicas[i].logs, "viewNumber", replicas[i].viewNumber, VNMetaLogType)
            IN replicas' = [
                replicas EXCEPT ![r] = [
                    status                     |-> "normal",
                    viewNumber                 |-> replicas[i].viewNumber,
                    opNumber                   |-> logIdxWithVNMetaLog,
                    commitNumber               |-> Min(replicas[i].commitNumber, logIdxWithVNMetaLog),
                    logs                       |-> SubSeq(replicas[i].logs, 1, logIdxWithVNMetaLog),
                    batch                      |-> <<>>,
                    lastNonce                  |-> replicas[r].lastNonce
                ]
            ]
        /\ UNCHANGED <<committedLogs>>

 
ViewChangeProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "recovering"
       /\ \/ StartViewChange(r)
          \/ HandleStartViewChange(r)
          \/ HandleDoViewChange(r)
          \/ HandleStartView(r)
          \/ GracefulDemote(r)
    /\ UNCHANGED <<nonce>>

=============================================================================
\* Modification History
\* Last modified Fri Jan 06 15:27:00 MSK 2023 by sandman
\* Created Thu Dec 01 21:03:22 MSK 2022 by sandman
