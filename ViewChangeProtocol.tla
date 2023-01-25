------------------------- MODULE ViewChangeProtocol -------------------------
EXTENDS Declarations
    
LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE NormalProtocol
LOCAL INSTANCE ReconfigurationProtocol

GracefulDemote(r) == \* M_d
    /\ replicas[r].viewNumber < MaxViewNumber
    /\ IsPrimary(r)
    /\ replicas[r].status = "normal"
    /\ replicas[r].opNumber = replicas[r].commitNumber
    /\ replicas' = [
        replicas EXCEPT ![r].viewNumber = @ + 1,
                        ![r].status     = "view-change"
       ]
    /\ UNCHANGED <<committedLogs>>
    
ReplicaWaitsForReconfiguration(r) ==
\*    IF 
        /\ Len(replicas[r].logs) > 0
        /\ replicas[r].logs[Len(replicas[r].logs)] \in ENMetaLogType
        /\ replicas[r].logs[Len(replicas[r].logs)].epochNumber > replicas[r].epochNumber
\*    THEN TRUE
\*    ELSE FALSE

StartViewChange(r) == \* See 4.2.1 of the paper. E_1
    /\ replicas[r].status /= "shut down"
    /\ replicas[r].viewNumber < MaxViewNumber - 1
    /\ ~ IsPrimary(r)
\*    /\ ~ ReplicaWaitsForReconfiguration(r)
    /\ replicas' = [
        replicas EXCEPT ![r].viewNumber = @ + 1,
                        ![r].status     = "view-change"
       ]
    /\ UNCHANGED <<committedLogs>>
    
HandleStartViewChange(r) ==
    \* See 4.2.1's end of the paper. 
\*       /\ ~ PreparingReconfiguration(r)
       /\ \E i \in Range(replicas[r].config):
          \/ /\ replicas[i].viewNumber > replicas[r].viewNumber
             /\ \/ /\ replicas[i].epochNumber = replicas[r].epochNumber
                   /\ replicas[r].status /= "shut down"
                   /\ replicas' = [
                        replicas EXCEPT ![r].viewNumber = replicas[i].viewNumber,
                                        ![r].status     = "view-change"
                       ]
                   /\ UNCHANGED <<committedLogs>>
\*                \/ /\ replicas[i].epochNumber > replicas[r].epochNumber
\*\*                   /\ replicas[i].status /= "recovering"
\*                   /\ DownloadTillEN(i, r)
\*                   /\ UNCHANGED <<committedLogs>>
\*          \/ /\ replicas[i].viewNumber = replicas[r].viewNumber
\*             /\ replicas[i].epochNumber > replicas[r].epochNumber
\*             /\ DownloadTillEN(i, r)
\*             /\ UNCHANGED  <<committedLogs>>
                 

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
                            i \in Range(replicas[r].config):
                               /\ replicas[i].viewNumber = viewNumber
                               /\ replicas[i].epochNumber = replicas[r].epochNumber
                               /\ replicas[i].status /= "recovering"
\*                               /\ IF Len(replicas[i].logs) > 0
\*                                  THEN ~ (replicas[i].logs[Len(replicas[i].logs)] \in ENMetaLogType /\ replicas[i].status = "view-change")
\*                                  ELSE TRUE
                          }) >= majority(r)
                    /\ \/ /\ replicas[r].status = "normal"
                          /\ replicas[r].viewNumber + 1 = viewNumber
                          /\ replicas[r].config[(viewNumber % ConfigSize(r)) + 1] = r
                       \/ /\ replicas[r].status = "view-change"
                          /\ replicas[r].viewNumber = viewNumber
                          /\ replicas[r].config[(viewNumber % ConfigSize(r)) + 1] = r
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
                            replicas[i]: i \in Range(replicas[r].config)
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
                replicaWithNewCommitNumberIdx == CHOOSE i \in 1..NumReplicas: replicas[i] = replicaWithNewCommitNumber
              IN
                \/ /\ replicaWithNewCommitNumber.epochNumber = replicas[r].epochNumber
                   /\ replicas[r].config[(viewNumber % ConfigSize(r)) + 1] = r 
                   /\ \/ /\ replicas[r].status = "normal"
                         /\ replicas[r].viewNumber < viewNumber
                      \/ /\ replicas[r].status = "view-change"
                         /\ replicas[r].viewNumber = viewNumber
                   /\ replicas' = [
                       replicas EXCEPT ![r] = [
                           status                     |-> "normal",
                           viewNumber                 |-> viewNumber,
                           opNumber                   |-> opNumber + 1,
                           epochNumber                |-> replicas[r].epochNumber,
                           commitNumber               |-> replicaWithNewCommitNumber.commitNumber,
                           logs                       |-> Append(logs, [viewNumber |-> viewNumber]),
                           batch                      |-> <<>>,
                           lastNonce                  |-> replicas[r].lastNonce,
                           oldConfig                  |-> replicas[r].oldConfig,
                           config                     |-> replicas[r].config
                       ]
                      ]
                     /\ UNCHANGED <<committedLogs>>
\*                \/ /\ replicaWithNewCommitNumber.epochNumber > replicas[r].epochNumber
\*                   /\ DownloadTillEN(replicaWithNewCommitNumberIdx, r)
\*                   /\ UNCHANGED  <<committedLogs>>

HandleStartView(r) == \* See 4.2.5 of the paper. R_c
    /\ \E i \in Range(replicas[r].config):
        /\ \/ /\ replicas[r].status = "view-change"
              /\ replicas[i].status = "normal"
              /\ IsPrimary(i)
              /\ replicas[i].viewNumber = replicas[r].viewNumber
           \/ /\ replicas[r].status = "normal"
              /\ replicas[i].status = "normal"
              /\ GetPrimary(i) >= i
              /\ replicas[r].viewNumber < replicas[i].viewNumber 
        /\
            LET logIdxWithVNMetaLog == GetIdx(replicas[i].logs, "viewNumber", replicas[i].viewNumber, VNMetaLogType)
            IN replicas' = [
                replicas EXCEPT ![r] = [
                    status                     |-> IF r \in Range(replicas[i].config) THEN "normal" ELSE "shut down",
                    viewNumber                 |-> replicas[i].viewNumber,
                    epochNumber                |-> replicas[i].epochNumber,
                    opNumber                   |-> logIdxWithVNMetaLog,
                    commitNumber               |-> Min(replicas[i].commitNumber, logIdxWithVNMetaLog),
                    logs                       |-> SubSeq(replicas[i].logs, 1, logIdxWithVNMetaLog),
                    batch                      |-> <<>>,
                    lastNonce                  |-> replicas[r].lastNonce,
                    oldConfig                  |-> replicas[i].oldConfig,
                    config                     |-> replicas[i].config
                ]
            ]
        /\ UNCHANGED <<committedLogs>>

\*SVC == {r \in 1..Len(replicas): StartViewChange(r)} 
\*HSVC == {r \in 1..Len(replicas): HandleStartViewChange(r)} 
\*HDVC == {r \in 1..Len(replicas): HandleDoViewChange(r)} 
\*HSV == {r \in 1..Len(replicas): HandleStartView(r)} 
\*GD == {r \in 1..Len(replicas): GracefulDemote(r)} 

 
ViewChangeProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "recovering"
       /\ replicas[r].status /= "transitioning"
       /\ \/ StartViewChange(r)
          \/ HandleStartViewChange(r)
          \/ HandleDoViewChange(r)
          \/ HandleStartView(r)
          \/ GracefulDemote(r)
    /\ UNCHANGED <<nonce>>

=============================================================================
\* Modification History
\* Last modified Wed Jan 25 00:22:49 MSK 2023 by sandman
\* Created Thu Dec 01 21:03:22 MSK 2022 by sandman
