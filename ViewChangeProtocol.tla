------------------------- MODULE ViewChangeProtocol -------------------------
EXTENDS Declarations
    
LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE StateTransferProtocol

StartViewChange(r) == \* See 4.2.1 of the paper. E_1
    /\ replicas[r].status /= "shut down"
    /\ ~ IsPrimary(r)
    /\ \/ /\ vcCount < MaxViewNumber
          /\ vcCount' = vcCount + 1
       \/ /\ replicas[GetPrimary(r)].status = "recovering" \* for a dead primary
          /\ replicas[r].viewNumber < QuasiMaxViewNumber
          /\ UNCHANGED <<vcCount>>
    /\ replicas' = [
        replicas EXCEPT ![r].viewNumber = @ + 1,
                        ![r].status     = "view-change"
       ]
    
HandleStartViewChange(r) ==
    \* See 4.2.1's end of the paper. 
       /\ \E i \in Range(replicas[r].config):
          \/ /\ replicas[i].viewNumber > replicas[r].viewNumber
             /\ \/ /\ replicas[i].epochNumber = replicas[r].epochNumber
                   /\ replicas[r].status /= "shut down"
                   /\ replicas' = [
                        replicas EXCEPT ![r].viewNumber = replicas[i].viewNumber,
                                        ![r].status     = "view-change"
                       ]
                   /\ UNCHANGED <<vcCount>>

    \* See 4.2.2 of the paper. Send "DoViewChange" msg was here

GetLastNormalViewNumber(replica) == 
    IF \E i \in 1..Len(replica.logs): replica.logs[i] \in VNMetaLogType
    THEN
        CHOOSE viewNumber \in 1..QuasiMaxViewNumber:
            \A i \in 1..Len(replica.logs):
                replica.logs[i] \in VNMetaLogType => replica.logs[i].viewNumber <= viewNumber
    ELSE 0

HandleDoViewChange(r) == \* See 4.2.3 of the paper. E_m и M_c
        LET 
            viewNumbers == {
                viewNumber \in 0..QuasiMaxViewNumber:
                    /\ Cardinality({
                            i \in Range(replicas[r].config):
                               /\ replicas[i].viewNumber = viewNumber
                               /\ replicas[i].epochNumber = replicas[r].epochNumber
                               /\ replicas[i].status /= "recovering"
                       }) >= majority(r)
                    /\ replicas[r].config[(viewNumber % ConfigSize(r)) + 1] = r
                    /\ \/ /\ replicas[r].status = "normal"
                          /\ replicas[r].viewNumber + 1 = viewNumber
                       \/ /\ replicas[r].status = "view-change"
                          /\ replicas[r].viewNumber = viewNumber
            }
IN
           /\ viewNumbers /= {}
           /\ LET
                viewNumber == 
                    CHOOSE viewNumber \in 0..QuasiMaxViewNumber:
                        \A x \in viewNumbers:
                            viewNumber >= x
                doViewChangeReplicas == 
                    {
                        replica \in {
                            replicas[i]: i \in Range(replicas[r].config)
                        }: /\ replica.viewNumber = viewNumber
                           /\ replica.epochNumber = replicas[r].epochNumber
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
                \/ /\ replicaWithNewCommitNumber.epochNumber = replicas[r].epochNumber
                   /\ replicas[r].config[(viewNumber % ConfigSize(r)) + 1] = r 
                   /\ \/ /\ replicas[r].status = "normal"
                         /\ replicas[r].viewNumber < viewNumber
                      \/ /\ replicas[r].status = "view-change"
                         /\ replicas[r].viewNumber = viewNumber
                   /\ \/ /\ replicas[r].logs /= logs
                         /\ 
                            LET
                                lcs == LongestCommonSubsequence(replicas[r].logs, logs)
                            IN replicas' = [
                                replicas EXCEPT ![r].logs         = Append(lcs, logs[Len(lcs) + 1]),
                                                ![r].opNumber     = Len(lcs) + 1,
                                                ![r].commitNumber = IF @ < replicaWithNewCommitNumber.commitNumber
                                                                    THEN @ + 1
                                                                    ELSE @
                            ]
                      \/ /\ replicas[r].logs = logs
                         /\ replicas' = [
                                replicas EXCEPT ![r].status       = "normal",
                                                ![r].viewNumber   = viewNumber,
                                                ![r].opNumber     = @ + 1,
                                                ![r].commitNumber = IF @ < replicaWithNewCommitNumber.commitNumber 
                                                                    THEN @ + 1
                                                                    ELSE @,
                                                ![r].logs         = Append(@, [viewNumber |-> viewNumber]),
                                                ![r].batch        = <<>>
                            ]
                     /\ UNCHANGED <<vcCount>>

HandleStartView(r) == \* See 4.2.5 of the paper. R_c
    /\ \E i \in Range(replicas[r].config):
        /\ replicas[r].epochNumber = replicas[i].epochNumber
        /\ \/ /\ replicas[r].status = "view-change"
              /\ replicas[i].status = "normal"
              /\ IsPrimary(i)
              /\ replicas[i].viewNumber = replicas[r].viewNumber
           \/ /\ replicas[r].status = "normal"
              /\ replicas[i].status = "normal"
              /\ GetPrimary(i) >= i
              /\ replicas[r].viewNumber < replicas[i].viewNumber 
        /\
            LET
                vnMetaLogIdx == GetIdx(replicas[i].logs, "viewNumber", replicas[i].viewNumber, VNMetaLogType)
                logs == SubSeq(replicas[i].logs, 1, vnMetaLogIdx)
                lcs == LongestCommonSubsequence(replicas[r].logs, logs)
            IN
                /\ \/ lcs /= logs
                   \/ replicas[r].commitNumber < replicas[i].commitNumber
                /\ Download(i, r, vnMetaLogIdx)
        /\ UNCHANGED <<vcCount>>
 
ViewChangeProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "recovering"
       /\ \/ StartViewChange(r)
          \/ HandleStartViewChange(r)
          \/ HandleDoViewChange(r)
          \/ HandleStartView(r)
    /\ UNCHANGED <<nonce>>

=============================================================================
\* Modification History
\* Last modified Wed Mar 29 20:53:28 MSK 2023 by sandman
\* Created Thu Dec 01 21:03:22 MSK 2022 by sandman
