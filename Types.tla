------------------------------- MODULE Types -------------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils

MaxLogsSize == Cardinality(Requests) + MaxViewNumber

CommonLogType == [request: Requests]

VNMetaLogType == [viewNumber: 1..MaxViewNumber]

LogType == \* log is an entry with request and op-number assigned to it + metalogs
    CommonLogType \union VNMetaLogType

LogsType == \* replicas[r].logs invariant
    LET
        possibleLogsSets == SUBSET LogType
        possibleLogsPerms == UNION {Perms(SetToSeq(possibleLogs)): possibleLogs \in possibleLogsSets}
        possibleLogsSubSeqs == {
            SafeSubSeq(possibleLogsPerm, 1, n): 
                possibleLogsPerm \in possibleLogsPerms,
                n \in 1..MaxLogsSize
            }
        correctPossibleLogsSubSeqs == {
            possibleLogsSubSeq \in possibleLogsSubSeqs:
                \A i, j \in 1..Len(possibleLogsSubSeq):
                    /\ (
                        /\ i < j
                        /\ possibleLogsSubSeq[i] \in VNMetaLogType
                        /\ possibleLogsSubSeq[j] \in VNMetaLogType
                       ) => possibleLogsSubSeq[i].viewNumber < possibleLogsSubSeq[j].viewNumber     
        }
    IN correctPossibleLogsSubSeqs
    
        
CommittedLogsTypeOK == committedLogs \in LogsType \* committedLogs type invariant

BatchType == \* requests are send from primary replica to others using batching
    {
        SubSeq(
            [
                i \in 1..Cardinality(Requests) |-> [
                    request  |-> perm[i]
                ]
            ],
            l, 
            r
        ): l, r \in 1..Cardinality(Requests),
           perm \in Perms(SetToSeq(Requests))
    } \union {<<>>}

ReplicasTypeOK == \* replicas type invariant
    replicas \in [
        1..NumReplicas -> [
            status:                     {"normal", "view-change", "recovering"},
            viewNumber:                 0..MaxViewNumber,
            opNumber:                   0..MaxLogsSize,
            commitNumber:               0..MaxLogsSize,
            logs:                       LogsType,
            batch:                      BatchType,
            lastNonce:                  0..MaxNumFailures
        ]
    ]
   
NonceTypeOK == nonce \in 0..MaxNumFailures \* nonce type invariant

TypeOK == \* type invariant
    /\ ReplicasTypeOK
    /\ NonceTypeOK
    /\ CommittedLogsTypeOK

=============================================================================
\* Modification History
\* Last modified Wed Jan 04 20:10:01 MSK 2023 by sandman
\* Created Thu Dec 01 20:40:50 MSK 2022 by sandman
