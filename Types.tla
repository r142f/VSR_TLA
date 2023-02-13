------------------------------- MODULE Types -------------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils

ConfigType ==
    {
        SetToSeq(config): config \in
            {
                config \in SUBSET (1..NumReplicas) \ {{}}:
                    Cardinality(config) <= MaxConfigSize
            }
    }

MaxLogsSize == Cardinality(Requests) + QuasiMaxViewNumber + MaxEpochNumber

CommonLogType == [request: Requests]

VNMetaLogType == [viewNumber: 1..QuasiMaxViewNumber]

ENMetaLogType == 
    [
        epochNumber: 1..MaxEpochNumber,
        config: ConfigType
    ]

LogType == \* log is an entry with request and op-number assigned to it + metalogs
    CommonLogType \union VNMetaLogType \union ENMetaLogType

CheckLogs(logs) ==
    /\ Len(logs) = Cardinality(Range(logs))
    /\ \A i, j \in 1..Len(logs):
        /\ (
            /\ i < j
            /\ logs[i] \in VNMetaLogType
            /\ logs[j] \in VNMetaLogType
           ) => logs[i].viewNumber < logs[j].viewNumber
        /\ (
            /\ i < j
            /\ logs[i] \in ENMetaLogType
            /\ logs[j] \in ENMetaLogType
           ) => logs[i].epochNumber < logs[j].epochNumber
        
CommittedLogsTypeOK == CheckLogs(committedLogs) \* committedLogs type invariant

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
    \A r \in 1..NumReplicas: TRUE
        /\ replicas[r].status \in {"normal", "view-change", "recovering", "transitioning", "shut down"}
        /\ replicas[r].viewNumber \in 0..QuasiMaxViewNumber
        /\ replicas[r].epochNumber \in 0..MaxEpochNumber
        /\ replicas[r].opNumber \in 0..MaxLogsSize
        /\ replicas[r].commitNumber \in 0..MaxLogsSize
        /\ CheckLogs(replicas[r].logs)
        /\ replicas[r].batch \in BatchType
        /\ replicas[r].lastNonce \in 0..MaxNumFailures
        /\ replicas[r].oldConfig \in ConfigType \cup {<<>>}
        /\ replicas[r].config \in ConfigType \cup {<<>>}
   
NonceTypeOK == nonce \in 0..MaxNumFailures \* nonce type invariant

TypeOK == \* type invariant
    /\ ReplicasTypeOK
    /\ NonceTypeOK
    /\ CommittedLogsTypeOK

=============================================================================
\* Modification History
\* Last modified Thu Jan 26 02:03:04 MSK 2023 by sandman
\* Created Thu Dec 01 20:40:50 MSK 2022 by sandman
