------------------------------- MODULE Types -------------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils

InitConfig(n) == [i \in 1..n |-> i]

ConfigTypeOrdered == 
    {
        SetToSeq(config): config \in {
            config \in SUBSET (1..NumReplicas) \ {{}}:
                /\ Cardinality(config) >= MinConfigSize
                /\ Cardinality(config) <= MaxConfigSize
        }
    }
    
ConfigTypeUnordered ==
    UNION {
        Perms(config): config \in ConfigTypeOrdered
    }
    
ConfigType == ConfigTypeOrdered

MaxLogsSize == Cardinality(Requests) + QuasiMaxViewNumber + MaxEpochNumber

CommonLogType == [request: Requests]

VNMetaLogType ==
    [
        viewNumber: 1..QuasiMaxViewNumber,
        epochNumber: 0..MaxEpochNumber
    ]

ENMetaLogType == 
    [
        epochNumber: 1..MaxEpochNumber,
        config: ConfigType
    ]

LogType == \* log is an entry with request and op-number assigned to it + metalogs
    CommonLogType \union
    VNMetaLogType \union
    ENMetaLogType

CheckCommittedLogs(logs) ==
    /\ Len(logs) = Cardinality(Range(logs))
    /\ \A i, j \in 1..Len(logs):
        /\ (
            /\ i < j
            /\ logs[i] \in VNMetaLogType
            /\ logs[j] \in VNMetaLogType
           ) => 
                /\ logs[i].viewNumber < logs[j].viewNumber
                /\ logs[i].epochNumber <= logs[j].epochNumber
        /\ (
            /\ i < j
            /\ logs[i] \in ENMetaLogType
            /\ logs[j] \in ENMetaLogType
           ) => logs[i].epochNumber < logs[j].epochNumber

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
    \A r \in 1..NumReplicas:
        /\ replicas[r].status \in {"normal", "view-change", "recovering", "shut down", "epoch catchup"}
        /\ replicas[r].viewNumber \in 0..QuasiMaxViewNumber
        /\ replicas[r].epochNumber \in 0..MaxEpochNumber
        /\ replicas[r].opNumber = Len(replicas[r].logs)
        /\ replicas[r].commitNumber \in 0..replicas[r].opNumber
        /\ CheckCommittedLogs(SafeSubSeq(replicas[r].logs, 1, replicas[r].commitNumber))
        /\ replicas[r].batch \in BatchType
        /\ replicas[r].seedReplica \in 1..NumReplicas \union {NULL}
        /\ replicas[r].config \in ConfigType \cup {<<>>}
   
NonceTypeOK == nonce \in 0..MaxNumFailures \* nonce type invariant

VCCountTypeOK == vcCount \in 0..MaxViewNumber

TypeOK == \* type invariant
    /\ ReplicasTypeOK
    /\ NonceTypeOK
    /\ VCCountTypeOK

=============================================================================
\* Modification History
\* Last modified Thu May 18 15:51:51 MSK 2023 by sandman
\* Created Thu Dec 01 20:40:50 MSK 2022 by sandman
