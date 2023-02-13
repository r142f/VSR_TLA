----------------------- MODULE ViewstampedReplicationV3 -----------------------
EXTENDS Declarations

INSTANCE Utils
INSTANCE Types
    
vars == <<replicas, nonce, committedLogs>>

ConsistentLogs == \* "all replicas must have consistent logs" invariant
    \A i \in 1..Len(replicas):
        Len(LongestCommonSubsequence(
            SafeSubSeq(replicas[i].logs, 1, replicas[i].commitNumber),
            committedLogs
        )) = Min(replicas[i].commitNumber, Len(committedLogs))
        
----
    
ReplicasInit == \* see fig. 2 of the paper for explanation
  \E config \in ConfigType:
    replicas = [
        x \in 1..NumReplicas |-> [
            status                     |-> IF x \in Range(config) THEN "normal" ELSE "shut down",
            viewNumber                 |-> 0,
            epochNumber                |-> 0,
            opNumber                   |-> 0,
            commitNumber               |-> 0,
            logs                       |-> <<>>,
            batch                      |-> <<>>,
            lastNonce                  |-> 0,
            oldConfig                  |-> <<>>,
            config                     |-> config\*SetToSeq(1..MaxConfigSize) \* TODO
        ]
    ]
    
NonceInit == nonce = 0

CommittedLogsInit == committedLogs = <<>>

Init == 
    /\ ReplicasInit
    /\ NonceInit
    /\ CommittedLogsInit
    
----

INSTANCE StateTransferProtocol
INSTANCE NormalProtocol
INSTANCE ViewChangeProtocol 
INSTANCE RecoveryProtocol
INSTANCE ReconfigurationProtocol

----

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ ExistsFunctioningLatestConfig
    /\ \A r \in Range(LatestConfigReplicas):
        /\ replicas[r].commitNumber >= Cardinality(Requests) \* every request was committed
        /\ \/ replicas[r].viewNumber >= MaxViewNumber \* changed maximum views
           \/ /\ replicas[ReplicaWithLatestFunctioningConfig].epochNumber = MaxEpochNumber
              /\ Len(LatestConfigReplicas) = 1
    /\ UNCHANGED <<vars>>

 
Next ==
    \/ NormalProtocolNext
    \/ ViewChangeProtocolNext
    \/ RecoveryProtocolNext
    \/ ReconfigurationProtocolNext
    \/ Terminating
       
Spec == 
    /\ Init
    /\ [][Next]_vars 
    \* used to prevent stuttering before terminating
    \* gurantees that we won't be in a behaviour
    \* where from some state Next is always enabled and we didn't used it
    \* (in a way that changes vars)
    \* when Terminating happens it is not true, so stuttering happens
    \* but it's allowed by us. RequestsCommitted should be true at this point.
    /\ SF_vars(Next)    

RequestsCommitted == \* "eventually all client requests are committed" temporal property
    <>(
        /\ \A request \in Requests:
            \E i \in 1..Len(committedLogs):
                /\ committedLogs[i] \in CommonLogType
                /\ committedLogs[i].request = request
\*        /\ \A r \in Range(ConfigReplicas):
\*            replicas[r].logs = committedLogs
      )

=============================================================================
\* Modification History
\* Last modified Thu Jan 26 04:47:51 MSK 2023 by sandman
\* Created Sat Nov 12 01:35:27 MSK 2022 by sandman
