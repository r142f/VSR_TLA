----------------------- MODULE ViewstampedReplicationV3 -----------------------
EXTENDS Declarations, Naturals, TLC

INSTANCE Utils
INSTANCE Types
    
vars == <<replicas, nonce, vcCount>>

ConsistentLogs == \* "all replicas must have consistent logs" invariant
    \A i \in 1..NumReplicas:
        \A j \in (i + 1)..NumReplicas:
          LET
            a == SafeSubSeq(replicas[i].logs, 1, replicas[i].commitNumber)
            b == SafeSubSeq(replicas[j].logs, 1, replicas[j].commitNumber)
          IN 
          /\ Len(LongestCommonSubsequence(
                SafeSubSeq(replicas[i].logs, 1, replicas[i].commitNumber),
                SafeSubSeq(replicas[j].logs, 1, replicas[j].commitNumber)
             )) = Min(replicas[i].commitNumber, replicas[j].commitNumber)
        
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
            config                     |-> config
        ]
    ]
    
NonceInit == nonce = 0

VCCountInit == vcCount = 0

Init == 
    /\ ReplicasInit
    /\ NonceInit
    /\ VCCountInit
    
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
    /\ \A r \in Range(LatestConfigReplicas): \* every request was committed
        /\ replicas[r].status = "normal"
        /\ \A request \in Requests:
            \E l \in 1..Len(replicas[r].logs):
                /\ replicas[r].logs[l] \in CommonLogType
                /\ replicas[r].logs[l].request = request
                /\ replicas[r].commitNumber >= l            
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
            \E r \in 1..NumReplicas:
                \A request \in Requests:
                    \E i \in 1..replicas[r].commitNumber:
                        /\ replicas[r].logs[i] \in CommonLogType
                        /\ replicas[r].logs[i].request = request
      )

=============================================================================
\* Modification History
\* Last modified Mon Mar 20 18:48:35 MSK 2023 by sandman
\* Created Sat Nov 12 01:35:27 MSK 2022 by sandman
