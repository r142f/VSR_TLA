----------------------- MODULE ViewstampedReplication -----------------------
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
                Len(LongestCommonSubsequence(
                   SafeSubSeq(replicas[i].logs, 1, replicas[i].commitNumber),
                   SafeSubSeq(replicas[j].logs, 1, replicas[j].commitNumber)
                )) = Min(replicas[i].commitNumber, replicas[j].commitNumber)
        
----
    
ReplicasInit ==
  \E n \in MinConfigSize..MaxConfigSize:
    replicas = [
        r \in 1..NumReplicas |-> [
            status                     |-> IF r \in Range(InitConfig(n))
                                           THEN "normal"
                                           ELSE "shut down",
            viewNumber                 |-> 0,
            epochNumber                |-> 0,
            opNumber                   |-> 0,
            commitNumber               |-> 0,
            logs                       |-> <<>>,
            batch                      |-> <<>>,
            seedReplica                |-> NULL,
            oldConfig                  |-> <<>>,
            config                     |-> InitConfig(n)
        ]
    ]
    
NonceInit == nonce = 0

VCCountInit == vcCount = 0

Init == 
    /\ ReplicasInit
    /\ NonceInit
    /\ VCCountInit
    
----

INSTANCE DownloadProtocol
INSTANCE NormalProtocol
INSTANCE ViewChangeProtocol 
INSTANCE RecoveryProtocol
INSTANCE ReconfigurationProtocol

----

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
\*    /\ ~ ENABLED ViewChangeProtocolNext
\*    /\ ~ ENABLED RecoveryProtocolNext
\*    /\ ~ ENABLED ReconfigurationProtocolNext
    /\ ExistsFunctioningLatestConfig
    /\ \E r \in Range(LatestConfigReplicas):
        replicas[r].epochNumber = MaxEpochNumber
    /\ \A r \in Range(LatestConfigReplicas): \* every request was committed
        /\ replicas[r].status = "normal"
        /\ \A request \in Requests:
            \E l \in 1..Len(replicas[r].logs):
                /\ replicas[r].logs[l] \in CommonLogType
                /\ replicas[r].logs[l].request = request
                /\ replicas[r].commitNumber >= l            
    /\ \/ vcCount = MaxViewNumber            \* changed maximum views
       \/ /\ Len(LatestConfigReplicas) = 1
          /\ ~ \E r \in 1..NumReplicas:
            /\ replicas[r].status /= "shut down"
            /\ r /= ReplicaWithLatestFunctioningConfig
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
\* Last modified Thu May 18 15:54:48 MSK 2023 by sandman
\* Created Sat Nov 12 01:35:27 MSK 2022 by sandman
