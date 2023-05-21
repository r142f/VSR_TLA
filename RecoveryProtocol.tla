-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE Types
LOCAL INSTANCE NormalProtocol
LOCAL INSTANCE DownloadProtocol
LOCAL INSTANCE ViewChangeProtocol

NumberOfFailedReplicas(config) ==
    Cardinality({
        r \in Range(config):
            replicas[r].status = "recovering"
    })
    
NumberOfReplicasThatCanFail(config) ==
    LET
        operatingConfigSize ==
            Cardinality(
                {
                    r \in Range(config): 
                        replicas[r].status /= "shut down"
                }
            )
        fs == {
            f_i \in 0..operatingConfigSize:
                2*f_i + 1 <= operatingConfigSize
        }
    IN
        CHOOSE f_i \in fs: 
            \A f_j \in fs:
                f_i >= f_j
        
CanFail(r) ==
    LET
        functioningReplicas == {
            i \in 1..NumReplicas:
                /\ replicas[i].status /= "recovering"
                /\ IF
                    \E j \in 1..NumReplicas:
                        replicas[j].epochNumber > replicas[i].epochNumber
                   THEN replicas[i].status /= "shut down"
                   ELSE TRUE
        }
        configs == {
            config \in ConfigType:
                \E i \in functioningReplicas:
                    \/ replicas[i].config = config
                    \/ \E l \in 1..Len(replicas[i].logs):
                       /\ replicas[i].logs[l] \in ENMetaLogType
                       /\ replicas[i].logs[l].epochNumber > replicas[i].epochNumber
        }   
    IN \A config \in configs:
        r \in Range(config) =>
            NumberOfFailedReplicas(config) < NumberOfReplicasThatCanFail(config)

Fail(r) ==    
    /\ nonce < MaxNumFailures
    /\ \/ replicas[r].status /= "recovering"
       \/ /\ replicas[r].status = "recovering"
          /\ replicas[r].seedReplica /= NULL
    /\ CanFail(r)
    \* needed to prevent situation when primary fails and view-change is not possible
    \* on practice view-change can always proceed to the next primary if the current fails
    /\ ~ (
        /\ replicas[r].viewNumber > MaxViewNumber
        /\ replicas[r].status /= "recovering"
        /\ IsPrimary(r)
       )
    /\ replicas' = 
     [
         replicas EXCEPT ![r] = [
             status       |-> "recovering",
             viewNumber   |-> 0,
             epochNumber  |-> 0,
             opNumber     |-> 0,
             commitNumber |-> 0,
             logs         |-> <<>>,
             batch        |-> <<>>,
             seedReplica  |-> NULL,
             config       |-> <<>>
         ]
     ]
    /\ nonce' = nonce + 1

IsSuitableAsRecoveryReplica(r, i) ==
    /\ replicas[i].status = "normal"
    /\ IsPrimary(i)
    /\ \/ /\ replicas[i].epochNumber >= replicas[r].epochNumber
          /\ replicas[i].viewNumber >= replicas[r].viewNumber
       \/ /\ replicas[i].epochNumber > replicas[r].epochNumber
          /\ replicas[i].viewNumber < replicas[r].viewNumber

 HandleRecoveryResponse(r) ==
     /\ replicas[r].status = "recovering"
     /\ \/ /\ replicas[r].seedReplica = NULL
           /\ \E i \in 1..NumReplicas \ {r}:
             /\ IsSuitableAsRecoveryReplica(r, i)
             /\ Cardinality({
                    j \in 1..NumReplicas:
                        /\ replicas[j].epochNumber = replicas[i].epochNumber
                        /\ replicas[j].viewNumber <= replicas[i].viewNumber
                        /\ replicas[j].status = "normal"
                }) >= majority(i)
             /\ replicas' = [
                     replicas EXCEPT ![r].seedReplica = i
                ]
        \/ /\ replicas[r].seedReplica /= NULL
           /\ LET
                 seedReplica == replicas[r].seedReplica
              IN 
                 \/ /\ IsSuitableAsRecoveryReplica(r, seedReplica)
                    /\ Download(seedReplica, r, replicas[seedReplica].opNumber, FALSE, FALSE) 
                 \/ /\ ~ IsSuitableAsRecoveryReplica(r, seedReplica)
                    /\ replicas' = [
                           replicas EXCEPT ![r].seedReplica = NULL
                       ]      
     /\ UNCHANGED <<nonce>>
     
RecoveryProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "shut down"
       /\ \/ Fail(r)
          \/ HandleRecoveryResponse(r)
    /\ UNCHANGED << vcCount>>

=============================================================================
\* Modification History
\* Last modified Sat May 20 20:50:14 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman