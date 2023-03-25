-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE Types
LOCAL INSTANCE NormalProtocol
LOCAL INSTANCE StateTransferProtocol

NumberOfFailedReplicas(config) ==
    Cardinality({
        r \in Range(config):
            replicas[r].status = "recovering"
    })
    
NumberOfReplicasThatCanFail(config) ==
    LET
        fs == {
            f_i \in 0..Len(config):
                2*f_i + 1 <= Len(config)
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
    
    
FailAndSendRecovery(r) == \* See 4.3.1 of the paper.
    /\ nonce < MaxNumFailures
    /\ \/ replicas[r].status /= "recovering"
       \/ /\ replicas[r].status = "recovering"
          /\ replicas[r].recoveryReplica /= NULL
    /\ CanFail(r)
    \* needed to prevent situation when primary fails and view-change is not possible
    \* on practice view-change can always proceed to the next primary if the current fails
    /\ ~ (
        /\ replicas[r].viewNumber > MaxViewNumber
        /\ IsPrimary(r)
       )
    /\ replicas' = 
     [
         replicas EXCEPT ![r] = [
             status                     |-> "recovering",
             viewNumber                 |-> replicas[r].viewNumber,
             epochNumber                |-> replicas[r].epochNumber,
             opNumber                   |-> replicas[r].opNumber,
             commitNumber               |-> replicas[r].commitNumber,
             logs                       |-> replicas[r].logs,
             batch                      |-> <<>>,
             recoveryReplica            |-> NULL,
             oldConfig                  |-> replicas[r].oldConfig,
             config                     |-> replicas[r].config
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

HandleRecoveryResponse(r) == \* See 4.3.3 of the paper.
    /\ replicas[r].status = "recovering"
    /\ \/ /\ replicas[r].recoveryReplica = NULL
          /\ \E i \in 1..NumReplicas:
            /\ IsSuitableAsRecoveryReplica(r, i)
            /\ replicas' = [
                    replicas EXCEPT ![r].recoveryReplica = i
               ]
       \/ /\ replicas[r].recoveryReplica /= NULL
          /\ LET
                currentRecoveryReplica == replicas[replicas[r].recoveryReplica]
             IN
                \E i \in 1..NumReplicas:
                   /\ IsSuitableAsRecoveryReplica(r, i)
                   /\ \/ /\ i /= replicas[r].recoveryReplica
                         /\ \/ /\ \/ replicas[i].epochNumber > currentRecoveryReplica.epochNumber
                                  \/ /\ replicas[i].epochNumber = currentRecoveryReplica.epochNumber
                                     /\ replicas[i].viewNumber > currentRecoveryReplica.viewNumber
                            \/ ~ IsSuitableAsRecoveryReplica(r, replicas[r].recoveryReplica)
                      \/ i = replicas[r].recoveryReplica
                   /\ Download(i, r, replicas[i].opNumber)       
    /\ UNCHANGED <<nonce>>
     
RecoveryProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "shut down"
       /\ \/ FailAndSendRecovery(r)
          \/ HandleRecoveryResponse(r)
    /\ UNCHANGED << vcCount>>

=============================================================================
\* Modification History
\* Last modified Sat Mar 25 22:03:33 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman
