-------------------------- MODULE RecoveryProtocol --------------------------
EXTENDS Declarations

LOCAL INSTANCE Utils
LOCAL INSTANCE Types
LOCAL INSTANCE NormalProtocol

ExistsMaxENLog == 
    \E r \in 1..Len(replicas):
        /\ Len(replicas[r].logs) > 0
        /\ \E l \in 1..Len(replicas[r].logs):
            replicas[r].logs[l] \in ENMetaLogType
            
MaxENLogs ==
    LET
        maxENLog == CHOOSE enLog \in ENMetaLogType:
        /\ \E r \in 1..Len(replicas):
            /\ Len(replicas[r].logs) > 0
            /\ \E l \in 1..Len(replicas[r].logs):
                replicas[r].logs[l] = enLog
        /\ ~ \E r \in 1..Len(replicas):
            /\ Len(replicas[r].logs) > 0
            /\ \E l \in 1..Len(replicas[r].logs):
               /\ replicas[r].logs[l] \in ENMetaLogType
               /\ replicas[r].logs[l].epochNumber > enLog.epochNumber
    IN {
        enLog \in ENMetaLogType:
            /\ enLog.epochNumber = maxENLog.epochNumber
            /\ \E r \in 1..Len(replicas):
                /\ Len(replicas[r].logs) > 0
                /\ \E l \in 1..Len(replicas[r].logs):
                    replicas[r].logs[l] = enLog
    }
    
CanFail(r) ==
    LET
        configs ==
            {
                replicas[_r].config: _r \in {
                    _r \in 1..NumReplicas: replicas[_r].status /= "shut down"
                }
            }
    IN \A config \in configs:
        LET
            f_config == LET fs == {f_i \in 0..Len(config): 2*f_i + 1 <= Len(config)}
                     IN CHOOSE f_i \in fs: 
                        \A f_j \in fs:
                            f_i >= f_j
                            
            deadSize == Cardinality({_r \in Range(config): replicas[_r].status = "recovering" \/ replicas[_r].status = "shut down"})
        IN IF r \in Range(config) THEN deadSize < f_config ELSE TRUE   
            

CanFailAsMemberOfCurrentConfig(r) ==
    IF r \in Range(replicas[r].config)
    THEN 
        Cardinality(
            {
                _r \in Range(replicas[r].config):
                    \/ replicas[_r].status = "recovering"
                    \/ replicas[_r].status = "shut down"
                    \/ replicas[_r].epochNumber < replicas[r].epochNumber
            }
        ) < f(r)
    ELSE TRUE


CanFailAsMemberOfPotentialNewConfig(r) ==
   IF
       /\ ExistsMaxENLog
       /\ \E maxENLog \in MaxENLogs: r \in Range(maxENLog.config)
   THEN
       \A maxENLog \in MaxENLogs:
           LET 
               config == maxENLog.config
               f_config == LET fs == {f_i \in 0..Len(config): 2*f_i + 1 <= Len(config)}
                    IN CHOOSE f_i \in fs: 
                       \A f_j \in fs:
                           f_i >= f_j
               deadSize == Cardinality({_r \in Range(config): replicas[_r].status = "recovering" \/ replicas[_r].status = "shut down"})
           IN deadSize < f_config
   ELSE TRUE
    
    
CanFailAsMemberOfNewConfig(r) ==
    IF ExistsFunctioningLatestConfig /\ r \in Range(LatestConfigReplicas)
    THEN 
        Cardinality(
            {
                _r \in Range(LatestConfigReplicas):
                    \/ replicas[_r].status = "recovering"
                    \/ replicas[_r].status = "shut down"
            }
        ) < f(ReplicaWithLatestFunctioningConfig)
    ELSE TRUE
    
    
FailAndSendRecovery(r) == \* See 4.3.1 of the paper.
    /\ nonce < MaxNumFailures
    /\ replicas[r].status /= "recovering"
    /\ CanFail(r)
    /\ CanFailAsMemberOfCurrentConfig(r)
\*    /\ CheckFailDuringReconfiguration(r)
    /\ CanFailAsMemberOfNewConfig(r)
    /\ CanFailAsMemberOfPotentialNewConfig(r)
    \* needed to prevent situation when last primary fails during view change
    \* on practice view-change can always proceed to the next primary if the current fails
\*    /\ replicas[r].config[((MaxViewNumber - 1) % ConfigSize(r)) + 1] /= r
\*    /\ replicas[r].config[(MaxViewNumber % ConfigSize(r)) + 1] /= r
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
             opNumber                   |-> 0,
             commitNumber               |-> 0,
             logs                       |-> replicas[r].logs,
             batch                      |-> <<>>,
             lastNonce                  |-> nonce,
             oldConfig                  |-> <<>>,
             config                     |-> <<>>
         ]
     ]
    /\ nonce' = nonce + 1

HandleRecoveryResponse(r) == \* See 4.3.3 of the paper.
    /\ replicas[r].status = "recovering"
    /\ LET
        latestEpochNumber ==
            CHOOSE epochNumber \in 0..MaxEpochNumber:
                /\ \A i \in 1..NumReplicas:
                    /\ replicas[i].epochNumber <= epochNumber
        latestViewNumber ==
            CHOOSE viewNumber \in 0..QuasiMaxViewNumber:
                /\ \A i \in {i \in 1..NumReplicas:
                    /\ replicas[i].epochNumber = latestEpochNumber
                    /\ replicas[i].status /= "recovering"}:
                        /\ replicas[i].viewNumber <= viewNumber
        replicaIdx == 
            CHOOSE i \in 1..NumReplicas:
                /\ replicas[i].epochNumber = latestEpochNumber
                /\ replicas[i].viewNumber = latestViewNumber
                /\ replicas[i].status /= "recovering"

        primary == replicas[GetPrimary(replicaIdx)]
       IN
        /\ primary.status = "normal"
        /\ primary.viewNumber = latestViewNumber
        /\ primary.viewNumber >= replicas[r].viewNumber
        /\ replicas' = 
             [
                 replicas EXCEPT ![r] = [
                     status                     |-> IF r \in Range(primary.config) THEN "normal" ELSE "shut down",
                     viewNumber                 |-> primary.viewNumber,
                     epochNumber                |-> primary.epochNumber,
                     opNumber                   |-> primary.opNumber,
                     commitNumber               |-> primary.commitNumber,
                     logs                       |-> primary.logs,
                     batch                      |-> <<>>,
                     lastNonce                  |-> replicas[r].lastNonce,
                     oldConfig                  |-> primary.oldConfig,
                     config                     |-> primary.config
                 ]
             ]
    /\ UNCHANGED <<nonce>>
     
RecoveryProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "shut down"
       /\ \/ FailAndSendRecovery(r)
          \/ HandleRecoveryResponse(r)
    /\ UNCHANGED << vcCount>>

=============================================================================
\* Modification History
\* Last modified Thu Mar 23 01:15:15 MSK 2023 by sandman
\* Created Thu Dec 01 21:33:07 MSK 2022 by sandman
