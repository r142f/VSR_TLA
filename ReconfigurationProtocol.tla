---------------------- MODULE ReconfigurationProtocol ----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils

PreparingReconfiguration(r) ==
    /\ IsPrimary(r)
    /\ Len(replicas[r].logs) > 0
    /\ replicas[r].logs[Len(replicas[r].logs)] \in ENMetaLogType
    /\ replicas[r].logs[Len(replicas[r].logs)].epochNumber = replicas[r].epochNumber
    
HandleReconfigurationRequest(r) ==
    /\ replicas[r].epochNumber < MaxEpochNumber
    /\ ~ \E i \in 1..Len(replicas[r].logs):
           /\ replicas[r].logs[i] \in ENMetaLogType
           /\ replicas[r].logs[i].epochNumber = replicas[r].epochNumber + 1
    /\ ~ PreparingReconfiguration(r)
    /\ IsPrimary(r)
    /\ replicas[r].opNumber = replicas[r].commitNumber \* check if there is no uncommitted batch
    /\ replicas[r].batch = <<>>                        \* batch must be empty
    /\ \E config \in ConfigType:
        LET enMetaLog == [epochNumber |-> replicas[r].epochNumber + 1, config |-> config]
        IN /\ config /= replicas[r].config
           /\ replicas' = [
               replicas EXCEPT ![r].opNumber = @ + 1,
                               ![r].logs = Append(@, enMetaLog)
              ]
    /\ UNCHANGED <<committedLogs, nonce>>

HandleReconfigurationPrepareOk(r) == \* See 4.1.5 of the paper.
    /\ PreparingReconfiguration(r)
    /\ Cardinality({
            i \in Range(replicas[r].config): 
                /\ replicas[i].viewNumber = replicas[r].viewNumber
                /\ replicas[i].opNumber >= replicas[r].opNumber
                /\ replicas[i].status = "normal"
        }) >= majority(r) 
    /\ replicas[r].commitNumber /= replicas[r].opNumber
    /\ replicas' = 
        [
            replicas EXCEPT ![r].commitNumber = replicas[r].opNumber,
                            ![r].epochNumber = @ + 1,
                            ![r].status = "transitioning"
        ]
    /\ committedLogs' =
        committedLogs 
            \o
        SubSeq(replicas'[r].logs, Len(committedLogs) + 1, replicas'[r].commitNumber)

ReconfigurationProtocolNext == \* M of the scheme
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "shut down"
       /\ \/ HandleReconfigurationRequest(r)
          \/ HandleReconfigurationPrepareOk(r)
       
    /\ UNCHANGED <<committedLogs, nonce>>

=============================================================================
\* Modification History
\* Last modified Mon Jan 23 02:47:40 MSK 2023 by sandman
\* Created Sat Jan 21 06:40:06 MSK 2023 by sandman
