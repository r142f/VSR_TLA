---------------------- MODULE ReconfigurationProtocol ----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE StateTransferProtocol


PreparingReconfiguration(r) ==
    /\ IsPrimary(r)
    /\ Len(replicas[r].logs) > 0
    /\ replicas[r].logs[Len(replicas[r].logs)] \in ENMetaLogType
    /\ replicas[r].logs[Len(replicas[r].logs)].epochNumber = replicas[r].epochNumber + 1
    
HandleReconfigurationRequest(r) ==
    /\ IsPrimary(r)
    /\ replicas[r].status = "normal"
    /\ replicas[r].epochNumber < MaxEpochNumber
    /\ ~ PreparingReconfiguration(r)
    /\ replicas[r].opNumber = replicas[r].commitNumber \* check if there is no uncommitted batch
    /\ replicas[r].batch = <<>>                        \* batch must be empty
    /\ \E config \in ConfigType:
        LET enMetaLog == [epochNumber |-> replicas[r].epochNumber + 1, config |-> config]
        IN /\ ~ \E i \in Range(config): replicas[i].status = "recovering"
           /\ config /= replicas[r].config
           /\ replicas' = [
               replicas EXCEPT ![r].opNumber = @ + 1,
                               ![r].logs = Append(@, enMetaLog)
              ]
    /\ UNCHANGED <<committedLogs>>

HandleReconfigurationPrepareOk(r) ==
    /\ PreparingReconfiguration(r)
    /\ Cardinality({
            i \in Range(replicas[r].config): 
                /\ replicas[i].viewNumber = replicas[r].viewNumber
                /\ replicas[i].opNumber >= replicas[r].opNumber
                /\ \E l \in 1..Len(replicas[i].logs):
                    /\ replicas[i].logs[l] \in ENMetaLogType
                    /\ replicas[i].logs[l].epochNumber = replicas[r].logs[Len(replicas[r].logs)].epochNumber
                    /\ replicas[i].logs[l].config = replicas[r].logs[Len(replicas[r].logs)].config
                /\ replicas[i].status = "normal"
        }) >= majority(r) 
    /\ replicas[r].commitNumber /= replicas[r].opNumber
    /\ replicas' = 
        [
            replicas EXCEPT ![r].commitNumber = replicas[r].opNumber,
                            ![r].epochNumber = @ + 1,
                            ![r].viewNumber = IF r \in Range(replicas[r].logs[Len(replicas[r].logs)].config) THEN @ + 1 ELSE @,
                            ![r].status = IF r \in Range(replicas[r].logs[Len(replicas[r].logs)].config) THEN "view-change" ELSE "shut down",
                            ![r].oldConfig = replicas[r].config,
                            ![r].config = replicas[r].logs[Len(replicas[r].logs)].config
        ]
    /\ committedLogs' =
        committedLogs 
            \o
        SubSeq(replicas'[r].logs, Len(committedLogs) + 1, replicas'[r].commitNumber)


ProcessInTheNewGroup(r) ==
    /\ \E i \in 1..NumReplicas:
        /\ replicas[i].epochNumber > replicas[r].epochNumber
        /\ 
            LET
                enMetaLogIdx ==
                    CHOOSE l \in 1..Len(replicas[i].logs):
                        /\ replicas[i].logs[l] \in ENMetaLogType
                        /\ replicas[i].logs[l].epochNumber = replicas[i].epochNumber
                enMetaLog == replicas[i].logs[enMetaLogIdx]
            IN
            /\ replicas[i].commitNumber >= enMetaLogIdx
            /\ r \in Range(enMetaLog.config)
            /\ \/ /\ replicas[r].commitNumber < enMetaLogIdx - 1
                  /\ Download(i, r, enMetaLogIdx)
               \/ 
                  LET
                    logs == SafeSubSeq(replicas[i].logs, 1, enMetaLogIdx)
                    lcs == LongestCommonSubsequence(replicas[r].logs, logs)
                    nextLogIdx == Len(lcs) + 1
                  IN 
                     /\ replicas[r].commitNumber = enMetaLogIdx - 1
                     /\ replicas' = 
                         [
                             replicas EXCEPT ![r].status = "view-change",
                                             ![r].viewNumber = Max(replicas[r].viewNumber + 1, IF replicas[i].status = "shut down" THEN replicas[i].viewNumber + 1 ELSE replicas[i].viewNumber),
                                             ![r].epochNumber = enMetaLog.epochNumber,
                                             ![r].oldConfig = replicas[r].config,
                                             ![r].config = enMetaLog.config,
                                             ![r].batch = <<>>,
                                             ![r].opNumber = IF lcs = logs THEN @ ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs = IF lcs = logs THEN @ ELSE Append(lcs, logs[nextLogIdx])
                         ]
            /\ UNCHANGED <<committedLogs>>
           

ProcessInTheOldGroup(r) ==
    /\ \E i \in 1..NumReplicas:
        /\ replicas[i].epochNumber > replicas[r].epochNumber
        /\ 
            LET
                enMetaLogIdx ==
                    CHOOSE l \in 1..Len(replicas[i].logs):
                        /\ replicas[i].logs[l] \in ENMetaLogType
                        /\ replicas[i].logs[l].epochNumber = replicas[i].epochNumber
                enMetaLog == replicas[i].logs[enMetaLogIdx]
            IN
            /\ replicas[i].commitNumber >= enMetaLogIdx
            /\ r \in Range(replicas[i].oldConfig)
            /\ ~ r \in Range(enMetaLog.config)
            /\ \/ /\ replicas[r].commitNumber < enMetaLogIdx - 1
                  /\ Download(i, r, enMetaLogIdx)
               \/ 
                  LET
                    logs == SafeSubSeq(replicas[i].logs, 1, enMetaLogIdx)
                    lcs == LongestCommonSubsequence(replicas[r].logs, logs)
                    nextLogIdx == Len(lcs) + 1
                  IN 
                     /\ replicas[r].commitNumber = enMetaLogIdx - 1
                     /\ replicas' = 
                         [
                             replicas EXCEPT ![r].status = "shut down",
                                             ![r].viewNumber = IF replicas[i].status = "shut down" THEN replicas[i].viewNumber ELSE replicas[i].viewNumber - 1,
                                             ![r].epochNumber = enMetaLog.epochNumber,
                                             ![r].oldConfig = replicas[r].config,
                                             ![r].config = enMetaLog.config,
                                             ![r].batch = <<>>,
                                             ![r].opNumber = IF lcs = logs THEN @ ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs = IF lcs = logs THEN @ ELSE Append(lcs, logs[nextLogIdx])
                         ]
            /\ UNCHANGED <<committedLogs>>
  

ReconfigurationProtocolNext == \* M of the scheme
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "recovering"
       /\ \/ HandleReconfigurationRequest(r)
          \/ HandleReconfigurationPrepareOk(r)
          \/ ProcessInTheNewGroup(r)
          \/ ProcessInTheOldGroup(r)
       
    /\ UNCHANGED <<nonce, vcCount>>

=============================================================================
\* Modification History
\* Last modified Thu Mar 16 00:04:37 MSK 2023 by sandman
\* Created Sat Jan 21 06:40:06 MSK 2023 by sandman
