---------------------- MODULE ReconfigurationProtocol ----------------------
EXTENDS Declarations, TLC

LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE DownloadProtocol


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
        LET 
            enMetaLog == [
                epochNumber |-> replicas[r].epochNumber + 1,
                config      |-> config
            ]
        IN 
            /\ ~ \E i \in Range(config): replicas[i].status = "recovering"
            /\ config /= replicas[r].config
            /\ replicas' = [
                replicas EXCEPT ![r].opNumber = @ + 1,
                                ![r].logs     = Append(@, enMetaLog)
               ]

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
            /\ r \in Range(enMetaLog.config)
            /\ \/ /\ replicas[r].commitNumber < enMetaLogIdx - 1
                  /\ Download(i, r, enMetaLogIdx, TRUE, FALSE)
               \/ 
                  LET
                    logs == SafeSubSeq(replicas[i].logs, 1, enMetaLogIdx)
                    lcs == LongestCommonSubsequence(replicas[r].logs, logs)
                    nextLogIdx == Len(lcs) + 1
                  IN 
                     /\ replicas[r].commitNumber = enMetaLogIdx - 1
                     /\ replicas' = 
                         [
                             replicas EXCEPT ![r].status       = "view-change",
                                             ![r].viewNumber   = Max(
                                                                    replicas[r].viewNumber + 1,
                                                                    IF replicas[i].status = "shut down"
                                                                    THEN replicas[i].viewNumber + 1
                                                                    ELSE replicas[i].viewNumber
                                                                 ),
                                             ![r].epochNumber  = enMetaLog.epochNumber,
                                             ![r].config       = enMetaLog.config,
                                             ![r].batch        = <<>>,
                                             ![r].opNumber     = IF lcs = logs
                                                                 THEN @
                                                                 ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs         = IF lcs = logs
                                                                 THEN @
                                                                 ELSE Append(lcs, logs[nextLogIdx])
                         ]           
           
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
            /\ replicas[r].status /= "shut down"
            /\ ~ r \in Range(enMetaLog.config)
            /\ \/ /\ replicas[r].commitNumber < enMetaLogIdx - 1
                  /\ Download(i, r, enMetaLogIdx, TRUE, FALSE)
               \/ 
                  LET
                    logs == SafeSubSeq(replicas[i].logs, 1, enMetaLogIdx)
                    lcs == LongestCommonSubsequence(replicas[r].logs, logs)
                    nextLogIdx == Len(lcs) + 1
                  IN 
                     /\ replicas[r].commitNumber = enMetaLogIdx - 1
                     /\ replicas' = 
                         [
                             replicas EXCEPT ![r].status       = "shut down",
                                             ![r].viewNumber   = Max(@, replicas[i].viewNumber),
                                             ![r].epochNumber  = enMetaLog.epochNumber,
                                             ![r].config       = enMetaLog.config,
                                             ![r].batch        = <<>>,
                                             ![r].opNumber     = IF lcs = logs
                                                                 THEN @
                                                                 ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs         = IF lcs = logs
                                                                 THEN @
                                                                 ELSE Append(lcs, logs[nextLogIdx])
                         ]  

ReconfigurationProtocolNext ==
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status /= "recovering"
       /\ \/ HandleReconfigurationRequest(r)
          \/ ProcessInTheNewGroup(r)
          \/ ProcessInTheOldGroup(r)
    /\ UNCHANGED <<nonce, vcCount>>

=============================================================================
\* Modification History
\* Last modified Sat May 20 21:45:06 MSK 2023 by sandman
\* Created Sat Jan 21 06:40:06 MSK 2023 by sandman
