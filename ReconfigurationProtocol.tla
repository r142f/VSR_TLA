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
\*    /\ InLatestEpoch(r)
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

HandleReconfigurationPrepareOk(r) ==
    /\ PreparingReconfiguration(r)
    /\ 
        LET 
            enMetaLog == replicas[r].logs[Len(replicas[r].logs)]
        IN
           /\ Cardinality({
                   i \in Range(replicas[r].config): 
                       /\ replicas[i].viewNumber = replicas[r].viewNumber
                       /\ replicas[i].epochNumber = replicas[r].epochNumber
                       /\ replicas[i].opNumber >= replicas[r].opNumber
                       /\ \E l \in 1..Len(replicas[i].logs):
                           /\ replicas[i].logs[l] \in ENMetaLogType
                           /\ replicas[i].logs[l].epochNumber = enMetaLog.epochNumber
                           /\ replicas[i].logs[l].config = enMetaLog.config
                       /\ replicas[i].status = "normal"
               }) >= majority(r) 
           /\ replicas' = 
               [
                   replicas EXCEPT ![r].commitNumber = replicas[r].opNumber,
                                   ![r].epochNumber  = @ + 1,
                                   ![r].viewNumber   = IF r \in Range(enMetaLog.config)
                                                       THEN @ + 1
                                                       ELSE @,
                                   ![r].status       = IF r \in Range(enMetaLog.config)
                                                       THEN "view-change"
                                                       ELSE "shut down",
                                   ![r].oldConfig    = replicas[r].config,
                                   ![r].config       = enMetaLog.config
               ]

ProcessInTheNewGroup(r) ==
    /\ \E i \in 1..NumReplicas:
        /\ replicas[i].epochNumber > replicas[r].epochNumber
\*        /\ replicas[i].viewNumber >= replicas[r].viewNumber
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
                  /\ Download(i, r, enMetaLogIdx, TRUE)
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
                                             ![r].oldConfig    = replicas[r].config,
                                             ![r].config       = enMetaLog.config,
                                             ![r].batch        = <<>>,
                                             ![r].opNumber     = IF lcs = logs
                                                                 THEN Len(lcs)
                                                                 ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs         = IF lcs = logs
                                                                 THEN lcs \* TODO (remove) *\
                                                                 ELSE Append(lcs, logs[nextLogIdx])
                         ]           
           
ProcessInTheOldGroup(r) ==
    /\ \E i \in 1..NumReplicas:
        /\ replicas[i].epochNumber > replicas[r].epochNumber
\*        /\ replicas[i].viewNumber >= replicas[r].viewNumber
        /\ 
            LET
                enMetaLogIdx ==
                    CHOOSE l \in 1..Len(replicas[i].logs):
                        /\ replicas[i].logs[l] \in ENMetaLogType
                        /\ replicas[i].logs[l].epochNumber = replicas[i].epochNumber
                enMetaLog == replicas[i].logs[enMetaLogIdx]
            IN
\*            /\ Print(<<r, enMetaLog>>, TRUE) 
            /\ replicas[r].status /= "shut down"
            /\ ~ r \in Range(enMetaLog.config)
            /\ \/ /\ replicas[r].commitNumber < enMetaLogIdx - 1
                  /\ Download(i, r, enMetaLogIdx, TRUE)
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
                                             ![r].oldConfig    = replicas[r].config,
                                             ![r].config       = enMetaLog.config,
                                             ![r].batch        = <<>>,
                                             ![r].opNumber     = IF lcs = logs
                                                                 THEN Len(lcs)
                                                                 ELSE nextLogIdx,
                                             ![r].commitNumber = @ + 1,
                                             ![r].logs         = IF lcs = logs
                                                                 THEN lcs  \* TODO (remove) *\
                                                                 ELSE Append(lcs, logs[nextLogIdx])
                         ]  

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
\* Last modified Tue Apr 11 02:20:21 MSK 2023 by sandman
\* Created Sat Jan 21 06:40:06 MSK 2023 by sandman
