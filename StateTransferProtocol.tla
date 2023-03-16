----------------------- MODULE StateTransferProtocol -----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils

HandleNewState(r) == \* See 5.2 of the paper.
    LET
        primary == replicas[GetPrimary(r)]
    IN
        /\ ~ (primary.opNumber = replicas[r].opNumber /\ primary.viewNumber = replicas[r].viewNumber)
        /\ primary.opNumber > replicas[r].opNumber
        /\ primary.viewNumber >= replicas[r].viewNumber
        /\ primary.epochNumber = replicas[r].epochNumber
        /\ primary.status = "normal"
        /\ replicas' = [
            replicas EXCEPT ![r].opNumber = primary.opNumber,
                            ![r].logs = 
                                LET
                                    idxOfLastCommitedLog == replicas[r].commitNumber
                                    logs == IF primary.viewNumber = replicas[r].viewNumber THEN @ ELSE SafeSubSeq(@, 1, idxOfLastCommitedLog)
                                    idxOfPrimaryLog == primary.opNumber
                                    logsToAdd == SafeSubSeq(primary.logs, Len(logs) + 1, idxOfPrimaryLog)
                                IN logs \o logsToAdd,
                            ![r].commitNumber = primary.commitNumber,
\*                            ![r].epochNumber = primary.epochNumber,
\*                            ![r].config = primary.config,
\*                            ![r].oldConfig = primary.oldConfig,
                            ![r].viewNumber = primary.viewNumber
                            
           ]
    /\ UNCHANGED <<committedLogs>>

Download(from, to, logIdx) == 
    LET
        logs == SafeSubSeq(replicas[from].logs, 1, logIdx)
        lcs == LongestCommonSubsequence(replicas[to].logs, logs)
        nextLogIdx == Len(lcs) + 1
    IN 
        \/ /\ lcs /= logs
           /\ \/ /\ Len(lcs) = replicas[to].commitNumber
                 /\ replicas' = 
                       [
                          replicas EXCEPT ![to].opNumber = nextLogIdx,
                                          ![to].commitNumber = IF @ < replicas[from].commitNumber /\ @ < nextLogIdx THEN @ + 1 ELSE @,
                                          ![to].logs = Append(lcs, logs[nextLogIdx]),
                                          ![to].viewNumber = 
                                              IF 
                                                  /\ logs[nextLogIdx] \in VNMetaLogType
                                                  /\ nextLogIdx <= replicas[from].commitNumber
                                                  /\ logs[nextLogIdx].viewNumber > @
                                              THEN logs[nextLogIdx].viewNumber
                                              ELSE @,
                                          ![to].epochNumber = 
                                              IF 
                                                  /\ logs[nextLogIdx] \in ENMetaLogType
                                                  /\ nextLogIdx <= replicas[from].commitNumber
                                              THEN logs[nextLogIdx].epochNumber
                                              ELSE @,
                                          ![to].oldConfig = 
                                              IF 
                                                  /\ logs[nextLogIdx] \in ENMetaLogType
                                                  /\ nextLogIdx <= replicas[from].commitNumber
                                              THEN replicas[to].config
                                              ELSE @,
                                          ![to].config = 
                                              IF 
                                                  /\ logs[nextLogIdx] \in ENMetaLogType
                                                  /\ nextLogIdx <= replicas[from].commitNumber
                                              THEN logs[nextLogIdx].config
                                              ELSE @,
                                          ![to].status = 
                                              IF 
                                                  /\ logs[nextLogIdx] \in ENMetaLogType
                                                  /\ nextLogIdx <= replicas[from].commitNumber
                                                  /\ ~ to \in Range(logs[nextLogIdx].config)
                                              THEN "shut down"
                                              ELSE @
                       ]
               \/ /\ Len(lcs) > replicas[to].commitNumber
                  /\ replicas[from].commitNumber > replicas[to].commitNumber 
                  /\ replicas' = 
                       [
                          replicas EXCEPT ![to].commitNumber = @ + 1,
                                          ![to].viewNumber = 
                                              IF
                                                 /\ replicas[to].logs[replicas[to].commitNumber + 1] \in VNMetaLogType
                                                 /\ replicas[to].logs[replicas[to].commitNumber + 1].viewNumber > @
                                              THEN replicas[to].logs[replicas[to].commitNumber + 1].viewNumber
                                              ELSE @,
                                          ![to].epochNumber = 
                                              IF replicas[to].logs[replicas[to].commitNumber + 1] \in ENMetaLogType
                                              THEN replicas[to].logs[replicas[to].commitNumber + 1].epochNumber
                                              ELSE @,
                                          ![to].oldConfig = 
                                              IF replicas[to].logs[replicas[to].commitNumber + 1] \in ENMetaLogType
                                              THEN replicas[to].config
                                              ELSE @,
                                          ![to].config = 
                                              IF replicas[to].logs[replicas[to].commitNumber + 1] \in ENMetaLogType
                                              THEN replicas[to].logs[replicas[to].commitNumber + 1].config
                                              ELSE @,
                                          ![to].status = 
                                              IF 
                                                  /\ replicas[to].logs[replicas[to].commitNumber + 1] \in ENMetaLogType
                                                  /\ ~ to \in Range(replicas[to].logs[replicas[to].commitNumber + 1].config)
                                              THEN "shut down"
                                              ELSE @
                       ]
        \/ /\ lcs = logs
           /\ replicas[to].commitNumber < replicas[from].commitNumber
           /\ replicas[to].commitNumber < Len(logs)
           /\ replicas' = 
                 [
                    replicas EXCEPT ![to].commitNumber = @ + 1
                 ]
        
            
        

=============================================================================
\* Modification History
\* Last modified Wed Mar 15 18:21:51 MSK 2023 by sandman
\* Created Thu Dec 01 20:54:50 MSK 2022 by sandman
