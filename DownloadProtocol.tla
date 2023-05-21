----------------------- MODULE DownloadProtocol -----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils

Download(from, to, logIdx, epochCatchup, startViewCatchup) == 
    LET
        logs == SafeSubSeq(replicas[from].logs, 1, logIdx)
        lcs == LongestCommonSubsequence(replicas[to].logs, logs)
        nextLogIdx == Len(lcs) + 1
    IN 
        LET
            needToCommit == 
                /\ replicas[to].commitNumber < replicas[from].commitNumber 
                /\ \/ /\ lcs /= logs
                      /\ replicas[to].commitNumber < nextLogIdx
                   \/ /\ lcs = logs
                      /\ replicas[to].commitNumber < Len(logs)
            logToCommitIdx == replicas[to].commitNumber + 1
            logToCommit ==
                IF needToCommit
                THEN logs[logToCommitIdx]
                ELSE 0
            needToCommitVNMetaLog == 
                /\ needToCommit
                /\ logToCommit \in VNMetaLogType
            needToCommitENMetaLog == 
                /\ needToCommit
                /\ logToCommit \in ENMetaLogType
            needToAddLog == 
                /\ lcs /= logs
                /\ replicas[to].commitNumber >= Min(replicas[from].commitNumber, Len(lcs)) \* first we commit, then we add logs *\
            needToAddVNMetaLog ==
               /\ needToAddLog
               /\ logs[nextLogIdx] \in VNMetaLogType
            needToEndRecovery ==
               /\ replicas[to].status = "recovering"
               /\ ~ needToCommit
               /\ ~ needToAddLog   
            needToEndStartViewCatchup ==
               /\ needToAddLog
               /\ nextLogIdx = Len(logs) 
        IN replicas' = 
           [
              replicas EXCEPT ![to].opNumber     = IF Len(lcs) < replicas[to].commitNumber
                                                   THEN -1
                                                   ELSE IF needToAddLog
                                                        THEN nextLogIdx
                                                        ELSE @,
                              ![to].commitNumber = IF needToCommit
                                                   THEN @ + 1
                                                   ELSE @,
                              ![to].logs         = IF needToAddLog
                                                   THEN Append(lcs, logs[nextLogIdx])
                                                   ELSE @,
                              ![to].viewNumber   = IF needToCommitVNMetaLog
                                                   THEN Max(logToCommit.viewNumber, @)
                                                   ELSE IF needToAddVNMetaLog
                                                        THEN Max(logs[nextLogIdx].viewNumber, @)
                                                        ELSE @,
                              ![to].epochNumber  = IF needToCommitENMetaLog
                                                   THEN logToCommit.epochNumber
                                                   ELSE @,
                              ![to].config       = IF needToCommitENMetaLog
                                                   THEN logToCommit.config
                                                   ELSE IF /\ replicas[from].epochNumber = 0
                                                           /\ @ = <<>>
                                                        THEN replicas[from].config
                                                        ELSE @,
                              ![to].seedReplica = IF \/ needToEndRecovery
                                                     \/ replicas[to].status /= "recovering"
                                                  THEN NULL
                                                  ELSE from,
                              ![to].status       =  IF /\ @ = "recovering"
                                                       /\ ~ needToEndRecovery
                                                    THEN @
                                                    ELSE IF /\ needToCommitENMetaLog
                                                            /\ ~ to \in Range(logToCommit.config)
                                                         THEN "shut down"
                                                         ELSE IF needToEndStartViewCatchup
                                                              THEN "normal"
                                                              ELSE IF startViewCatchup
                                                                   THEN "view-change"
                                                                   ELSE IF needToEndRecovery
                                                                        THEN IF to \in Range(replicas[from].config)
                                                                             THEN "normal"
                                                                             ELSE "shut down"
                                                                        ELSE IF epochCatchup
                                                                             THEN "epoch catchup"
                                                                             ELSE @
           ]                                                  
                                                        
=============================================================================
\* Modification History
\* Last modified Sat May 20 21:50:29 MSK 2023 by sandman
\* Created Thu Dec 01 20:54:50 MSK 2022 by sandman
