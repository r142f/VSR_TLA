----------------------- MODULE StateTransferProtocol -----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils

Download(from, to, logIdx) == 
    LET
        logs == SafeSubSeq(replicas[from].logs, 1, logIdx)
        lcs == LongestCommonSubsequence(replicas[to].logs, logs)
        nextLogIdx == Len(lcs) + 1
    IN 
        /\ \/ /\ replicas[to].commitNumber < replicas[from].commitNumber
              /\ replicas[to].commitNumber < Len(logs)
           \/ lcs /= logs
        /\
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
             IN replicas' = 
                [
                   replicas EXCEPT ![to].opNumber     =
                                      IF needToAddLog
                                      THEN nextLogIdx
                                      ELSE @,

                                   ![to].commitNumber =
                                      IF needToCommit
                                      THEN @ + 1
                                      ELSE @,

                                   ![to].logs         =
                                      IF needToAddLog
                                      THEN Append(lcs, logs[nextLogIdx])
                                      ELSE @,

                                   ![to].viewNumber   = 
                                       IF needToCommitVNMetaLog
                                       THEN Max(logToCommit.viewNumber, @)
                                       ELSE
                                            IF needToAddVNMetaLog
                                            THEN Max(logs[nextLogIdx].viewNumber, @)
                                            ELSE @,

                                   ![to].epochNumber  = 
                                       IF needToCommitENMetaLog
                                       THEN logToCommit.epochNumber
                                       ELSE @,

                                   ![to].oldConfig    = 
                                       IF needToCommitENMetaLog
                                       THEN replicas[to].config
                                       ELSE @,

                                   ![to].config       = 
                                       IF needToCommitENMetaLog
                                       THEN logToCommit.config
                                       ELSE @,

                                   ![to].status       = 
                                       IF 
                                           /\ needToCommitENMetaLog
                                           /\ ~ to \in Range(logToCommit.config)
                                       THEN "shut down"
                                       ELSE 
                                         IF 
                                            /\ @ = "view-change"      \* for handle start view change *\
                                            /\ needToAddLog
                                            /\ nextLogIdx = Len(logs)
                                         THEN "normal"
                                         ELSE @
                ]

=============================================================================
\* Modification History
\* Last modified Wed Mar 22 15:43:56 MSK 2023 by sandman
\* Created Thu Dec 01 20:54:50 MSK 2022 by sandman
