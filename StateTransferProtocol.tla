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
                            ![r].epochNumber = primary.epochNumber,
                            ![r].config = primary.config,
                            ![r].oldConfig = primary.oldConfig,
                            ![r].viewNumber = primary.viewNumber
                            
           ]
    /\ UNCHANGED <<committedLogs>>


=============================================================================
\* Modification History
\* Last modified Tue Jan 24 19:57:22 MSK 2023 by sandman
\* Created Thu Dec 01 20:54:50 MSK 2022 by sandman
