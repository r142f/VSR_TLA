----------------------- MODULE StateTransferProtocol -----------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils

\*_primary == replicas[GetPrimary(2)]
\*_idxOfLastCommitedLog == GetIdx(replicas[2].logs, "opNumber", replicas[2].commitNumber, CommonLogType)
\*_logs == IF _primary.viewNumber = replicas[2].viewNumber THEN replicas[2].logs ELSE SafeSubSeq(replicas[2].logs, 1, _idxOfLastCommitedLog)
\*_idxOfPrimaryLog == GetIdx(_primary.logs, "opNumber", _primary.opNumber, CommonLogType)
\*_logsToAdd == SafeSubSeq(_primary.logs, Len(_logs) + 1, _idxOfPrimaryLog)

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
                            ![r].viewNumber = primary.viewNumber
           ]
    /\ UNCHANGED <<committedLogs>>


=============================================================================
\* Modification History
\* Last modified Wed Jan 04 20:09:52 MSK 2023 by sandman
\* Created Thu Dec 01 20:54:50 MSK 2022 by sandman
