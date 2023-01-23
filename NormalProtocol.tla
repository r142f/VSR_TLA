--------------------------- MODULE NormalProtocol ---------------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE StateTransferProtocol
LOCAL INSTANCE ReconfigurationProtocol
                  
TryUpdateBatch(r) ==
    /\ IsPrimary(r)
    /\ ~ PreparingReconfiguration(r)
    /\ Len(replicas[r].batch) < 1                            \* only batches of size 1 are allowed (to minimize state space)
    /\ \/ replicas[r].opNumber > replicas[r].commitNumber    \* check if there is an uncommitted batch
       \/ /\ replicas[r].opNumber = replicas[r].commitNumber \* or force replica to prepare batch
          /\ replicas[r].batch = <<>>                        \* (since it didn't prepare it during committing)
    /\ \E request \in Requests:                              \* choose next unhandled request and update batch
       /\ ~ \E i \in 1..Len(replicas[r].logs):
           /\ replicas[r].logs[i] \in CommonLogType
           /\ replicas[r].logs[i].request = request
       /\ ~ \E i \in 1..Len(replicas[r].batch):
           /\ replicas[r].batch[i].request \in CommonLogType
           /\ replicas[r].batch[i].request = request
       /\ replicas' = [
              replicas EXCEPT ![r].batch = Append(
                @,
                [request |-> request]
              )
          ]

TryBroadcastPrepare(r) ==
    /\ IsPrimary(r)
    /\ replicas[r].opNumber = replicas[r].commitNumber \* check if there is no uncommitted batch
    /\ replicas[r].batch /= <<>>                       \* batch mustn't be empty
    /\ replicas' = [                                   \* update opNumber & logs, empty batch
          replicas EXCEPT ![r].opNumber = @ + Len(replicas[r].batch),
                          ![r].logs = @ \o replicas[r].batch,
                          ![r].batch = <<>>
       ]

(***************************************************************************)
(* In this implementation primary can't broadcast "Prepare" messages with  *)
(* the new requests until it has committed the previous requests.  Since   *)
(* batching is used, primary can do 1 of 2 things, when it gets a request: *)
(* add the request to the current batch if it didn't commit the previous   *)
(* batch yet or otherwise broadcast "Prepare" message with formed batch.   *)
(* See also 4.1.3 of the paper.                                            *)
(***************************************************************************)
HandleRequest(r) == 
    /\ \/ TryUpdateBatch(r)
       \/ TryBroadcastPrepare(r)
    /\ UNCHANGED <<committedLogs>>
         
HandlePrepare(r) == \* See 4.1.4 of the paper.
    LET 
        primary == replicas[GetPrimary(r)]
    IN
        /\ ~ IsPrimary(r)
        /\ primary.viewNumber = replicas[r].viewNumber
        /\ primary.opNumber > replicas[r].opNumber
        /\ replicas' = [
                     replicas EXCEPT ![r].opNumber = @ + 1,
                                     ![r].logs = Append(@, primary.logs[replicas[r].opNumber + 1])
                 ]
        /\ UNCHANGED <<committedLogs>> 
                   
HandlePrepareOk(r) == \* See 4.1.5 of the paper.
    /\ IsPrimary(r)
    /\ ~ PreparingReconfiguration(r)
    /\ Cardinality({
            i \in Range(replicas[r].config): 
                /\ replicas[i].viewNumber = replicas[r].viewNumber
                /\ replicas[i].opNumber >= replicas[r].opNumber
                /\ replicas[i].status = "normal"
        }) >= majority(r) 
    /\ replicas[r].commitNumber /= replicas[r].opNumber
    /\ replicas' = [replicas EXCEPT ![r].commitNumber = replicas[r].opNumber]
    /\ committedLogs' =
        committedLogs 
            \o
        SubSeq(replicas'[r].logs, Len(committedLogs) + 1, replicas'[r].commitNumber)
    
HandleCommit(r) == \* See 4.1.7 of the paper.
    LET 
        primary == replicas[GetPrimary(r)]
    IN
        /\ primary.viewNumber = replicas[r].viewNumber
        /\ primary.commitNumber > replicas[r].commitNumber
        /\ replicas[r].opNumber > replicas[r].commitNumber
        /\ replicas' = [replicas EXCEPT ![r].commitNumber = @ + 1]
        /\ UNCHANGED <<committedLogs>>        
    
NormalProtocolNext == \* M of the scheme
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status = "normal"
       /\ \/ HandleRequest(r)
          \/ HandlePrepare(r)
          \/ HandleNewState(r)
          \/ HandlePrepareOk(r)
          \/ HandleCommit(r)
    /\ UNCHANGED <<nonce>>

=============================================================================
\* Modification History
\* Last modified Mon Jan 23 02:49:13 MSK 2023 by sandman
\* Created Wed Nov 16 21:44:52 MSK 2022 by sandman
