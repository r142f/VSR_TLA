--------------------------- MODULE NormalProtocol ---------------------------
EXTENDS Declarations

LOCAL INSTANCE Types
LOCAL INSTANCE Utils
LOCAL INSTANCE StateTransferProtocol
LOCAL INSTANCE ReconfigurationProtocol
                  
TryUpdateBatch(r) ==
    /\ IsPrimary(r)
    /\ ~ \E i \in 1..NumReplicas:                            \* check that we can accept request
        /\ replicas[i].epochNumber > replicas[r].epochNumber \* we lose our right to handle requests after new epoch commit
        /\ replicas[i].status = "normal"
        /\ IsPrimary(i)
    /\ ~ PreparingReconfiguration(r)                         \* during reconfiguration we stop requests handling
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
                          ![r].logs     = @ \o replicas[r].batch,
                          ![r].batch    = <<>>
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
    \/ TryUpdateBatch(r)
    \/ TryBroadcastPrepare(r)
         
HandlePrepare(r) == \* See 4.1.4 of the paper.
    LET 
        primary == replicas[GetPrimary(r)]
    IN
        /\ ~ IsPrimary(r)
        /\ primary.viewNumber = replicas[r].viewNumber
        /\ primary.epochNumber = replicas[r].epochNumber
        /\ primary.opNumber > replicas[r].opNumber
        /\ replicas' = [
                     replicas EXCEPT ![r].commitNumber = Min(replicas[r].opNumber + 1, primary.commitNumber),
                                     ![r].opNumber     = @ + 1,
                                     ![r].logs         = Append(@, primary.logs[replicas[r].opNumber + 1])
                 ]

HandlePrepareOk(r) == \* See 4.1.5 of the paper.
    /\ IsPrimary(r)
\*    /\ InLatestEpoch(r)
    /\ ~ PreparingReconfiguration(r)
    /\ replicas[r].opNumber > replicas[r].commitNumber
    /\
        LET
            l   == replicas[r].commitNumber + 1
            log == replicas[r].logs[l]
        IN
            /\ Cardinality({
                   i \in Range(replicas[r].config):
                       /\ replicas[i].viewNumber = replicas[r].viewNumber
                       /\ replicas[i].epochNumber = replicas[r].epochNumber
                       /\ replicas[i].opNumber >= l
                       /\ replicas[i].status = "normal"
               }) >= majority(r)
            /\ \/ /\ log \in ENMetaLogType
                  /\ replicas' = 
                    [
                        replicas EXCEPT ![r].commitNumber = l,
                                        ![r].epochNumber  = log.epochNumber,
                                        ![r].viewNumber   = IF r \in Range(log.config)
                                                            THEN @ + 1
                                                            ELSE @,
                                        ![r].status       = IF r \in Range(log.config)
                                                            THEN "view-change"
                                                            ELSE "shut down",
                                        ![r].oldConfig    = replicas[r].config,
                                        ![r].config       = log.config
                    ]
               \/ /\ ~ log \in ENMetaLogType
                  /\ replicas' = [replicas EXCEPT ![r].commitNumber = l]
    
HandleCommit(r) == \* See 4.1.7 of the paper.
    LET 
        primary == replicas[GetPrimary(r)]
    IN
        /\ primary.viewNumber = replicas[r].viewNumber
        /\ primary.epochNumber = replicas[r].epochNumber
        /\ primary.commitNumber > replicas[r].commitNumber
        /\ replicas[r].opNumber > replicas[r].commitNumber
        /\ replicas' = [replicas EXCEPT ![r].commitNumber = @ + 1]
    
NormalProtocolNext == \* M of the scheme
    /\ \E r \in 1..Len(replicas):
       /\ replicas[r].status = "normal"
       /\ \/ HandleRequest(r)
          \/ HandlePrepare(r)
          \/ HandlePrepareOk(r)
          \/ HandleCommit(r)
    /\ UNCHANGED <<nonce, vcCount>>

=============================================================================
\* Modification History
\* Last modified Fri Mar 31 20:40:03 MSK 2023 by sandman
\* Created Wed Nov 16 21:44:52 MSK 2022 by sandman
