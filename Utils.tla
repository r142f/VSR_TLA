------------------------------- MODULE Utils -------------------------------
EXTENDS Declarations

Range(T) == { T[x] : x \in DOMAIN T }

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == 
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
    
IndexPerms(n) == {key \in [1..n -> 1..n] : Range(key) = 1..n}

Perms(seq) ==
    {
        [i \in 1..Len(seq) |-> seq[perm[i]]]:
            perm \in IndexPerms(Len(seq))
    }

Min(a, b) == IF a < b THEN a ELSE b

Max(a, b) == IF a < b THEN b ELSE a

LongestCommonSubsequence(s1, s2) ==
    LET
        setOfIndices == {i \in 1..Min(Len(s1), Len(s2)): SubSeq(s1, 1, i) = SubSeq(s2, 1, i)} \cup {0}
        maxIndex == CHOOSE x \in setOfIndices: \A y \in setOfIndices: x >= y
    IN SubSeq(s1, 1, maxIndex)
    
SafeSubSeq(seq, from, to) == IF from > Len(seq) THEN <<>> ELSE IF to > Len(seq) THEN <<>> ELSE SubSeq(seq, from, to)

Insert(seq, elem, pos) == SubSeq(seq, 1, pos - 1) \o <<elem>> \o SubSeq(seq, pos, Len(seq))

Subset(set, size) == {subset \in SUBSET set: Cardinality(subset) = size}
    
GetIdx(seq, key, value, type) == 
    IF (
        \E i \in 1..Len(seq):
            /\ seq[i] \in type
            /\ seq[i][key] = value
    ) THEN (
        CHOOSE i \in 1..Len(seq):
            /\ seq[i] \in type
            /\ seq[i][key] = value
    ) ELSE 0
    
----

QuasiMaxViewNumber == MaxViewNumber + MaxEpochNumber + MaxNumFailures

ConfigSize(r) == Len(replicas[r].config)

f(r) ==  \* number of replicas that can fail simultaniously
    LET fs == {f_i \in 0..ConfigSize(r): 2*f_i + 1 <= ConfigSize(r)}
    IN CHOOSE f_i \in fs: 
        \A f_j \in fs:
            f_i >= f_j
                    
majority(r) == ConfigSize(r) \div 2 + 1

GetPrimary(r) == 
    LET
        primaryIdx == (replicas[r].viewNumber % ConfigSize(r)) + 1
    IN replicas[r].config[primaryIdx]

IsPrimary(r) == GetPrimary(r) = r   

ExistsFunctioningLatestConfig ==
    \E r \in 1..Len(replicas):
        /\ replicas[r].status /= "shut down"
        /\ \A r_j \in 1..Len(replicas):
                    replicas[r_j].epochNumber <= replicas[r].epochNumber

ReplicaWithLatestFunctioningConfig ==
    CHOOSE r \in 1..Len(replicas):
        /\ replicas[r].status /= "shut down"
        /\ \A r_j \in 1..Len(replicas):
            replicas[r_j].epochNumber <= replicas[r].epochNumber

LatestConfigReplicas == replicas[ReplicaWithLatestFunctioningConfig].config

=============================================================================
\* Modification History
\* Last modified Tue Feb 14 13:24:18 MSK 2023 by sandman
\* Created Wed Nov 16 21:32:33 MSK 2022 by sandman
