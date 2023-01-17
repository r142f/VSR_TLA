------------------------------- MODULE Utils -------------------------------
EXTENDS Declarations

Range(T) == { T[x] : x \in DOMAIN T }

Seq2(S, n) == UNION {[1..m -> S] : m \in 1..n}

SetToSeq(set) ==
    IF Cardinality(set) = 0
    THEN <<>>
    ELSE CHOOSE x \in Seq2(set, Cardinality(set)) : Range(x) = set
    
IndexPerms(n) == {key \in [1..n -> 1..n] : Range(key) = 1..n}

Perms(seq) ==
    {
        [i \in 1..Len(seq) |-> seq[perm[i]]]:
            perm \in IndexPerms(Len(seq))
    }

Min(a, b) == IF a < b THEN a ELSE b

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

IsPrimary(r) == replicas[r].viewNumber % NumReplicas = r - 1   

GetPrimary(r) == (replicas[r].viewNumber % NumReplicas) + 1

f == NumReplicas \div 2 \* number of replicas that can fail simultaniously


=============================================================================
\* Modification History
\* Last modified Wed Jan 04 19:38:25 MSK 2023 by sandman
\* Created Wed Nov 16 21:32:33 MSK 2022 by sandman
