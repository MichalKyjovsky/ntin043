----------------------------- MODULE OnlineShoppingPlatform -----------------------------

\* IMPORTS 
EXTENDS
    Naturals,
    Integers,
    Sequences,
    TLC,
    FiniteSets


VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"
           
Add1 == \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"
           
Next == Pick \/ Add1

=========================================================================================