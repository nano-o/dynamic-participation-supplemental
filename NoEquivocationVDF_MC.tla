----------------- MODULE NoEquivocationVDF_MC --------------------

EXTENDS NoEquivocationVDF

CONSTANTS p1, p2, p3
P_MC == {p1,p2,p3}
Nat_MC == 0..3

Constraint == round \in Nat_MC

Canary1 == \A p \in P : done[p] < 3

==================================================================