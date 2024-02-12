--------------------------------- MODULE CommitAdopt_MC ---------------------------------

EXTENDS CommitAdopt

CONSTANTS v1, v2, v3, p1, p2, p3, p4

\* P_MC == {p1, p2, p3, p4}
\* V_MC == {v1, v2, v3}
\* Checking the safety properties of the model took about one hour on a 2022 desktop computer.
\* To speed things up, try 3 processors and 2 values
P_MC == {p1, p2, p3}
V_MC == {v1, v2}

===============================================================================