----------------- MODULE NoEquivocationVDF --------------------

(***********************************************************************************)
(* Consider the Gorilla model. We want to implement a broadcast abstraction such   *)
(* that, each round, each well-behaved player receives more messages from          *)
(* well-behaved players than from ill-behaved players.                             *)
(*                                                                                 *)
(* We require that every message m carry a VDF evaluation VDF(m) and we assume     *)
(* that well-behaved players discount any messages unless it has a correct VDF     *)
(* evaluation.                                                                     *)
(*                                                                                 *)
(* However, just requiring that every message m carry a correct VDF evaluation     *)
(* VDF(m) is not enough for this because ill-behaved players could for example     *)
(* pre-compute VDF evaluations in one round to later use them in the next round in *)
(* order to overwhelm the well-behaved players.                                    *)
(*                                                                                 *)
(* To prevent this, we additionally require that each message include a set of     *)
(* (valid) messages from the previous round and that this set be big enough to     *)
(* ensure that it includes at least one message from a well-behaved player. This   *)
(* ensures that ill-behaved players cannot pre-compute VDF outputs. The trick is   *)
(* to figure out how to ensure that a set of messages contains at least one        *)
(* message from a well-behaved player. This is what the algorithm below does.      *)
(***********************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    P \* the set of players (could be infinite)

(*--algorithm NoEquivocation {
    variables
        msgs = [r \in Nat |-> [p \in P |-> {}]]; \* messages sent to each process each round
        round = 0; \* current round
        done = [p \in P |-> -1]; \* highest round in which each process participated
    macro SendAll(m) {
        msgs[round] := [p \in P |-> msgs[round][p] \cup {m}];
    }
    define {
        ValidSet(msgs, recvd) == \* whether msgs is a valid set of msgs given we received rcvd
            \* msgs is a set of messages from the previous round
            \* recvd is what we received in the current round
            \E S \in SUBSET msgs :
                /\ 2*Cardinality(S) > Cardinality(msgs)
                /\ \E R \in SUBSET recvd :
                    /\ 2*Cardinality(R) > Cardinality(recvd)
                    /\ \A r \in R : 
                        /\ S \subseteq r[2] \* r[2] is the set of messages attached to r
                        /\ 2*Cardinality(S) > Cardinality(r[2])
        \* in short: there is a majority among msgs that is a majority of a majority among recvd
    }
    process (proc \in P) 
        variables
            delivered = [r \in Nat |-> {}]; \* delivered broadcast messages
    {
l0:     SendAll(<<self>>);
        done[self] := 0; \* done for round 0
l1:     await round = 1;
        \* now deliver for round 0; we can deliver everything since the adversary cannot precompute VDF outputs before round 0
        delivered[0] := msgs[0][self];
        SendAll(<<self, delivered[0]>>); \* we attach all the delivered messages
        done[self] := 1; \* done for round 1
l2:     while (TRUE) {
            await round = done[self]+1;
            delivered[round-1] := {m \in msgs[round-1][self] : ValidSet(m[2], msgs[round-1][self])}
            SendAll(<<self, delivered[round-1]>>); \* we attach all the messages delivered for the previous round
            done[self] := round;
        }
    }
    process (clock \in {"clock"}) {
l0:    while (TRUE) {
            await \A p \in P : done[p] = round;
            round := round+1;
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "d8dd42ac" /\ chksum(tla) = "61bbbd1b")
\* Label l0 of process proc at line 36 col 9 changed to l0_
VARIABLES msgs, round, done, pc, delivered

vars == << msgs, round, done, pc, delivered >>

ProcSet == (P) \cup ({"clock"})

Init == (* Global variables *)
        /\ msgs = [r \in Nat |-> [p \in P |-> {}]]
        /\ round = 0
        /\ done = [p \in P |-> -1]
        (* Process proc *)
        /\ delivered = [self \in P |-> [r \in Nat |-> {}]]
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "l0_"
                                        [] self \in {"clock"} -> "l0"]

l0_(self) == /\ pc[self] = "l0_"
             /\ msgs' = [msgs EXCEPT ![round] = [p \in P |-> msgs[round][p] \cup {(<<self>>)}]]
             /\ done' = [done EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ UNCHANGED << round, delivered >>

l1(self) == /\ pc[self] = "l1"
            /\ round = 1
            /\ delivered' = [delivered EXCEPT ![self][0] = delivered[self][0] \cup msgs[0][self]]
            /\ msgs' = [msgs EXCEPT ![round] = [p \in P |-> msgs[round][p] \cup {(<<self, delivered'[self][0]>>)}]]
            /\ done' = [done EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ round' = round

l2(self) == /\ pc[self] = "l2"
            /\ round = done[self]+1
            /\ msgs' = [msgs EXCEPT ![round] = [p \in P |-> msgs[round][p] \cup {(<<self, delivered[self][round-1]>>)}]]
            /\ done' = [done EXCEPT ![self] = round]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << round, delivered >>

proc(self) == l0_(self) \/ l1(self) \/ l2(self)

l0(self) == /\ pc[self] = "l0"
            /\ \A p \in P : done[p] = round
            /\ round' = round+1
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << msgs, done, delivered >>

clock(self) == l0(self)

Next == (\E self \in P: proc(self))
           \/ (\E self \in {"clock"}: clock(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================
