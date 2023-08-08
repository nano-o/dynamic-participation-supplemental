--------------------------------- MODULE CA ---------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS P, V, Bot, Lambda, NoCommit

Distinct(s) == \A i,j \in DOMAIN s : i # j => s[i] \cap s[j] = {}
ASSUME Distinct(<<P,V,{Bot},{Lambda},{NoCommit}>>)

(* --algorithm CA {
    variables
      input \in [P -> V];
      sent = [p \in P |-> Bot]; \* messages sent
      received = [p \in P |-> [q \in P |-> Bot]]; \* message received by p from q
      rnd = 1; \* 1..3
      output = [p \in P |-> Bot];
      participating = [r \in {1,2} |-> {}];
      corrupted = [r \in {1,2} |-> {}];
    define {
        HeardOf(rcvd) == {p \in P : rcvd[p] # Bot}
        Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}
        VoteCount(rcvd, v) == Cardinality({p \in P : rcvd[p] = v})
        VotedByMajority(rcvd) == {v \in V : 2*VoteCount(rcvd, v) > Cardinality(HeardOf(rcvd))}
        MostVotedFor(rcvd) == {v \in V : \A w \in V \ {v} : VoteCount(rcvd, v) >= VoteCount(rcvd, w)}
        Canary1 == \A p \in P : output[p] = Bot
        Canary2 == \A p,q \in P : output[p] # Bot /\ output[q] # Bot => \neg (output[p][1] = "commit" /\ output[q][1] = "adopt")
        Canary3 == \A p,q \in P : output[p] # Bot /\ output[q] # Bot => \neg (output[p][1] = "adopt" /\ output[q][1] = "adopt" /\ output[p][2] # output[q][2])
        Agreement == \A p,q \in P : output[p] # Bot /\ output[q] # Bot /\ output[p][1] = "commit"
            => output[p][2] = output[q][2]
        Validity == \A p \in P : \A v \in V :
            pc[p] = "Done" /\ (\A q \in P : input[q] = v) => output[p] = <<"commit", v>>
    }
    macro broadcast(v) {
        sent := [sent EXCEPT ![self] = v]
    }
    macro deliver_msgs() {
        with (ByzMsg \in [P -> [corrupted[rnd] -> V\cup {Bot, Lambda, NoCommit}]]) {
            when \A p1,p2 \in P : \A q \in corrupted[rnd] :
                    ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda};
            received := [p \in P |-> [q \in P |->
                IF q \in corrupted[rnd]
                THEN ByzMsg[p][q]
                ELSE sent[q]]];
        };
    }
    process (proc \in P) {
        \* vote for input[self]:
r1:     broadcast(input[self]);
r2:     await rnd = 2;
        \* if there is a majority for a value v, propose to commit v:
        if (VotedByMajority(received[self]) # {})
            with (v \in VotedByMajority(received[self]))
            broadcast(v)
        else
            broadcast(NoCommit);
r3:     await rnd = 3;
        if (VotedByMajority(received[self]) # {}) \* if there is a majority for a value v, commit v:
            with (v \in VotedByMajority(received[self]))
            output[self] := <<"commit", v>>
        else if (MostVotedFor(received[self]) # {}) \* otherwise, adopt the most voted value:
            with (v \in MostVotedFor(received[self]))
            output[self] := <<"adopt", v>>
        else \* if no value was voted for, adopt input:
            output[self] := <<"adopt", input[self]>>
    }
    (******************************************************************************)
    (* Below we specify the behavior of the adversary.  The no-equivocation model *)
    (* guarantees that if a processor receive v from p, then all receive v        *)
    (* or Lambda (but they do hear from p).                                       *)
    (******************************************************************************)
    process (adversary \in {"adversary"}) {
        \* TODO : while(rnd < 3) { ... }
a1:     await \A p \in P : pc[p] = "r2";
        \* pick a participating set:
        with (Participating \in SUBSET P) {
            when Participating # {};
            participating[rnd] := Participating;
        };
        \* pick a set of corrupted processors:
        with (Corrupted \in Minority(participating[rnd]))
            corrupted[rnd] := Corrupted;
        deliver_msgs();
        rnd := 2;
a2:     await \A p \in P : pc[p] = "r3";
        with (Participating \in SUBSET P) {
            when Participating # {};
            participating[rnd] := Participating;
        };
        with (Corrupted \in Minority(participating[rnd]))
            corrupted[2] := Corrupted;
        deliver_msgs();
        rnd := 3;
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "559bc7bd" /\ chksum(tla) = "37277062")
VARIABLES input, sent, received, rnd, output, participating, corrupted, pc

(* define statement *)
HeardOf(rcvd) == {p \in P : rcvd[p] # Bot}
Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}
VoteCount(rcvd, v) == Cardinality({p \in P : rcvd[p] = v})
VotedByMajority(rcvd) == {v \in V : 2*VoteCount(rcvd, v) > Cardinality(HeardOf(rcvd))}
MostVotedFor(rcvd) == {v \in V : \A w \in V \ {v} : VoteCount(rcvd, v) >= VoteCount(rcvd, w)}
Canary1 == \A p \in P : output[p] = Bot
Canary2 == \A p,q \in P : output[p] # Bot /\ output[q] # Bot => \neg (output[p][1] = "commit" /\ output[q][1] = "adopt")
Canary3 == \A p,q \in P : output[p] # Bot /\ output[q] # Bot => \neg (output[p][1] = "adopt" /\ output[q][1] = "adopt" /\ output[p][2] # output[q][2])
Safety == \A p,q \in P : output[p] # Bot /\ output[q] # Bot /\ output[p][1] = "commit"
    => output[p][2] = output[q][2]
Liveness == \A p \in P : \A v \in V :
    pc[p] = "Done" /\ (\A q \in P : input[q] = v) => output[p] = <<"commit", v>>


vars == << input, sent, received, rnd, output, participating, corrupted, pc
        >>

ProcSet == (P) \cup ({"adversary"})

Init == (* Global variables *)
        /\ input \in [P -> V]
        /\ sent = [p \in P |-> Bot]
        /\ received = [p \in P |-> [q \in P |-> Bot]]
        /\ rnd = 1
        /\ output = [p \in P |-> Bot]
        /\ participating = [r \in {1,2} |-> {}]
        /\ corrupted = [r \in {1,2} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "r1"
                                        [] self \in {"adversary"} -> "a1"]

r1(self) == /\ pc[self] = "r1"
            /\ sent' = [sent EXCEPT ![self] = (input[self])]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << input, received, rnd, output, participating, 
                            corrupted >>

r2(self) == /\ pc[self] = "r2"
            /\ rnd = 2
            /\ IF VotedByMajority(received[self]) # {}
                  THEN /\ \E v \in VotedByMajority(received[self]):
                            sent' = [sent EXCEPT ![self] = v]
                  ELSE /\ sent' = [sent EXCEPT ![self] = "no-commit"]
            /\ pc' = [pc EXCEPT ![self] = "r3"]
            /\ UNCHANGED << input, received, rnd, output, participating, 
                            corrupted >>

r3(self) == /\ pc[self] = "r3"
            /\ rnd = 3
            /\ IF VotedByMajority(received[self]) # {}
                  THEN /\ \E v \in VotedByMajority(received[self]):
                            output' = [output EXCEPT ![self] = <<"commit", v>>]
                  ELSE /\ IF MostVotedFor(received[self]) # {}
                             THEN /\ \E v \in MostVotedFor(received[self]):
                                       output' = [output EXCEPT ![self] = <<"adopt", v>>]
                             ELSE /\ output' = [output EXCEPT ![self] = <<"adopt", input[self]>>]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << input, sent, received, rnd, participating, 
                            corrupted >>

proc(self) == r1(self) \/ r2(self) \/ r3(self)

a1(self) == /\ pc[self] = "a1"
            /\ \A p \in P : pc[p] = "r2"
            /\ \E Participating \in SUBSET P:
                 /\ Participating # {}
                 /\ participating' = [participating EXCEPT ![rnd] = Participating]
            /\ \E Corrupted \in Minority(participating'[rnd]):
                 corrupted' = [corrupted EXCEPT ![rnd] = Corrupted]
            /\ \E ByzMsg \in [P -> [corrupted'[rnd] -> V\cup {Bot, Lambda}]]:
                 /\ \A p1,p2 \in P : \A q \in corrupted'[rnd] :
                       ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda}
                 /\ received' =         [p \in P |-> [q \in P |->
                                IF q \in corrupted'[rnd]
                                THEN ByzMsg[p][q]
                                ELSE sent[q]]]
            /\ rnd' = 2
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << input, sent, output >>

a2(self) == /\ pc[self] = "a2"
            /\ \A p \in P : pc[p] = "r3"
            /\ \E Participating \in SUBSET P:
                 /\ Participating # {}
                 /\ participating' = [participating EXCEPT ![rnd] = Participating]
            /\ \E Corrupted \in Minority(participating'[rnd]):
                 corrupted' = [corrupted EXCEPT ![2] = Corrupted]
            /\ \E ByzMsg \in [P -> [corrupted'[rnd] -> V\cup {Bot, Lambda}]]:
                 /\ \A p1,p2 \in P : \A q \in corrupted'[rnd] :
                       ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda}
                 /\ received' =         [p \in P |-> [q \in P |->
                                IF q \in corrupted'[rnd]
                                THEN ByzMsg[p][q]
                                ELSE sent[q]]]
            /\ rnd' = 3
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << input, sent, output >>

adversary(self) == a1(self) \/ a2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in P: proc(self))
           \/ (\E self \in {"adversary"}: adversary(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* StateConstraint1 == corrupted[1] \in {{},{p1}} /\ corrupted[2] \in {{},{p1,p2}} /\ participating[1] \in {{},{p1,p2,p4}} /\ participating[2] \in {{},P}

=============================================================================
\* Modification History
\* Last modified Sun Jan 01 16:07:58 PST 2023 by nano
\* Created Thu Dec 29 09:54:34 PST 2022 by nano
