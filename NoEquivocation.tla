---------------------------- MODULE NoEquivocation ----------------------------

EXTENDS Naturals, FiniteSets, Utilities, TLC

CONSTANT P, V, Lambda, Bot

ASSUME Distinct(<<P,V,{Bot},{Lambda}>>)

(* --algorithm NoEquivocation {
    variables
      input \in [P -> V];
      sent = [p \in P |-> Bot]; \* messages sent
      received = [p \in P |-> [q \in P |-> Bot]]; \* message received by p from q
      rnd = 1; \* 1..3
      output = [p \in P |-> [q \in P |-> Bot]];
      participating = [r \in {1,2} |-> {}];
      corrupted = {};
    define {
        TypeOkay == 
            /\ input \in [P -> V]
            /\ sent \in [P -> [P -> V\cup {Bot}] \cup V \cup {Bot}]
            /\ received \in [P -> [P -> [P -> V\cup {Bot}] \cup V \cup {Bot}]]
            /\ rnd \in {1,2,3}
            /\ output \in [P -> [P -> {Bot,Lambda} \cup V]]
            /\ participating \in [{1,2} -> SUBSET P]
            /\ corrupted \in SUBSET P
        HeardOf(p) == {q \in P : received[p][q] # Bot} \* heard of in the current round
        Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}
        NumHeardOf(p1, p2) == \* number of processes that report to p1 hearing from p2:
            Cardinality({q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot})
        NumHeardValue(p1, p2, v) == \* number of processes that report to p1 hearing v from p2:
            Cardinality({q \in P : received[p1][q] # Bot /\ received[p1][q][p2] = v})
        ValidOutput(p1, p2, v) ==
            /\ 2*NumHeardValue(p1, p2, v) > Cardinality(HeardOf(p1))
            /\ \A q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot => received[p1][q][p2] = v
        Output(p1, p2) ==
            IF \E v \in V : ValidOutput(p1, p2, v) \* true for at most one value v
            THEN CHOOSE v \in V : ValidOutput(p1, p2, v)
            ELSE
                IF \E q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot
                THEN Lambda
                ELSE Bot
        SimulatedParticipants == {p \in P : \E q \in P : output[q][p] # Bot}
        CorrectSimulatedParticipants == participating[1] \ corrupted
        \* Now we define the correctness properties of the algorithm:
        NoEquivocation == \A p1,p2,q \in P :
            output[p1][q] \in V /\ pc[p2] = "Done" => output[p2][q] \in {output[p1][q], Lambda}
        NoTampering == \A p,q \in P :
            /\ p \in CorrectSimulatedParticipants
            /\ pc[q] = "Done"
            => output[q][p] = input[p]
        MinorityCorruption == (\A p \in P : pc[p] = "Done") =>
            2*Cardinality(CorrectSimulatedParticipants) > Cardinality(SimulatedParticipants)
        Correctness == NoEquivocation /\ NoTampering /\ MinorityCorruption
    }
    macro broadcast(v) {
        sent := [sent EXCEPT ![self] = v]
    }
    (********************************************)
    (* We now specify the simulation algorithm: *)
    (********************************************)
    process (proc \in P) {
r1:     broadcast(input[self]);
r2:     await rnd = 2; 
        broadcast(received[self]);
r3:     await rnd = 3;
        output[self] := [p \in P |-> Output(self,p)];
    }
    (***********************************************************************)
    (* Below we specify the behavior of the adversary.                     *)
    (***********************************************************************)
    process (adversary \in {"adversary"}) {
a1:    await \A p \in P : pc[p] = "r2";
        \* pick a participating set:
        with (Participating \in SUBSET P) {
            when Participating # {};
            participating[rnd] := Participating;
        };
        \* pick a set whose messages will be tampered with:
        with (Corrupted \in Minority(participating[1]))
            corrupted := Corrupted;
        \* tamper with the messages:
        with(ByzVal \in [corrupted -> [P -> V\cup{Bot}]]) {
            received := [p \in P |-> [q \in P |-> 
                IF q \in corrupted
                \* in round 1, the adversary can make up any value:
                THEN ByzVal[q][p]
                ELSE
                    IF q \in participating[rnd] \ corrupted
                    THEN sent[q]
                    ELSE Bot]];
        };
        rnd := 2;
a2:     await \A p \in P : pc[p] = "r3";
        with (Participating \in SUBSET P) {
            when Participating # {};
            when corrupted \in Minority(Participating);
            participating[2] := Participating;
        };
        \* uncomment the following three lines to obtain a counter-example to MinorityCorruption under a growing adversary:
        \* with (Corrupted \in Minority(participating[2])) {
        \*     when corrupted \subseteq Corrupted;
        \*     corrupted := Corrupted };
        with (ByzVal \in [corrupted -> [P -> [P -> V\cup{Bot}] \cup {Bot}]]) {
            \* In round 2, the adversary can only lie by omission about non-corrupted processes (because of signatures):
            when \A p1 \in P : \A q \in corrupted : \A p2 \in (P \ corrupted) :
                IF ByzVal[q][p1] # Bot
                THEN 
                    IF p2 \in participating[1]
                    THEN ByzVal[q][p1][p2] \in {Bot,input[p2]} \* either the adversary reports not hearing from p1, or it reports p2's true input
                    ELSE ByzVal[q][p1][p2] = Bot
                ELSE TRUE; \* TODO: why does \/ short-circuiting not work here?
            received := [p \in P |-> [q \in P |-> 
                IF q \in corrupted
                THEN ByzVal[q][p]
                ELSE
                    IF q \in participating[rnd] \ corrupted
                    THEN sent[q]
                    ELSE Bot]];
        };
        rnd := 3;
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ae244ac" /\ chksum(tla) = "e5ad08d1")
VARIABLES input, sent, received, rnd, output, participating, corrupted, pc

(* define statement *)
TypeOkay ==
    /\ input \in [P -> V]
    /\ sent \in [P -> [P -> V\cup {Bot}] \cup V \cup {Bot}]
    /\ received \in [P -> [P -> [P -> V\cup {Bot}] \cup V \cup {Bot}]]
    /\ rnd \in {1,2,3}
    /\ output \in [P -> [P -> {Bot,Lambda} \cup V]]
    /\ participating \in [{1,2} -> SUBSET P]
    /\ corrupted \in SUBSET P
HeardOf(p) == {q \in P : received[p][q] # Bot}
Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}
NumHeardOf(p1, p2) ==
    Cardinality({q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot})
NumHeardValue(p1, p2, v) ==
    Cardinality({q \in P : received[p1][q] # Bot /\ received[p1][q][p2] = v})
ValidOutput(p1, p2, v) ==
    /\ 2*NumHeardValue(p1, p2, v) > Cardinality(HeardOf(p1))
    /\ \A q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot => received[p1][q][p2] = v
Output(p1, p2) ==
    IF \E v \in V : ValidOutput(p1, p2, v)
    THEN CHOOSE v \in V : ValidOutput(p1, p2, v)
    ELSE
        IF \E q \in P : received[p1][q] # Bot /\ received[p1][q][p2] # Bot
        THEN Lambda
        ELSE Bot
SimulatedParticipants == {p \in P : \E q \in P : output[q][p] # Bot}
CorrectSimulatedParticipants == participating[1] \ corrupted

NoEquivocation == \A p1,p2,q \in P :
    output[p1][q] \in V /\ pc[p2] = "Done" => output[p2][q] \in {output[p1][q], Lambda}
NoTampering == \A p,q \in P :
    /\ p \in CorrectSimulatedParticipants
    /\ pc[q] = "Done"
    => output[q][p] = input[p]
MinorityCorruption == (\A p \in P : pc[p] = "Done") =>
    2*Cardinality(CorrectSimulatedParticipants) > Cardinality(SimulatedParticipants)
Correctness == NoEquivocation /\ NoTampering /\ MinorityCorruption


vars == << input, sent, received, rnd, output, participating, corrupted, pc
        >>

ProcSet == (P) \cup ({"adversary"})

Init == (* Global variables *)
        /\ input \in [P -> V]
        /\ sent = [p \in P |-> Bot]
        /\ received = [p \in P |-> [q \in P |-> Bot]]
        /\ rnd = 1
        /\ output = [p \in P |-> [q \in P |-> Bot]]
        /\ participating = [r \in {1,2} |-> {}]
        /\ corrupted = {}
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "r1"
                                        [] self \in {"adversary"} -> "a1"]

r1(self) == /\ pc[self] = "r1"
            /\ sent' = [sent EXCEPT ![self] = (input[self])]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << input, received, rnd, output, participating, 
                            corrupted >>

r2(self) == /\ pc[self] = "r2"
            /\ rnd = 2
            /\ sent' = [sent EXCEPT ![self] = (received[self])]
            /\ pc' = [pc EXCEPT ![self] = "r3"]
            /\ UNCHANGED << input, received, rnd, output, participating, 
                            corrupted >>

r3(self) == /\ pc[self] = "r3"
            /\ rnd = 3
            /\ output' = [output EXCEPT ![self] = [p \in P |-> Output(self,p)]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << input, sent, received, rnd, participating, 
                            corrupted >>

proc(self) == r1(self) \/ r2(self) \/ r3(self)

a1(self) == /\ pc[self] = "a1"
            /\ \A p \in P : pc[p] = "r2"
            /\ \E Participating \in SUBSET P:
                 /\ Participating # {}
                 /\ participating' = [participating EXCEPT ![rnd] = Participating]
            /\ \E Corrupted \in Minority(participating'[1]):
                 corrupted' = Corrupted
            /\ \E ByzVal \in [corrupted' -> [P -> V\cup{Bot}]]:
                 received' =         [p \in P |-> [q \in P |->
                             IF q \in corrupted'
                             
                             THEN ByzVal[q][p]
                             ELSE
                                 IF q \in participating'[rnd] \ corrupted'
                                 THEN sent[q]
                                 ELSE Bot]]
            /\ rnd' = 2
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << input, sent, output >>

a2(self) == /\ pc[self] = "a2"
            /\ \A p \in P : pc[p] = "r3"
            /\ \E Participating \in SUBSET P:
                 /\ Participating # {}
                 /\ corrupted \in Minority(Participating)
                 /\ participating' = [participating EXCEPT ![2] = Participating]
            /\ \E Corrupted \in Minority(participating'[2]):
                 /\ corrupted \subseteq Corrupted
                 /\ corrupted' = Corrupted
            /\ \E ByzVal \in [corrupted' -> [P -> [P -> V\cup{Bot}] \cup {Bot}]]:
                 /\  \A p1 \in P : \A q \in corrupted' : \A p2 \in (P \ corrupted') :
                    IF ByzVal[q][p1] # Bot
                    THEN
                        IF p2 \in participating'[1]
                        THEN ByzVal[q][p1][p2] \in {Bot,input[p2]}
                        ELSE ByzVal[q][p1][p2] = Bot
                    ELSE TRUE
                 /\ received' =         [p \in P |-> [q \in P |->
                                IF q \in corrupted'
                                THEN ByzVal[q][p]
                                ELSE
                                    IF q \in participating'[rnd] \ corrupted'
                                    THEN sent[q]
                                    ELSE Bot]]
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

\* Stuff for TLC:

Canary1 == \neg (
    /\ \A p \in P : pc[p] = "Done"
    /\ \E p,q \in P : output[p][q] = Bot ) 
Canary2 == \neg (
    /\ \A p \in P : pc[p] = "Done"
    /\ \E p,q \in P : 
        /\ output[p][q] = Lambda 
        /\ \A p1,q1 \in P : (p1 # p \/ q1 # q) => output[p1][q1] # Lambda )
        
X \subset Y == X \subseteq Y /\ X # Y 
Maximal(Ss) == {S \in Ss : \A S2 \in Ss : \neg S \subset S2}
Minimal(Ss) == {S \in Ss : \A S2 \in Ss : \neg S2 \subset S}
Minority_TLC(S) ==
    IF \E M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)
    THEN 
        LET Ms == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}
        IN CHOOSE Ss \in SUBSET Maximal(Ms) : Cardinality(Ss) = 1
    ELSE {{}}

=============================================================================
