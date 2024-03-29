--------------------------------- MODULE CommitAdopt ---------------------------------

(***********************************************************************************)
(* This is a specification of the commit-adopt algorithm of `^Gafni^' and `^Losa^' *)
(* in the message-adversary model with dynamic participation. The specification is *)
(* written in `^PlusCal^' and TLA+.                                                *)
(*                                                                                 *)
(* The message-adversary model with dynamic participation is like the sleepy       *)
(* model, except that processes never fail; instead, the adversary corrupts their  *)
(* messages. This has the same effect as processes being faulty but is cleaner to  *)
(* model.                                                                          *)
(*                                                                                 *)
(* Note that, to check this specification with the `^TLC^' model-checker, you must *)
(* first translate the `^PlusCal^' algorithm to TLA+ using the TLA toolbox or the  *)
(* TLA+ `^VSCode^' extension.                                                      *)
(***********************************************************************************)

EXTENDS Naturals, FiniteSets, Utilities

CONSTANTS 
    P \* the set of processors
,   V \* the set of possible values
,   Bot \* the special value "bottom", indicating the absence of something
,   Lambda \* the failure notification "lambda"
,   NoCommit \* an indication that a processors didn't see a unanimous majority in round 1 of the algorithm

ASSUME Distinct(<<P,V,{Bot},{Lambda},{NoCommit}>>)

(* --algorithm CA {
    variables
      input \in [P -> V]; \* the processors' inputs
      sent = [p \in P |-> Bot]; \* messages sent in the current round
      \* message received by p from q in the current round; `Bot' means no message received:
      received = [p \in P |-> [q \in P |-> Bot]];
      rnd = 1; \* the current round (1, 2, or 3); we end at 3 but nothing happens in round 3
      \* the processors' outputs (either Bot, <<"commit",v>>, or <<"adopt",v>>) for some v
      output = [p \in P |-> Bot];
    define {
        TypeOkay == 
            /\ input \in [P -> V]
            /\ sent \in [P -> V\cup {Bot,NoCommit}]
            /\ received \in [P -> [P -> V\cup {Bot, NoCommit, Lambda}]]
            /\ rnd \in {1,2,3}
            /\ output \in [P -> {Bot} \cup {<<ca,v>> : ca \in {"commit", "adopt"}, v \in V}]
        \* the set of processors from which p received a message (i.e. heard of):
        HeardOf(p) == {q \in P : received[p][q] # Bot}
        \* the set of minority subsets of S:
        Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)} 
        \* the number of votes for v that p received:
        VoteCount(p, v) == Cardinality({q \in P : received[p][q] = v})
        \* the set of values v for which p received a strict majority of votes:
        VotedByMajority(p) == {v \in V : 2*VoteCount(p, v) > Cardinality(HeardOf(p))}
        \* the set containing the value voted for most often, if any, according to p's received messages:
        MostVotedFor(p) == {v \in V : \A w \in V \ {v} : VoteCount(p, v) > VoteCount(p, w)}
        \* for technical reasons, we need the program counter of a processor in round r:
        Pc(r) == CASE r = 1 -> "r1" 
                [] r = 2 -> "r2"
                [] r = 3 -> "r3"
        \* Now we give the two safety properties:
        Agreement == \A p,q \in P : output[p] # Bot /\ output[q] # Bot /\ output[p][1] = "commit"
            => output[p][2] = output[q][2]
        Validity == \A p \in P : \A v \in V :
            pc[p] = "Done" /\ (\A q \in P : input[q] = v) => output[p] = <<"commit", v>>
    }
    macro broadcast(v) {
        sent := [sent EXCEPT ![self] = v]
    }
    \* The following macro is used to deliver messages to the processors.  It includes message corruptions by the adversary:
    macro deliver_msgs(participating, corrupted) {
        with (ByzMsg \in [P -> [corrupted -> V\cup {Bot, Lambda, NoCommit}]]) {
            \* we assert the properties of the no-equivocation model:
            when \A p1,p2 \in P : \A q \in corrupted :
                    ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda};
            received := [p \in P |-> [q \in P |->
                IF q \in corrupted
                THEN ByzMsg[p][q] \* p receives a corrupted message
                ELSE IF q \in participating
                    THEN sent[q] \* p receives what q sent
                    ELSE Bot]] \* p receives nothing
        }
    }
    (***************************************************)
    (* Now we give the specification of the algorithm: *)
    (***************************************************)
    fair process (proc \in P) {
        \* in round 1, vote for input[self]:
r1:     broadcast(input[self]);
r2:     await rnd = 2;
        \* if there is a majority for a value v, propose to commit v:
        if (VotedByMajority(self) # {})
            with (v \in VotedByMajority(self)) \* the set is a singleton at this point
            broadcast(v)
        else
            broadcast(NoCommit);
r3:     await rnd = 3; \* in round 3 we just produce an output
        if (VotedByMajority(self) # {}) \* if there is a majority for a value v, commit v:
            with (v \in VotedByMajority(self)) \* the set is a singleton at this point
            output[self] := <<"commit", v>>
        else if (MostVotedFor(self) # {}) \* otherwise, adopt a most voted value:
            with (v \in MostVotedFor(self)) \* there can be multiple values in the set
            output[self] := <<"adopt", v>>
        else \* if no value was voted for, adopt an arbitrary value:
            with (v \in V)
            output[self] := <<"adopt", v>>
    }
    (******************************************************************************)
    (* Below we specify the behavior of the adversary.  The no-equivocation model *)
    (* guarantees that if a processor receives v from p, then all receive v       *)
    (* or Lambda.                                                                 *)
    (******************************************************************************)
    fair process (adversary \in {"adversary"}) {
adv:    while (rnd < 3) {
            await \A p \in P : pc[p] = Pc(rnd+1);
            \* pick a participating set and a set of corrupted processors:
            with (Participating \in SUBSET P \ {{}})
            with (Corrupted \in Minority(Participating))
                deliver_msgs(Participating, Corrupted);
            rnd := rnd+1;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "882cc78d" /\ chksum(tla) = "2a1f3d3d")
VARIABLES input, sent, received, rnd, output, pc

(* define statement *)
TypeOkay ==
    /\ input \in [P -> V]
    /\ sent \in [P -> V\cup {Bot,NoCommit}]
    /\ received \in [P -> [P -> V\cup {Bot, NoCommit, Lambda}]]
    /\ rnd \in {1,2,3}
    /\ output \in [P -> {Bot} \cup {<<ca,v>> : ca \in {"commit", "adopt"}, v \in V}]

HeardOf(p) == {q \in P : received[p][q] # Bot}

Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)}

VoteCount(p, v) == Cardinality({q \in P : received[p][q] = v})

VotedByMajority(p) == {v \in V : 2*VoteCount(p, v) > Cardinality(HeardOf(p))}

MostVotedFor(p) == {v \in V : \A w \in V \ {v} : VoteCount(p, v) > VoteCount(p, w)}

Pc(r) == CASE r = 1 -> "r1"
        [] r = 2 -> "r2"
        [] r = 3 -> "r3"

Agreement == \A p,q \in P : output[p] # Bot /\ output[q] # Bot /\ output[p][1] = "commit"
    => output[p][2] = output[q][2]
Validity == \A p \in P : \A v \in V :
    pc[p] = "Done" /\ (\A q \in P : input[q] = v) => output[p] = <<"commit", v>>


vars == << input, sent, received, rnd, output, pc >>

ProcSet == (P) \cup ({"adversary"})

Init == (* Global variables *)
        /\ input \in [P -> V]
        /\ sent = [p \in P |-> Bot]
        /\ received = [p \in P |-> [q \in P |-> Bot]]
        /\ rnd = 1
        /\ output = [p \in P |-> Bot]
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "r1"
                                        [] self \in {"adversary"} -> "adv"]

r1(self) == /\ pc[self] = "r1"
            /\ sent' = [sent EXCEPT ![self] = (input[self])]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << input, received, rnd, output >>

r2(self) == /\ pc[self] = "r2"
            /\ rnd = 2
            /\ IF VotedByMajority(self) # {}
                  THEN /\ \E v \in VotedByMajority(self):
                            sent' = [sent EXCEPT ![self] = v]
                  ELSE /\ sent' = [sent EXCEPT ![self] = NoCommit]
            /\ pc' = [pc EXCEPT ![self] = "r3"]
            /\ UNCHANGED << input, received, rnd, output >>

r3(self) == /\ pc[self] = "r3"
            /\ rnd = 3
            /\ IF VotedByMajority(self) # {}
                  THEN /\ \E v \in VotedByMajority(self):
                            output' = [output EXCEPT ![self] = <<"commit", v>>]
                  ELSE /\ IF MostVotedFor(self) # {}
                             THEN /\ \E v \in MostVotedFor(self):
                                       output' = [output EXCEPT ![self] = <<"adopt", v>>]
                             ELSE /\ \E v \in V:
                                       output' = [output EXCEPT ![self] = <<"adopt", v>>]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << input, sent, received, rnd >>

proc(self) == r1(self) \/ r2(self) \/ r3(self)

adv(self) == /\ pc[self] = "adv"
             /\ IF rnd < 3
                   THEN /\ \A p \in P : pc[p] = Pc(rnd+1)
                        /\ \E Participating \in SUBSET P \ {{}}:
                             \E Corrupted \in Minority(Participating):
                               \E ByzMsg \in [P -> [Corrupted -> V\cup {Bot, Lambda, NoCommit}]]:
                                 /\ \A p1,p2 \in P : \A q \in Corrupted :
                                       ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda}
                                 /\ received' =         [p \in P |-> [q \in P |->
                                                IF q \in Corrupted
                                                THEN ByzMsg[p][q]
                                                ELSE IF q \in Participating
                                                    THEN sent[q]
                                                    ELSE Bot]]
                        /\ rnd' = rnd+1
                        /\ pc' = [pc EXCEPT ![self] = "adv"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << received, rnd >>
             /\ UNCHANGED << input, sent, output >>

adversary(self) == adv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in P: proc(self))
           \/ (\E self \in {"adversary"}: adversary(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in P : WF_vars(proc(self))
        /\ \A self \in {"adversary"} : WF_vars(adversary(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Canary invariants that should break (this is to make sure that the specification reaches expected states):
\* To find a state in which some process outputs:
Canary1 == \A p \in P : output[p] = Bot
\* To find a state in which some process commits while another adopts:
Canary2 == \A p,q \in P : 
    /\ output[p] # Bot 
    /\ output[q] # Bot 
    => \neg (output[p][1] = "commit" /\ output[q][1] = "adopt")
\* To find a state in which two processes adopt different values:
Canary3 == \A p,q \in P : 
    /\ output[p] # Bot 
    /\ output[q] # Bot 
    => \neg (output[p][1] = "adopt" /\ output[q][1] = "adopt" /\ output[p][2] # output[q][2])

=============================================================================
\* Modification History
\* Last modified Sun Jan 01 16:07:58 PST 2023 by nano
\* Created Thu Dec 29 09:54:34 PST 2022 by nano
