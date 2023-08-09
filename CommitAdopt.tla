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

EXTENDS Naturals, FiniteSets

CONSTANTS 
    P \* the set of processors
,   V \* the set of possible values
,   Bot \* the special value "bottom", indicating the absence of something
,   Lambda \* the failure notification "lambda"
,   NoCommit \* an indication that a processors didn't see a unanimous majority in round 1 of the algorithm

Distinct(s) == \A i,j \in DOMAIN s : i # j => s[i] \cap s[j] = {}
ASSUME Distinct(<<P,V,{Bot},{Lambda},{NoCommit}>>)

(* --algorithm CA {
    variables
      input \in [P -> V]; \* the processors' inputs
      sent = [p \in P |-> Bot]; \* messages sent in the current round
      received = [p \in P |-> [q \in P |-> Bot]]; \* message received by p from q in the current round
      rnd = 1; \* the current round (1, 2, or 3); we end at 3 but nothing happens in round 3
      output = [p \in P |-> Bot]; \* the processors' outputs
      participating = [r \in {1,2} |-> {}]; \* the set of participating processors in round r
      corrupted = [r \in {1,2} |-> {}]; \* the set of corrupted processors in round r
    define {
        \* first we make some auxiliary definitions
        \* the set of processors from which p received a message:
        HeardOf(rcvd) == {p \in P : rcvd[p] # Bot} 
        \* the set of minority subsets of S:
        Minority(S) == {M \in SUBSET S : 2*Cardinality(M)<Cardinality(S)} 
        VoteCount(rcvd, v) == Cardinality({p \in P : rcvd[p] = v})
        VotedByMajority(rcvd) == {v \in V : 2*VoteCount(rcvd, v) > Cardinality(HeardOf(rcvd))}
        MostVotedFor(rcvd) == {v \in V : \A w \in V \ {v} : VoteCount(rcvd, v) >= VoteCount(rcvd, w)}
        \* for technical reasons, we need the program counter of a processor in round r:
        Pc(r) == CASE r = 1 -> "r1" 
                [] r = 2 -> "r2"
                [] r = 3 -> "r3"
        \* Now the two safety properties:
        Agreement == \A p,q \in P : output[p] # Bot /\ output[q] # Bot /\ output[p][1] = "commit"
            => output[p][2] = output[q][2]
        Validity == \A p \in P : \A v \in V :
            pc[p] = "Done" /\ (\A q \in P : input[q] = v) => output[p] = <<"commit", v>>
    }
    macro broadcast(v) {
        sent := [sent EXCEPT ![self] = v]
    }
    \* The following macro is used to deliver messages to the processors.  It includes message corruptions by the advesary.
    macro deliver_msgs() {
        with (ByzMsg \in [P -> [corrupted[rnd] -> V\cup {Bot, Lambda, NoCommit}]]) {
            \* we assert the properties of the no-equivocation model:
            when \A p1,p2 \in P : \A q \in corrupted[rnd] :
                    ByzMsg[p1][q] \in V => ByzMsg[p2][q] \in {ByzMsg[p1][q], Lambda};
            received := [p \in P |-> [q \in P |->
                IF q \in corrupted[rnd]
                THEN ByzMsg[p][q]
                ELSE sent[q]]];
        };
    }
    \* Now the specification of the algorithm:
    fair process (proc \in P) {
        \* in round 1, vote for input[self]:
r1:     broadcast(input[self]);
r2:     await rnd = 2;
        \* if there is a majority for a value v, propose to commit v:
        if (VotedByMajority(received[self]) # {})
            with (v \in VotedByMajority(received[self])) \* the set is a singleton at this point
            broadcast(v)
        else
            broadcast(NoCommit);
r3:     await rnd = 3;
        if (VotedByMajority(received[self]) # {}) \* if there is a majority for a value v, commit v:
            with (v \in VotedByMajority(received[self])) \* the set is a singleton at this point
            output[self] := <<"commit", v>>
        else if (MostVotedFor(received[self]) # {}) \* otherwise, adopt a most voted value:
            with (v \in MostVotedFor(received[self])) \* there can be multiple values in the set
            output[self] := <<"adopt", v>>
        else \* if no value was voted for, adopt input:
            output[self] := <<"adopt", input[self]>>
    }
    (******************************************************************************)
    (* Below we specify the behavior of the adversary.  The no-equivocation model *)
    (* guarantees that if a processor receives v from p, then all receive v       *)
    (* or Lambda.                                                                 *)
    (******************************************************************************)
    fair process (adversary \in {"adversary"}) {
adv:    while (rnd < 3) {
            await \A p \in P : pc[p] = Pc(rnd+1);
            \* pick a participating set:
            with (Participating \in SUBSET P) {
                when Participating # {};
                participating[rnd] := Participating;
            };
            \* pick a set of corrupted processors:
            with (Corrupted \in Minority(participating[rnd]))
                corrupted[rnd] := Corrupted;
            deliver_msgs();
            rnd := rnd+1;
        }
    }
}
*)

\* Canary invariants that should break (this is to make sure that the specification reaches expected states):
Canary1 == \A p \in P : output[p] = Bot
Canary2 == \A p,q \in P : 
    /\ output[p] # Bot 
    /\ output[q] # Bot 
    => \neg (output[p][1] = "commit" /\ output[q][1] = "adopt")
Canary3 == \A p,q \in P : 
    /\ output[p] # Bot 
    /\ output[q] # Bot 
    => \neg (output[p][1] = "adopt" /\ output[q][1] = "adopt" /\ output[p][2] # output[q][2])

=============================================================================
\* Modification History
\* Last modified Sun Jan 01 16:07:58 PST 2023 by nano
\* Created Thu Dec 29 09:54:34 PST 2022 by nano
