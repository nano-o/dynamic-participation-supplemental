This repository contains supplemental material for the brief announcement [Byzantine Consensus Under Dynamic Participation with a Well-Behaved Majority](https://losa.fr/dynamic-consensus/brief-extended.pdf), to appear at DISC 2023.

The makefile typesets the specifications by default, and `make tlc` runs the TLC model-checker.

# PlusCal/TLA+ specification of the no-equivocation simulation algorithm

See [NoEquivocation.tla](./NoEquivocation.tla) and its typeset version [NoEquivocation.pdf](./NoEquivocation.pdf).

[NoEquivocation_MC.tla](./NoEquivocation_MC.tla) and [NoEquivocation_MC.cfg](./NoEquivocation_MC.cfg) are
configuration files for the TLC model-checker. If you are using the TLA+ VSCode extension, you can
model-check the specification by opening [NoEquivocation_MC.tla](./NoEquivocation_MC.tla) and running TLC from
this file.

An interesting bit is that the no-equivocation algorithm does not tolerate a growing adversary.
To get a counter-example to the correctness properties under a growing adversary, uncomment the lines as indicated in [NoEquivocation.tla](./NoEquivocation.tla) and run the TLC model-checker.

# PlusCal/TLA+ specification of the commit-adopt algorithm

See [CommitAdopt.tla](./CommitAdopt.tla) and its typeset version [CommitAdopt.pdf](./CommitAdopt.pdf).

[CommitAdopt_MC.tla](./CommitAdopt_MC.tla) and [CommitAdopt_MC.cfg](./CommitAdopt_MC.cfg) are
configuration files for the TLC model-checker. If you are using the TLA+ VSCode extension, you can
model-check the specification by opening [CommitAdopt_MC.tla](./CommitAdopt_MC.tla) and running TLC from
this file.

# Mechanically-checked proofs in Isabelle/HOL

We formalize the no-equivocation model in Isabelle/HOL and we prove the main lemma justifying the correctness of the commit-adopt algorithm.
You can browse the proof at [`DynamicConsensus/browser_info/DynamicConsensus.html`](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/dynamic-participation-supplemental/isabelle-proofs/DynamicConsensus/browser_info/DynamicConsensus.html).
The actual theory file (which must be opened using [Isabelle](https://isabelle.in.tum.de/)) is [`DynamicConsensus/DynamicConsensus.thy`](DynamicConsensus/DynamicConsensus.thy)
