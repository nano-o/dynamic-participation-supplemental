This repository contains supplemental material for the brief announcement "Byzantine Consensus Under Dynamic
Participation with a Well-Behaved Majority", to appear at DISC 2023.

# PlusCal/TLA+ specification of the no-equivocation simulation algorithm

See [NoEquivocation.tla](./NoEquivocation.tla) and its typeset version [NoEquivocation.pdf](./NoEquivocation.pdf).

[NoEquivocation_MC.tla](./NoEquivocation_MC.tla) and [NoEquivocation_MC.cfg](./NoEquivocation_MC.cfg) are
configuration files for the TLC model-checker. If you are using the TLA+ VSCode extension, you can
model-check the specification by opening [NoEquivocation_MC.tla](./NoEquivocation_MC.tla) and running TLC from
this file.

# PlusCal/TLA+ specification of the commit-adopt algorithm

See [CommitAdopt.tla](./CommitAdopt.tla) and its typeset version [CommitAdopt.pdf](./CommitAdopt.pdf).

[CommitAdopt_MC.tla](./CommitAdopt_MC.tla) and [CommitAdopt_MC.cfg](./CommitAdopt_MC.cfg) are
configuration files for the TLC model-checker. If you are using the TLA+ VSCode extension, you can
model-check the specification by opening [CommitAdopt_MC.tla](./CommitAdopt_MC.tla) and running TLC from
this file.
