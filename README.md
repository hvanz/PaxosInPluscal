# PaxosInPluscal
Paxos algorithm specified and proved in TLA+/Pluscal, with separate processes and invariants for proposers and acceptors.

The file PaxosPluscal.tla presents a version of the Paxos algorithm written in PlusCal, with its correspoding TLA+ spec, and a proof of the consistency property. In this specification, the two participants, acceptor and proposer, are modeled as disjoint processes, each with their own invariant properties.

The goal of this spec and proof is to obtain a low-level model of the algorithm, closer to an implementation in an imperative language, with disjoint invariants for the proposer and the acceptor, i.e., formulas that do not share variables (except one variable representing network communication). Consequently, ballots are modeled as tuples of ballot number and proposer id, the main processes are enclosed in an infinite loop, and proposers have a local variable that keep track of the acceptors that replied to it, which is used to compute quorums.

Additionally, this specification includes an optimization that allows a proposer to preempt and restart its execution when it receives a message from an acceptor with a higher ballot than its own. This spec was built starting from a simpler TLA+ spec of Paxos by Leslie Lamport, where only the acceptor was modeled.

Author: Hernán Vanzetto.
