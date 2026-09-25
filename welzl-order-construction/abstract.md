# Constructing Welzl Orders: Algorithm and Correctness

This submission develops the construction in Dreier and Kuske,
*Near-Linear Time Computation of Welzl Orders on Graphs with Linear
Neighborhood Complexity* (arXiv:2602.14625v1). Its intended endpoint is the
randomized algorithmic claim in Lax195003. **That claim remains open.**

Seven component claims are proved: adjacent twin insertion, stability of
crossings under membership changes, the geometric contraction recurrence,
near-twin replacement in the registered set-system representation, the
uniform-sample avoidance bound, the finite random-key collision bound, and
correctness of checked reconstruction as an encoded graph Welzl order.

The program is an explicit fixed sequence of 5,213 word-RAM instructions.
Its readable source, compilation identity, and proofs for individual
implementation stages are provided in the proof package. Three separate
open claims state its worst-case running time, the correctness of its
successful outputs, and its finite-tape success probability. A checked
conditional assembly theorem shows that these three claims imply the exact
registered statement of Lax195003. It does not discharge those assumptions.

The submission imports the registered graph encoding, machine, graph-class,
and Welzl-order definitions. All seven component proofs have only the
archive's background axioms; the assembly proof additionally depends on
precisely the three explicitly open program claims.
