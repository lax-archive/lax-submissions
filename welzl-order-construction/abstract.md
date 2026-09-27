This submission develops the construction in Dreier and Kuske,
*Near-Linear Time Computation of Welzl Orders on Graphs with Linear
Neighborhood Complexity* (arXiv:2602.14625v1). Its intended endpoint is the
randomized algorithmic claim in Lax195003. **That claim remains open.**

Seven supporting lemmas are proved: adjacent twin insertion, stability of
crossings under membership changes, the geometric contraction recurrence,
near-twin replacement in the registered set-system representation, the
uniform-sample avoidance bound, the finite random-key collision bound, and
correctness of checked reconstruction as an encoded graph Welzl order.

The program is an explicit fixed sequence of 5,213 word-RAM instructions.
Its readable source, compilation identity, and proofs for individual
implementation stages are provided in the proof package. The three main
theorems, still open, state its worst-case running time, the correctness of its
successful outputs, and its finite-tape success probability. A checked
conditional assembly lemma shows that these three claims imply the exact
registered statement of Lax195003. It does not discharge those assumptions.

Checked implementation lemmas cover canonical setup, persistent memory bounds,
exact finite-tape sampling, both accepted and rejected round paths, and the
entire guarded reduction loop with a near-linear source cost. The shrinking
frontier preserves nonempty active sets, zero-one indicators, counter identities,
and log capacity. The near verifier accepts exactly when its concrete
representatives satisfy the required distance bounds. Linked-list initialization,
individual logged insertions, and final output traversal are also verified.

The remaining work is to connect the guarded loop to the complete driver and
its reconstruction history, and identify the concrete adaptive random process
with the proved finite-tape failure count. The compiler and counting bridges
are checked, but these remaining connections are necessary to discharge the
three main theorems.

The submission imports the registered graph encoding, machine, graph-class,
and Welzl-order definitions. All seven component proofs have only the
archive's background axioms; the assembly proof additionally depends on
precisely the three explicitly open program claims.
