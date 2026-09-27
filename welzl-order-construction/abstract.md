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
complete guarded reduction phase. Setup and reduction take at most
5,600(|x|+1)(L+1) source steps, where L is the ceiling binary logarithm of n;
the public budget supplies the entire adaptive bit reserve. Quotient guards
justify the products evaluated by the program. The shrinking frontier preserves
nonempty active sets, zero-one indicators, counter identities, and log capacity.
The near verifier accepts exactly when its concrete representatives satisfy
the required distance bounds.

The whole reconstruction routine is verified at a cost of at most 100(n+1)
source steps, conditional on a certificate for its recorded log. Its pointer
writes restore precisely the vertices in each stored interval, in source order,
and its final traversal emits the certified list. A separate checked bridge
builds a graph reduction using that same concrete deletion order.

The remaining work is to carry these exact log certificates through every
accepted round of the driver, and to identify the concrete adaptive random
process with the proved finite-tape failure count. The compiler and counting
bridges are checked, but these remaining connections are necessary to discharge
the three main theorems.

The submission imports the registered graph encoding, machine, graph-class,
and Welzl-order definitions. All seven component proofs have only the
archive's background axioms; the assembly proof additionally depends on
precisely the three explicitly open program claims.
