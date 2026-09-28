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
implementation stages are provided in the proof package. Of the three main
theorem concepts, the worst-case running-time and successful-output
correctness claims now have checked proofs. The finite-tape success
probability remains open. The assembly lemma consequently derives the exact
registered statement of Lax195003 conditional only on that probability claim.

Checked implementation lemmas cover canonical setup, persistent memory bounds,
exact finite-tape sampling, both accepted and rejected round paths, and the
complete guarded reduction phase. The literal driver, including its final
output routine, executes within 6,000(|x|+1)(L+1) source steps, where L is the
ceiling binary logarithm of n. The compiler bridge gives the registered
word-RAM bound for every tape. Quotient guards justify the products evaluated
by the program. The shrinking frontier preserves nonempty active sets,
zero-one indicators, counter identities, and log capacity. The near verifier
accepts exactly when its concrete representatives satisfy the required
distance bounds.

The whole reconstruction routine is verified at a cost of at most 100(n+1)
source steps. Its pointer writes restore precisely the vertices in each stored
interval, in source order, and its final traversal emits the certified list.
Every accepted round appends the verifier's concrete reduction, deletion slice,
and representatives to the history attached to the source arrays; the loop
carries this history into reconstruction. Empty and singleton inputs have
separate complete execution proofs.

The remaining work is to identify the concrete adaptive random process with
the proved finite-tape failure count. The compiler and abstract counting
bridges are checked, but this connection is necessary to discharge the
probability theorem.

The submission imports the registered graph encoding, machine, graph-class,
and Welzl-order definitions. The runtime and correctness proofs have only
the archive's background axioms; the assembly proof additionally depends on
the explicitly open probability claim.
