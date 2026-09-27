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

Checked implementation lemmas now cover canonical setup and persistent
memory bounds, sharper random-key costs summed over shrinking active sets,
the complete accepted-round log update, and linked reconstruction insertions.
A compiler bridge transfers complete source-level guarantees to each of the
three exact machine contracts. Adaptive failure bounds allow later random
block lengths to depend on earlier choices. The whole-loop invariant and
its connection to these bounds remain unfinished.

The submission imports the registered graph encoding, machine, graph-class,
and Welzl-order definitions. All seven component proofs have only the
archive's background axioms; the assembly proof additionally depends on
precisely the three explicitly open program claims.
