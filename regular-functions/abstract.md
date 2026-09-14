Sections 1–3 of Part C of the book *Transducers* (M. Bojańczyk) as concepts
and proofs: the regular functions, defined as the compositions of rational
functions with map reverse and map duplicate, and their two machine models,
deterministic two-way transducers and streaming string transducers. The Lean
development is Aristotle's formalisation of the book, re-presented in the
archive's form; it requires the Part A and Part B submissions.

The definition-concepts are the regular functions (C.0.1), two-way
transducers (C.2.1) with their run semantics, codes of two-way transducers,
the string representation of the reachable configuration graph of a two-way
transducer, streaming string transducers (C.3.1), and snake graphs with their
outputs and widths.

The theorem-concepts are the numbered results: continuity and closure under
composition of the regular functions (C.1.1), continuity of reversal,
duplication (C.1.2) and map lifting (C.1.3), decidable equivalence of regular
functions given by two-way transducers (C.1.4), continuity of two-way
transducers (C.2.2, Rabin–Scott and Shepherdson) with the two lemmas on the
configuration graph (C.2.3, C.2.4), closure of two-way transducers under
composition (C.2.5, Chytil–Jákl) and under pre-composition with Mealy
machines and rational functions (C.2.6, C.2.7), the theorem that two-way
transducers compute exactly the regular functions (C.2.8, C.2.9, as two
implications and their conjunction), the closure properties of regular
functions under map lifting, concatenation and conditionals (C.2.10), the
sum of two regular functions (C.2.11, corrected on the empty input), the
snake lemma (C.2.12, for every width), and the equivalence of streaming string
transducers with the regular functions (C.3.2, Alur–Černý, as two
implications and their conjunction). All are proved.

The decidability of equivalence is proved not by the book's reduction to
weighted automata but by an explicit bound from the crossing-sequence
decomposition of a two-way run and Schützenberger's rank criterion; the
book's reduction is formalised as well, and the two agree. Conjecture C.1.5
is not formalised. The exercises are not part of this submission.
