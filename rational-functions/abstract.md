Part B of the book *Transducers* (M. Bojańczyk) as concepts and proofs: the
rational relations and the rational functions, one step up the transducer
ladder from Mealy machines. The Lean development is Aristotle's formalisation
of the book, re-presented in the archive's form; it requires the Part A
submission for continuity, Mealy machines and the composition closure, and
assumes the undecidability of the Post correspondence problem from the
archive's submission on it.

The definition-concepts are the automata with labelled transitions that
underlie the two nondeterministic models, nondeterministic automata with
output and the rational relations (B.1.1, B.1.2), rational functions
(B.2.1), string homomorphisms, bimachines (B.2.2), the prime rational
functions of Theorem B.2.6, finite codes of automata and decidability under
a promise, weighted automata (B.3.2) and their codes over $\mathbb{Q}$,
sequential and subsequential transducers, the left distance (B.4.7) with
bounded variation, and automata with extended transitions.

The theorem-concepts are the numbered results of Part B: closure of rational
relations under composition and their continuity (B.1.4, B.1.5), the
undecidability of their equivalence (B.1.6, Griffiths) with the rationality
of the complement of a homomorphism (B.1.7), Eilenberg's theorem that
rational functions, unambiguous automata and bimachines coincide (B.2.3, as
three implications and their conjunction), the elimination of
$\varepsilon$-transitions (B.2.4, in its two forms), uniformisation (B.2.5),
the decomposition into prime rational functions (B.2.6, both directions and
the biconditional), which rational functions are Mealy machines (B.2.7),
Schützenberger's decidability of equivalence and of zeroness for weighted
automata over $\mathbb{Q}$ (B.3.3, B.3.7), decidable equivalence of rational
functions (B.3.4), closure of weighted automata under pre-composition with
rational functions and the resulting characterisation (B.3.5, B.3.6), and the
machine-independent characterisations of Mealy machines (B.4.1, with its
decidability B.4.2, B.4.3, B.4.4, B.4.5), of sequential functions (B.4.6,
Ginsburg–Rose), of subsequential functions (B.4.8, Choffrut) and of rational
functions (B.4.13, Reutenauer–Schützenberger). All are proved.

Decidability statements are about finite codes of automata over the alphabet
$\mathbb{N}$ and are relativised to the letters a code mentions, since no
code describes a total function on all of $\mathbb{N}^*$. Definition B.1.3
(rational and recognisable subsets of a monoid) is not formalised; Claims
B.4.9–B.4.12 are internal steps of B.4.8 and appear only inside its proof.
The exercises of Part B are not part of this submission.
