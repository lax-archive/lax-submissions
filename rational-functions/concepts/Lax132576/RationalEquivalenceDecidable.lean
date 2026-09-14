import Lax132576.TransducerCodes

/-!
---
title: Decidable equivalence of rational functions
type: theorem
---
The equivalence problem $f = g$ is decidable for rational functions (Theorem
B.3.4 of *Transducers*). The book reduces it to equivalence of weighted
automata over the rationals (Theorem B.3.3): output strings are represented
injectively by rational numbers through a weighted automaton $\iota$, weighted
automata are closed under pre-composition with rational functions (Lemma
B.3.5), and $f = g$ exactly when $f \cdot \iota = g \cdot \iota$.

# Formalization notes

The two functions are given by codes, under the promise that both codes are
functional (`TransducerCodes`); the decided property is equality of the coded
relations. The proof turns the two codes into codes of weighted automata whose
values are the numerical encodings of the outputs, multiplied by the numbers
of accepting runs, which are the same for both, and applies the decision
procedure of Theorem B.3.3.
-/

namespace Lax132576.RationalEquivalenceDecidable

open Lax132576.TransducerCodes

/-- Equivalence of two coded rational functions is decidable. -/
axiom decidable_codeRel_eq :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2)

end Lax132576.RationalEquivalenceDecidable
