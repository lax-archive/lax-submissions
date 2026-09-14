import Lax132576.RationalRelations
import Lax132576.StringHomomorphisms

/-!
---
title: The complement of a homomorphism is rational
type: theorem
---
If $h : A^* \to B^*$ is a string homomorphism, then its complement
$$\{(w, v) \in A^* \times B^* \mid v \neq h(w)\}$$
is a rational relation (Claim B.1.7 of *Transducers*). The automaton guesses a
prefix of the input on which the homomorphism is applied correctly, then
insists on an error at the next letter: it outputs a proper prefix of the image
of that letter and nothing more, or a string incomparable with it and then
anything. This is the observation behind the undecidability of equivalence
(Theorem B.1.6).

# Formalization notes

Both alphabets are assumed finite, as in the book; the automaton has one
transition per letter and per prefix of its image.
-/

namespace Lax132576.HomomorphismComplement

open Lax132576.RationalRelations Lax132576.StringHomomorphisms

/-- The complement of the graph of a string homomorphism is a rational relation. -/
axiom isRationalRel_ne_homOf {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w)

end Lax132576.HomomorphismComplement
