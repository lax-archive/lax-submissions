import Lax132576.RationalFunctions
import Lax916827.TwoWayTransducers

/-!
---
title: Two-way transducers are closed under pre-composition with rational functions
type: theorem
---
Functions computed by two-way transducers are closed under pre-composition with
rational functions (Corollary C.2.7 of *Transducers*). By Theorem B.2.6 a
rational function is a composition of prime Mealy machines, their right-to-left
variants, homomorphisms and the separator function; Lemma C.2.6 handles the
Mealy machines, a right-to-left machine is handled symmetrically, and a
homomorphism is handled by simulating the head inside the image of a letter.

# Formalization notes

All three alphabets are assumed finite, as in the book.
-/

namespace Lax916827.TwoWayRationalPrecomposition

open Lax132576.RationalFunctions Lax916827.TwoWayTransducers

/-- Pre-composing a two-way transducer with a rational function gives a two-way
transducer. -/
axiom isTwoWay_comp_isRationalFun {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsRationalFun f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f)

end Lax916827.TwoWayRationalPrecomposition
