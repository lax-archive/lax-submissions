import Lax132576.RationalFunctions
import Lax132576.WeightedAutomata

/-!
---
title: Functions that weighted automata can be pre-composed with are rational
type: theorem
---
If pre-composition with a function $f : A^* \to B^*$ preserves computability by
weighted automata over every semiring, then $f$ is rational: the implication
⇐ of Theorem B.3.6 of *Transducers*, its content. The book applies the
hypothesis to the weighted automaton over the semiring of regular languages
that maps a string to the singleton language of itself — the rational relations
are the weighted automata over that semiring — and reads a rational relation
computing the graph of $f$ off the resulting automaton.

# Formalization notes

The hypothesis quantifies over all semirings `S : Type` in the same universe as
the alphabets, which is where the semiring of regular languages over `B` lives.
Both alphabets are assumed finite.
-/

namespace Lax132576.RationalOfWeightedPrecomposition

open Lax132576.RationalFunctions Lax132576.WeightedAutomata

/-- A function with which every weighted automaton can be pre-composed is
rational. -/
axiom isRationalFun_of_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B)
    (h : ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f)) :
    IsRationalFun f

end Lax132576.RationalOfWeightedPrecomposition
