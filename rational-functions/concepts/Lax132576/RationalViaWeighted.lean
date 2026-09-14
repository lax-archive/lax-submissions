import Lax132576.RationalFunctions
import Lax132576.WeightedAutomata

/-!
---
title: Rational functions characterised by weighted automata
type: theorem
---
A string-to-string function is rational if and only if weighted automata, over
every semiring, are closed under pre-composition with it (Theorem B.3.6 of
*Transducers*). The implication ⇒ is Lemma B.3.5 (`WeightedPrecomposition`) and
the implication ⇐ is `RationalOfWeightedPrecomposition`; this statement is
their conjunction.

# Formalization notes

Both alphabets are assumed finite; the semirings range over `Type`.
-/

namespace Lax132576.RationalViaWeighted

open Lax132576.RationalFunctions Lax132576.WeightedAutomata

/-- A function is rational if and only if every weighted automaton can be
pre-composed with it. -/
axiom isRationalFun_iff_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f)

end Lax132576.RationalViaWeighted
