import Lax765601.MealyMachine
import Lax916827.TwoWayTransducers

/-!
---
title: Two-way transducers are closed under pre-composition with Mealy machines
type: theorem
---
Functions computed by two-way transducers are closed under pre-composition with
Mealy machines (Lemma C.2.6 of *Transducers*). By the Krohn–Rhodes theorem it
suffices to pre-compose with a reversible and with a flip-flop machine: a
reversible machine can be run backwards, so its state at the head can be
maintained when the head moves left; a flip-flop machine's state at a position
is determined by the last resetting letter before it, which the two-way
transducer finds by a detour to the left.

# Formalization notes

All three alphabets are assumed finite, as in the book.
-/

namespace Lax916827.TwoWayMealyPrecomposition

open Lax765601.MealyMachine Lax916827.TwoWayTransducers

/-- Pre-composing a two-way transducer with a Mealy machine gives a two-way
transducer. -/
axiom isTwoWay_comp_isMealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsMealy f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f)

end Lax916827.TwoWayMealyPrecomposition
