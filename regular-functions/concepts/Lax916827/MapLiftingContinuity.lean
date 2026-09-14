import Lax765601.Continuity
import Lax765601.MapLifting

/-!
---
title: The map lifting of a continuous function is continuous
type: theorem
---
If a string-to-string function is continuous, then so is its map lifting
(Lemma C.1.3 of *Transducers*). An automaton for the inverse image of a regular
language under the map lifting guesses, for every block, the states of the
automaton for the language at its two ends, and checks the transitions across
the blocks by continuity of the lifted function and across the separators
directly.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.MapLiftingContinuity

open Lax765601.Continuity Lax765601.MapLifting

/-- The map lifting of a continuous function is continuous. -/
axiom continuous_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f)

end Lax916827.MapLiftingContinuity
