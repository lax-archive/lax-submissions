import Lax765601.Continuity
import Lax194892.PolyregularFunctions

/-!
---
title: Polyregular functions are continuous
type: theorem
---
Polyregular functions are continuous (Theorem D.0.2 of *Transducers*):
regular functions are, continuity is preserved by composition, and marked
squaring is continuous — an automaton for the target language is run on the
marked square from right to left, remembering the state transformation of the
underlined suffix and how the state transformation of the prefix transforms the
contribution of the suffix.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax194892.PolyregularContinuity

open Lax765601.Continuity Lax194892.PolyregularFunctions

/-- A polyregular function is continuous. -/
axiom continuous_of_isPolyregular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : Continuous f

end Lax194892.PolyregularContinuity
