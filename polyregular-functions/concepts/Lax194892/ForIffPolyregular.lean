import Lax194892.PolyregularFunctions
import Lax194892.ForTransducers

/-!
---
title: For-transducers compute exactly the polyregular functions
type: theorem
---
A string-to-string function is polyregular if and only if it is computed by a
for-transducer (Theorem D.1.1 of *Transducers*). The two implications are the
separate statements `ForOfPolyregular` and `PolyregularOfFor`; this statement
is their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax194892.ForIffPolyregular

open Lax194892.PolyregularFunctions Lax194892.ForTransducers

/-- A function is polyregular if and only if a for-transducer computes it. -/
axiom isPolyregular_iff_isForTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f

end Lax194892.ForIffPolyregular
