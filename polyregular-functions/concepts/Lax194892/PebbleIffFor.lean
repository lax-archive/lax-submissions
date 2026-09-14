import Lax194892.PebbleTransducers
import Lax194892.ForTransducers

/-!
---
title: Pebble transducers and for-transducers compute the same functions
type: theorem
---
Pebble transducers and for-transducers compute the same string-to-string
functions (Theorem D.2.4 of *Transducers*). The two implications are the
separate statements `ForOfPebble` and `PebbleOfFor`; this statement is their
conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax194892.PebbleIffFor

open Lax194892.PebbleTransducers Lax194892.ForTransducers

/-- A function is computed by a pebble transducer if and only if it is computed by
a for-transducer. -/
axiom isPebbleTransducer_iff_isForTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPebbleTransducer f ↔ IsForTransducer f

end Lax194892.PebbleIffFor
