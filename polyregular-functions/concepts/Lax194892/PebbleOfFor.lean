import Lax194892.PebbleTransducers
import Lax194892.ForTransducers

/-!
---
title: For-transducers are computed by pebble transducers
type: theorem
---
Every function computed by a for-transducer is computed by a pebble
transducer (Theorem D.2.4 of *Transducers*, the implication from for-transducer
to pebble). In prenex form the loop variables are pushed as pebbles, in the
order of the loops; the loop-free body is evaluated by a one-way pass with the
pebbles in place, since it can only compare positions, read letters and read
Boolean variables, which the state carries.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax194892.PebbleOfFor

open Lax194892.PebbleTransducers Lax194892.ForTransducers

/-- A function computed by a for-transducer is computed by a pebble transducer. -/
axiom isPebbleTransducer_of_isForTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsForTransducer f) : IsPebbleTransducer f

end Lax194892.PebbleOfFor
