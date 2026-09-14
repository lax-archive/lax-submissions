import Lax765601.Continuity
import Lax194892.PebbleTransducers

/-!
---
title: Pebble transducers are continuous
type: theorem
---
Pebble transducers compute continuous functions (Theorem D.2.1 of
*Transducers*). The languages recognised by pebble automata — pebble
transducers with a yes/no answer — are regular, by induction on the number of
pebbles; running an automaton for the target language on the output turns the
transducer into a pebble automaton.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax194892.PebbleContinuity

open Lax765601.Continuity Lax194892.PebbleTransducers

/-- A function computed by a pebble transducer is continuous. -/
axiom continuous_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f

end Lax194892.PebbleContinuity
