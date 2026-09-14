import Lax194892.PebbleTransducers
import Lax194892.ForTransducers

/-!
---
title: Pebble transducers are computed by for-transducers
type: theorem
---
Every function computed by a pebble transducer is computed by a
for-transducer (Theorem D.2.4 of *Transducers*, the implication from pebble to
for-transducer). The run is organised as a tree of configurations; the
children of a configuration are produced by a for-transducer (Lemma D.2.5), and
iterating this over the height of the stack, with the output letters read off
the leaves, gives a polyregular function, hence a for-transducer.

# Formalization notes

Both alphabets are assumed finite, as in the book. The formal proof goes through
polyregularity by an induction on the number of pebbles rather than through
Lemma D.2.5.
-/

namespace Lax194892.ForOfPebble

open Lax194892.PebbleTransducers Lax194892.ForTransducers

/-- A function computed by a pebble transducer is computed by a for-transducer. -/
axiom isForTransducer_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsPebbleTransducer f) : IsForTransducer f

end Lax194892.ForOfPebble
