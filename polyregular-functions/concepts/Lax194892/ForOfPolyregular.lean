import Lax194892.PolyregularFunctions
import Lax194892.ForTransducers

/-!
---
title: Polyregular functions are computed by for-transducers
type: theorem
---
Every polyregular function is computed by a for-transducer (Theorem D.1.1 of
*Transducers*, the implication from polyregular to for-transducer): marked
squaring is two nested loops, a regular function is computed by a two-way
transducer whose run a for-transducer replays, and for-transducers are closed
under composition (Lemma D.1.4).

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax194892.ForOfPolyregular

open Lax194892.PolyregularFunctions Lax194892.ForTransducers

/-- A polyregular function is computed by a for-transducer. -/
axiom isForTransducer_of_isPolyregular {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsPolyregular f) : IsForTransducer f

end Lax194892.ForOfPolyregular
