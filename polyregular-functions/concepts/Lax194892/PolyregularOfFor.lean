import Lax194892.PolyregularFunctions
import Lax194892.ForTransducers

/-!
---
title: For-transducers compute polyregular functions
type: theorem
---
Every function computed by a for-transducer is polyregular (Theorem D.1.1 of
*Transducers*, the implication from for-transducer to polyregular). The program
is put in prenex form (Lemma D.1.3); the tuples of loop variables are
enumerated, in the order of the loops, by iterated marked squaring, and the
loop-free body is evaluated on each tuple by a rational function.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax194892.PolyregularOfFor

open Lax194892.PolyregularFunctions Lax194892.ForTransducers

/-- A function computed by a for-transducer is polyregular. -/
axiom isPolyregular_of_isForTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsForTransducer f) : IsPolyregular f

end Lax194892.PolyregularOfFor
