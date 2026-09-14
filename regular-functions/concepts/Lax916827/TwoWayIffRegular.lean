import Lax916827.RegularFunctions
import Lax916827.TwoWayTransducers

/-!
---
title: Two-way transducers compute exactly the regular functions
type: theorem
---
A string-to-string function is computed by a two-way transducer if and only if
it is regular (Theorem C.2.9 of *Transducers*). The two implications are the
separate statements `TwoWayOfRegular` (Corollary C.2.8) and `RegularOfTwoWay`
(the decomposition into primes through the snake lemma); this statement is
their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax916827.TwoWayIffRegular

open Lax916827.RegularFunctions Lax916827.TwoWayTransducers

/-- A function is computed by a two-way transducer if and only if it is regular. -/
axiom isTwoWay_iff_isRegularFun {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsTwoWay f ↔ IsRegularFun f

end Lax916827.TwoWayIffRegular
