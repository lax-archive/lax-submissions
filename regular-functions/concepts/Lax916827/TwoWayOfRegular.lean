import Lax916827.RegularFunctions
import Lax916827.TwoWayTransducers

/-!
---
title: Every regular function is computed by a two-way transducer
type: theorem
---
Every regular function is computed by a two-way transducer (Corollary C.2.8 of
*Transducers*). Two-way transducers are closed under composition (Theorem
C.2.5) and contain the rational functions (Corollary C.2.7), and map reverse
and map duplicate are computed by explicit two-way transducers that sweep each
block backwards, respectively twice.

# Formalization notes

Both alphabets are assumed finite; the induction on the composition tree uses
the finiteness of the intermediate alphabets built into the closure.
-/

namespace Lax916827.TwoWayOfRegular

open Lax916827.RegularFunctions Lax916827.TwoWayTransducers

/-- A regular function is computed by a two-way transducer. -/
axiom isTwoWay_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsTwoWay f

end Lax916827.TwoWayOfRegular
