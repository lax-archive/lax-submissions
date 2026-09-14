import Lax916827.RegularFunctions

/-!
---
title: Regular functions are closed under composition
type: theorem
---
Regular functions are closed under composition (Theorem C.1.1 of
*Transducers*, the composition half): composition is built into the definition
of the regular functions as compositions of primes.

# Formalization notes

The intermediate alphabet is assumed finite, as in the composition closure.
-/

namespace Lax916827.RegularComposition

open Lax916827.RegularFunctions

/-- The composition of two regular functions is regular. -/
axiom isRegularFun_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f)

end Lax916827.RegularComposition
