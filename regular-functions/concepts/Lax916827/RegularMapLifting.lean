import Lax765601.MapLifting
import Lax916827.RegularFunctions

/-!
---
title: Regular functions are closed under map lifting
type: theorem
---
The map lifting of a regular function is regular (Lemma C.2.10 of
*Transducers*, first item). Map lifting commutes with composition, so it
suffices to lift the primes: the map lifting of a rational function is rational,
and the map liftings of map reverse and map duplicate are regular.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.RegularMapLifting

open Lax765601.MapLifting Lax916827.RegularFunctions

/-- The map lifting of a regular function is regular. -/
axiom isRegularFun_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsRegularFun (mapLift f)

end Lax916827.RegularMapLifting
