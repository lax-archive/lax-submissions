import Lax916827.RegularFunctions

/-!
---
title: Regular functions are closed under concatenation
type: theorem
---
If $f, g : A^* \to B^*$ are regular, then so is their concatenation
$w \mapsto f(w) \cdot g(w)$ (Lemma C.2.10 of *Transducers*, second item): map
duplicate produces two copies of the input, and the map liftings of $f$ and of
$g$ are applied to the two copies, selected by a rational marking.

# Formalization notes

Both alphabets are assumed finite, as in the book.
-/

namespace Lax916827.RegularConcatenation

open Lax916827.RegularFunctions

/-- The concatenation of two regular functions is regular. -/
axiom isRegularFun_concat {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (fun w => f w ++ g w)

end Lax916827.RegularConcatenation
