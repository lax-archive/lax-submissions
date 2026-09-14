import Mathlib.Computability.DFA
import Lax916827.RegularFunctions

/-!
---
title: Regular functions are closed under conditionals over regular languages
type: theorem
---
If $f, g : A^* \to B^*$ are regular and $L \subseteq A^*$ is regular, then the
conditional function
$$w \mapsto \begin{cases} f(w) & \text{if } w \in L \\ g(w) & \text{otherwise} \end{cases}$$
is regular (Lemma C.2.10 of *Transducers*, third item): a rational function
marks the input with its membership in $L$, and the marked sum of Claim C.2.11
applies $f$ or $g$ according to the mark.

# Formalization notes

The conditional needs a decision of `w ∈ L`; the statement uses classical
decidability, since no computational content is claimed for the function. Both
alphabets are assumed finite, as in the book.
-/

namespace Lax916827.RegularConditional

open Lax916827.RegularFunctions

open scoped Classical in
/-- The conditional of two regular functions over a regular language is regular. -/
axiom isRegularFun_ite {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) (L : Language A) (hL : L.IsRegular) :
    IsRegularFun (fun w => if w ∈ L then f w else g w)

end Lax916827.RegularConditional
