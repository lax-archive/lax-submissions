import Lax916827.RegularFunctions

/-!
---
title: The sum of two regular functions on disjoint alphabets
type: theorem
---
For regular functions $f_1 : A_1^* \to B_1^*$ and $f_2 : A_2^* \to B_2^*$
with disjoint input and output alphabets, the function $f_1 + f_2$ on
$(A_1 + A_2)^*$ is regular (Claim C.2.11 of *Transducers*): it applies $f_1$
to the inputs using only letters of $A_1$, $f_2$ to those using only letters of
$A_2$, and returns a fixed string $\bot$ using both output alphabets otherwise.
The claim is what the closure properties of Lemma C.2.10 rest on.

# Formalization notes

The claim as printed is false on the empty input: the empty string uses only
letters of $A_1$ and, at the same time, only letters of $A_2$, so the first two
requirements conflict unless $f_1(\varepsilon)$ and $f_2(\varepsilon)$ are both
empty. The statement therefore imposes the two requirements on *nonempty*
inputs only and leaves the value on the empty input unspecified, which is
harmless for the use the book makes of the claim, where the blocks are always
nonempty. The disjoint union of alphabets is `A₁ ⊕ A₂`, and the output
alphabets are assumed nonempty so that $\bot$ exists.
-/

namespace Lax916827.RegularSum

open Lax916827.RegularFunctions

/-- The sum `f₁ + f₂` of two regular functions on disjoint alphabets is regular,
with a bottom value on mixed inputs (and the two clauses required on nonempty
inputs). -/
axiom exists_isRegularFun_sum {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂] {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot)

end Lax916827.RegularSum
