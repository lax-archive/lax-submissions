/-
Claim `claim:conditional` of *Transducers* (M. Bojańczyk): the disjoint sum of two regular
functions is regular.

*Discrepancy with the book.*  The claim, as printed, asks for a function `f₁ + f₂` on `(A₁ + A₂)*`
which agrees with `f₁` on the strings that use only letters of `A₁` and with `f₂` on the strings
that use only letters of `A₂`.  The empty string uses only letters of `A₁` *and* only letters of
`A₂`, so the two requirements conflict on it: no function whatsoever can satisfy both unless `f₁ ε`
and `f₂ ε` are both empty (`Transducers.not_sum_of_regular_nil` below is a counterexample with `f₁ ε
= a` and `f₂ = id`).  The claim is therefore formalised, and proved, for *nonempty* inputs; the
value on the empty string is left unspecified.  This is the only change, and it is harmless for the
way the claim is used in the book (in the proof of Lemma `lem:regular-closure-properties` the two
blocks that the sum is applied to are always nonempty). -/
import Lax916827Proofs.Source.PartC.SumReg
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- The empty string is a witness that the claim of `claim:conditional` cannot hold on *all*
inputs: it uses only letters of `A₁` and only letters of `A₂` at the same time.
Here `f₁` is the constant function with value `a` and `f₂` is the identity. -/
theorem not_sum_of_regular_nil :
    ¬ ∃ F : List (Unit ⊕ Unit) → List (Unit ⊕ Unit),
        (∀ u : List Unit, F (u.map Sum.inl) = ((fun _ => [()]) u).map Sum.inl) ∧
        (∀ u : List Unit, F (u.map Sum.inr) = (id u).map Sum.inr) := by
  rintro ⟨F, h₁, h₂⟩
  have e₁ := h₁ []
  have e₂ := h₂ []
  simp at e₁ e₂
  rw [e₂] at e₁
  exact absurd e₁ (by simp)

/-- **Claim `claim:conditional`** (corrected on the empty input; see the note at the top of
the file).  For regular functions `f₁ : A₁* → B₁*` and `f₂ : A₂* → B₂*` there is
a regular function `F : (A₁ + A₂)* → (B₁ + B₂)*` which applies `f₁` to the
nonempty strings that use only letters of `A₁`, applies `f₂` to the nonempty
strings that use only letters of `A₂`, and returns a fixed string `bot` using
both output alphabets on all other strings. -/
theorem sum_of_regular_aux {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂] {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) :=
  msum_to_sum hf₁ hf₂

end Lax916827Proofs.Transducers
