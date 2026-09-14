/-
The explicit equivalence bound for two-way transducers over finite alphabets,
for Theorem `thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk).

Two two-way transducers computing total functions over finite alphabets compute
the same function as soon as they agree on the inputs of length at most an
explicit arithmetic expression in the number of their states and the size of the
input alphabet (`Transducers.RegHankel.twoWay_eq_of_short`).  This is
Schützenberger's criterion, in the form
`Transducers.HankelRank.zero_of_short`, applied to the difference of the values
of the two transducers, which has a Hankel decomposition over the sum of the two
index sets of `RequestProject/PartC/RegHankel.lean`.

Unlike the bound of `RequestProject/PartC/RegCodeBound.lean`, which comes from
three existential statements over abstract finite types and so carries no size
information, this one is a *formula*, and that is what makes the decision
procedure of Theorem `thm:decidable-equivalence-regular` effective.
-/
import Lax916827Proofs.Source.PartC.RegHankel
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegHankel

open RegPos TwoWay

noncomputable section

open Classical

/-! ## The size of the index set -/

/-- An explicit upper bound for the size of the index set of the Hankel
decomposition, in terms of an upper bound `a` for the number of input letters
and an upper bound `q` for the number of states. -/
def idxBound (a q : ℕ) : ℕ := (a + 1) * ((q + 1) ^ (2 * q + 2) * ((2 * q + 1) * (2 * q + 2)))

lemma card_Idx (A Q : Type) [Fintype A] [Fintype Q] :
    Fintype.card (Idx A Q)
      = (Fintype.card A + 1) * (Fintype.card Q ^ (2 * Fintype.card Q) *
          ((2 * Fintype.card Q + 1) * (2 * Fintype.card Q + 2))) := by
  simp [Fintype.card_prod, Fintype.card_option, csN]

lemma card_Idx_le {A Q : Type} [Fintype A] [Fintype Q] {a q : ℕ}
    (ha : Fintype.card A ≤ a) (hq : Fintype.card Q ≤ q) :
    Fintype.card (Idx A Q) ≤ idxBound a q := by
  rw [card_Idx, idxBound]
  refine Nat.mul_le_mul (by omega) (Nat.mul_le_mul ?_ (Nat.mul_le_mul (by omega) (by omega)))
  calc Fintype.card Q ^ (2 * Fintype.card Q)
      ≤ (q + 1) ^ (2 * Fintype.card Q) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (q + 1) ^ (2 * q + 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## The bound -/

/-- **The explicit equivalence bound for two-way transducers.**  Two two-way
transducers over finite alphabets that compute total functions compute the same
function as soon as they agree on the inputs of length at most
`idxBound a q₁ + idxBound a q₂`, where `a` bounds the number of input letters
and `q₁`, `q₂` bound the numbers of states. -/
theorem twoWay_eq_of_short {A B Q₁ Q₂ : Type} [Fintype A] [Fintype B] [Fintype Q₁] [Fintype Q₂]
    (M₁ : TwoWay A B Q₁) (M₂ : TwoWay A B Q₂) {f₁ f₂ : List A → List B}
    (hf₁ : ∀ w, M₁.Computes w (f₁ w)) (hf₂ : ∀ w, M₂.Computes w (f₂ w))
    {a q₁ q₂ n : ℕ} (ha : Fintype.card A ≤ a) (h1 : Fintype.card Q₁ ≤ q₁)
    (h2 : Fintype.card Q₂ ≤ q₂) (hn : idxBound a q₁ + idxBound a q₂ ≤ n)
    (hshort : ∀ w : List A, w.length ≤ n → f₁ w = f₂ w) : ∀ w, f₁ w = f₂ w := by
  classical
  set F : List A → ℚ := fun w => oval (f₁ w) - oval (f₂ w) with hF
  set G : Idx A Q₁ ⊕ Idx A Q₂ → List A → ℚ :=
    Sum.elim (fun ι u => gfun M₁ ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u)
      (fun ι u => -gfun M₂ ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u) with hG
  set H : Idx A Q₁ ⊕ Idx A Q₂ → List A → ℚ :=
    Sum.elim (fun ι v => hfun M₁ ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v)
      (fun ι v => hfun M₂ ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v) with hH
  have hdec : ∀ u v : List A, F (u ++ v) = ∑ i, G i u * H i v := by
    intro u v
    rw [Fintype.sum_sum_type]
    simp only [hG, hH, Sum.elim_inl, Sum.elim_inr, neg_mul]
    rw [Finset.sum_neg_distrib]
    rw [← hankel_decomp M₁ f₁ hf₁ u v, ← hankel_decomp M₂ f₂ hf₂ u v]
    simp only [hF]
    ring
  have hcard : Fintype.card (Idx A Q₁ ⊕ Idx A Q₂) ≤ n := by
    rw [Fintype.card_sum]
    exact le_trans (Nat.add_le_add (card_Idx_le ha h1) (card_Idx_le ha h2)) hn
  have hzero : ∀ w : List A, w.length ≤ Fintype.card (Idx A Q₁ ⊕ Idx A Q₂) → F w = 0 := by
    intro w hw
    simp only [hF]
    rw [hshort w (le_trans hw hcard)]
    ring
  have := HankelRank.zero_of_short hdec hzero
  intro w
  have hw := this w
  simp only [hF, sub_eq_zero] at hw
  exact oval_injective hw

end

end RegHankel

end Lax916827Proofs.Transducers
