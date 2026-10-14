import Mathlib.Tactic

/-!
Exact rational averages on finite spaces, including the uniform product law for
finite independent choices with coordinate-dependent finite fibres.
-/

namespace Lax457868Proofs.SamplerFiniteMean

open Finset

/-- The uniform rational mean of a function on a finite type. -/
def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℚ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteMean f := by
  unfold finiteMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun ω _ => hf ω
  · exact_mod_cast (Nat.zero_le (Fintype.card Ω))

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ)
    (hfg : ∀ ω, f ω ≤ g ω) : finiteMean f ≤ finiteMean g := by
  unfold finiteMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun ω _ => hfg ω
  · exact_mod_cast (Nat.zero_le (Fintype.card Ω))

private lemma sum_eval_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (Ω : I → Type*) [∀ i, Fintype (Ω i)] (i : I) (f : Ω i → ℚ) :
    (∑ x : (∀ j, Ω j), f (x i)) =
      (Fintype.card (∀ j : {j // j ≠ i}, Ω j) : ℚ) * ∑ a : Ω i, f a := by
  classical
  let e := Equiv.piSplitAt i Ω
  calc
    (∑ x : (∀ j, Ω j), f (x i)) =
        ∑ p : Ω i × (∀ j : {j // j ≠ i}, Ω j), f p.1 := by
          exact Fintype.sum_equiv e (fun x => f (x i)) (fun p => f p.1) (by intro x; rfl)
    _ = ∑ a : Ω i, ∑ r : (∀ j : {j // j ≠ i}, Ω j), f a := by
          rw [Fintype.sum_prod_type]
    _ = (Fintype.card (∀ j : {j // j ≠ i}, Ω j) : ℚ) * ∑ a : Ω i, f a := by
          calc
            (∑ a : Ω i, ∑ r : (∀ j : {j // j ≠ i}, Ω j), f a) =
                ∑ a : Ω i, (Fintype.card (∀ j : {j // j ≠ i}, Ω j) : ℚ) * f a := by
                  apply Finset.sum_congr rfl
                  intro a _
                  simp [Finset.sum_const, nsmul_eq_mul]
            _ = (Fintype.card (∀ j : {j // j ≠ i}, Ω j) : ℚ) * ∑ a : Ω i, f a := by
                  rw [Finset.mul_sum]

private lemma card_pi_split {I : Type*} [Fintype I] [DecidableEq I]
    (Ω : I → Type*) [∀ i, Fintype (Ω i)] (i : I) :
    Fintype.card (∀ j, Ω j) =
      Fintype.card (Ω i) * Fintype.card (∀ j : {j // j ≠ i}, Ω j) := by
  rw [Fintype.card_congr (Equiv.piSplitAt i Ω), Fintype.card_prod]

/-- The average of a coordinate-only function over all product choices is its
uniform mean on that coordinate. This is the finite uniform marginal law. -/
private lemma finiteMean_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (Ω : I → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (i : I) (f : Ω i → ℚ) :
    finiteMean (fun x : (∀ j, Ω j) => f (x i)) = finiteMean f := by
  classical
  have hi : 0 < Fintype.card (Ω i) := Fintype.card_pos_iff.mpr ⟨Classical.choice inferInstance⟩
  have hr : 0 < Fintype.card (∀ j : {j // j ≠ i}, Ω j) := by
    exact Fintype.card_pos_iff.mpr ⟨fun j => Classical.choice (inferInstance : Nonempty (Ω j.1))⟩
  have hcard := card_pi_split Ω i
  have hcardQ : (Fintype.card (∀ j, Ω j) : ℚ) =
      (Fintype.card (Ω i) : ℚ) * Fintype.card (∀ j : {j // j ≠ i}, Ω j) := by
    exact_mod_cast hcard
  unfold finiteMean
  rw [sum_eval_coordinate, hcardQ]
  field_simp

/-- Uniform averaging over a dependent finite product factors as the sum of
the coordinate means. The proof derives each uniform marginal by splitting
the product at that coordinate. -/
lemma finiteMean_sum_pi {I : Type*} [Fintype I] [DecidableEq I]
    (Ω : I → Type*) [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (f : ∀ i, Ω i → ℚ) :
    finiteMean (fun choice : (∀ i, Ω i) => ∑ i, f i (choice i)) =
      ∑ i, finiteMean (f i) := by
  classical
  calc
    finiteMean (fun choice : (∀ i, Ω i) => ∑ i, f i (choice i)) =
        ∑ i, finiteMean (fun choice : (∀ j, Ω j) => f i (choice i)) := by
          unfold finiteMean
          calc
            (∑ choice : (∀ i, Ω i), ∑ i, f i (choice i)) /
                Fintype.card (∀ i, Ω i) =
              (∑ i, ∑ choice : (∀ j, Ω j), f i (choice i)) /
                Fintype.card (∀ i, Ω i) := by rw [Finset.sum_comm]
            _ = ∑ i, ((∑ choice : (∀ j, Ω j), f i (choice i)) /
                Fintype.card (∀ j, Ω j)) := by rw [Finset.sum_div]
            _ = ∑ i, finiteMean (fun choice : (∀ j, Ω j) => f i (choice i)) := by
                simp only [finiteMean]
    _ = ∑ i, finiteMean (f i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact finiteMean_coordinate Ω i (f i)

end Lax457868Proofs.SamplerFiniteMean
