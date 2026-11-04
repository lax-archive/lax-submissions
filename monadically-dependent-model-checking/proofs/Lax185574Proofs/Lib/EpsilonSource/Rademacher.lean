/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/Complexity/Rademacher.lean.
Changes: extract the epsilon-net dependency closure, add a submission-local
namespace, and port to Lean 4.33.0. See PROVENANCE.md for details.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Computability.Encoding
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProductMeasure
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Lax185574Proofs.Lib.EpsilonSource.Basic
import Lax185574Proofs.Lib.EpsilonSource.Generalization

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000

/-- Convert Bool labels to ±1 reals. true ↦ 1, false ↦ -1. -/
noncomputable def boolToSign (b : Bool) : ℝ := if b then 1 else -1

abbrev SignVector (m : ℕ) := Fin m → Bool

/-- cosh(x) ≤ exp(x²/2). Standard sub-Gaussian bound. -/
theorem cosh_le_exp_sq_half (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) :=
  Real.cosh_le_exp_half_sq x

/-- Rademacher MGF bound. -/
theorem rademacher_mgf_bound {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (ha : ∀ i, |a i| ≤ c) (t : ℝ) (_ht : 0 ≤ t) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
    Real.exp (t ^ 2 * c ^ 2 / (2 * m)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have h_step1 : ∀ σ : SignVector m,
      Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) =
      ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / m) := by
    intro σ
    have h_sum : t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i)) =
        ∑ i : Fin m, (t * a i * boolToSign (σ i) / m) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1; ext i; ring
    rw [h_sum, Real.exp_sum]
  simp_rw [h_step1]
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / ↑m) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m => Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) => Real.exp (t * a i * boolToSign b / ↑m))]
  have hcard_eq : (Fintype.card (SignVector m) : ℝ) = (2 : ℝ) ^ m := by
    have : Fintype.card (SignVector m) = 2 ^ m := by
      show Fintype.card (Fin m → Bool) = 2 ^ m
      simp [Fintype.card_fin, Fintype.card_bool]
    push_cast [this]; rfl
  have h_inv : (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = (1/2 : ℝ) ^ m := by
    rw [hcard_eq, one_div, one_div, inv_pow]
  rw [h_inv]
  have h_prod_const : ((1/2 : ℝ) ^ m : ℝ) = ∏ _i : Fin m, (1/2 : ℝ) := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_const, ← Finset.prod_mul_distrib]
  have h_factor_bound : ∀ i : Fin m,
      (1/2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) ≤
      Real.exp ((t * a i / ↑m) ^ 2 / 2) := by
    intro i
    set u := t * a i / (↑m : ℝ) with hu_def
    have h_sum_eq : ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) =
        Real.exp u + Real.exp (-u) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1
      · congr 1; rw [hu_def]; ring
      · congr 1; rw [hu_def]; ring
    rw [h_sum_eq]
    have h_eq_cosh : (1/2 : ℝ) * (Real.exp u + Real.exp (-u)) = Real.cosh u := by
      rw [Real.cosh_eq]; ring
    rw [h_eq_cosh]
    exact cosh_le_exp_sq_half _
  have h_factor_nonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1/2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) := by
    intro i _
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
    apply Finset.sum_nonneg; intro b _; exact (Real.exp_pos _).le
  calc ∏ i : Fin m, (1/2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m)
      ≤ ∏ i : Fin m, Real.exp ((t * a i / ↑m) ^ 2 / 2) :=
        Finset.prod_le_prod h_factor_nonneg (fun i _ => h_factor_bound i)
    _ = Real.exp (∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2) :=
        (Real.exp_sum Finset.univ _).symm
    _ ≤ Real.exp (t ^ 2 * c ^ 2 / (2 * ↑m)) := by
        apply Real.exp_le_exp_of_le
        have h_sum_eq : ∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2 =
            t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h_sum_eq]
        have h_sum_sq_le : ∑ i : Fin m, a i ^ 2 ≤ ↑m * c ^ 2 := by
          calc ∑ i : Fin m, a i ^ 2
              ≤ ∑ _i : Fin m, c ^ 2 := by
                apply Finset.sum_le_sum; intro i _
                exact sq_le_sq' (abs_le.mp (ha i)).1 (abs_le.mp (ha i)).2
            _ = ↑m * c ^ 2 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2
            ≤ t ^ 2 / (2 * ↑m ^ 2) * (↑m * c ^ 2) := by
              apply mul_le_mul_of_nonneg_left h_sum_sq_le; positivity
          _ = t ^ 2 * c ^ 2 / (2 * ↑m) := by field_simp

/-- Pure combinatorial inequality: ∑_{i=0}^d C(m,i) ≤ (em/d)^d for d ≤ m, d ≥ 1. -/
theorem sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hdm_r : (d : ℝ) ≤ ↑m := Nat.cast_le.mpr hdm
  have hd_div_m_pos : (0 : ℝ) < ↑d / ↑m := div_pos hd_pos hm_pos
  have hd_div_m_le : (d : ℝ) / ↑m ≤ 1 := by
    rw [div_le_one hm_pos]; exact hdm_r
  have hm_div_d_ge : (1 : ℝ) ≤ ↑m / ↑d := le_div_iff₀ hd_pos |>.mpr (by linarith)
  set t := (d : ℝ) / ↑m with ht_def
  have ht_pos : 0 < t := hd_div_m_pos
  have ht_le : t ≤ 1 := hd_div_m_le
  have h_binom : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      t ^ i * (1 : ℝ) ^ (m - i) * ↑(Nat.choose m i) := by
    rw [add_comm]; exact add_pow t 1 m
  have h_binom' : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      ↑(Nat.choose m i) * t ^ i := by
    rw [h_binom]
    congr 1; ext i
    rw [one_pow, mul_one]; ring
  have h_partial_le_binom : ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i ≤
      (1 + t) ^ m := by
    rw [h_binom']
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
  have h_exp_bound : (1 + t) ^ m ≤ Real.exp 1 ^ d := by
    have h1t_le : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h_pow : (1 + t) ^ m ≤ (Real.exp t) ^ m :=
      pow_le_pow_left₀ (by linarith) h1t_le m
    have h_exp_eq : (Real.exp t) ^ m = Real.exp (t * ↑m) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h_tm : t * ↑m = ↑d := by
      simp only [ht_def]; field_simp
    rw [h_exp_eq, h_tm] at h_pow
    calc (1 + t) ^ m ≤ Real.exp ↑d := h_pow
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp
  have h_factor : (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) ≤
      (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
    have h_id : ∀ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) =
        ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i := by
      intro i _
      have htinv : t * (↑m / ↑d) = 1 := by
        simp only [ht_def]; field_simp
      rw [mul_assoc, ← mul_pow, htinv, one_pow, mul_one]
    rw [Finset.sum_congr rfl h_id]
    calc ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ d := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · exact pow_right_mono₀ hm_div_d_ge hi_le
          · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
      _ = (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
          rw [← Finset.sum_mul, mul_comm]
  calc (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ))
      ≤ (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := h_factor
    _ ≤ (↑m / ↑d) ^ d * ((1 + t) ^ m) := by
        apply mul_le_mul_of_nonneg_left h_partial_le_binom
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ ≤ (↑m / ↑d) ^ d * Real.exp 1 ^ d := by
        apply mul_le_mul_of_nonneg_left h_exp_bound
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ = (Real.exp 1 * ↑m / ↑d) ^ d := by
        rw [mul_div_assoc, ← mul_pow, mul_comm (Real.exp 1) _]

end
end Lax185574Proofs.Lib.EpsilonSource
