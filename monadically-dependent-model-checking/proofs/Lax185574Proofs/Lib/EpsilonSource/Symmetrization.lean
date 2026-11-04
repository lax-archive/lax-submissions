/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/Complexity/Symmetrization.lean.
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
import Lax185574Proofs.Lib.EpsilonSource.Rademacher

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000
open MeasureTheory ENNReal

/-- One-sided Hoeffding: for iid Bernoulli(p) draws, the empirical average
    undershoots the mean by ≥ t with probability ≤ exp(-2mt²).

    **References:** SSBD Lemma B.3, Hoeffding (1963) -/
theorem hoeffding_one_sided {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≤ TrueErrorReal X h c D - t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set p := TrueErrorReal X h c D with hp_def
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  set Z : Fin m → (Fin m → X) → ℝ := fun i xs => p - indicator (xs i) with hZ_def
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set S := {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) ≤ p - t} with hS_def
  have h_set_sub : S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
    intro xs hxs
    simp only [Set.mem_setOf_eq] at hxs ⊢
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [hS_def, Set.mem_setOf_eq, EmpiricalError,
      Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hxs
    have h_div : (∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))) / (m : ℝ) ≤ p - t := hxs
    rw [div_le_iff₀ hm_pos] at h_div
    linarith
  calc μ S
      ≤ μ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
        exact MeasureTheory.measure_mono h_set_sub
    _ = ENNReal.ofReal (μ.real {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : MeasureTheory.IsProbabilityMeasure μ := by
          rw [hμ_def]; infer_instance
        set g : X → ℝ := fun x => p - indicator x with hg_def
        have hZ_eq : ∀ i : Fin m, ∀ xs : Fin m → X, Z i xs = g (xs i) := by
          intros i xs; simp [hZ_def, hg_def]
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x
          simp only [hind_def, zeroOneLoss]
          split
          · exact ⟨le_refl 0, zero_le_one⟩
          · exact ⟨zero_le_one, le_refl 1⟩
        have h_g_bound : ∀ x : X, g x ∈ Set.Icc (p - 1) p := by
          intro x
          have hix := h_ind_bound x
          simp only [hg_def, Set.mem_Icc] at hix ⊢
          constructor <;> linarith [hix.1, hix.2]
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          have hmeas_eq : MeasurableSet {a : X | h a = c a} := by
            have : {a : X | h a = c a} = {a : X | h a ≠ c a}ᶜ := by
              ext x; simp
            rw [this]; exact hmeas.compl
          exact Measurable.ite hmeas_eq measurable_const measurable_const
        have h_g_meas : Measurable g := by
          exact measurable_const.sub h_ind_meas
        have h_g_ae_bound : ∀ᵐ x ∂D, g x ∈ Set.Icc (p - 1) p := by
          exact Filter.Eventually.of_forall h_g_bound
        have h_int_ind : ∫ x, indicator x ∂D = p := by
          simp only [hind_def, zeroOneLoss, hp_def, TrueErrorReal, TrueError]
          have h_ite_eq : (fun x => if h x = c x then (0 : ℝ) else 1) =
              Set.indicator {x | h x ≠ c x} 1 := by
            ext x
            simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
            by_cases hx : h x = c x
            · simp [hx]
            · simp [hx]
          rw [h_ite_eq, integral_indicator_one hmeas]
          simp only [Measure.real]
        have h_int_g : ∫ x, g x ∂D = 0 := by
          simp only [hg_def]
          rw [integral_sub (integrable_const p)
            (Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound))]
          simp [h_int_ind]
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g ((‖p - (p - 1)‖₊ / 2) ^ 2) D := by
          exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable h_g_ae_bound h_int_g
        have h_param_eq : ‖p - (p - 1)‖₊ = (1 : NNReal) := by
          have hsub : p - (p - 1) = (1 : ℝ) := by ring
          rw [hsub]
          simp [nnnorm_one]
        have h_param_simp : (‖p - (p - 1)‖₊ / 2) ^ 2 = ((1 : NNReal) / 2) ^ 2 := by
          rw [h_param_eq]
        rw [h_param_simp] at h_g_subG
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (xs : Fin m → X) => g (xs i)) μ := by
          rw [hμ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun xs : Fin m → X => g (xs i)) ((1 / 2 : NNReal) ^ 2) μ := by
          intro i
          have h_of_map : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (xs : Fin m → X) => xs i) ((1 / 2 : NNReal) ^ 2) μ := by
            apply ProbabilityTheory.HasSubgaussianMGF.of_map
              (measurable_pi_apply i).aemeasurable
            rw [hμ_def]
            rw [MeasureTheory.measurePreserving_eval _ i |>.map_eq]
            exact h_g_subG
          exact h_of_map
        have h_eps_pos : (0 : ℝ) ≤ ↑m * t := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep
          (c := fun _ => (1 / 2 : NNReal) ^ 2)
          (s := Finset.univ)
          (fun i _ => h_subG_each i)
          h_eps_pos
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 / 2 : NNReal) ^ 2 : NNReal)) =
            ↑m * (1 / 2 : NNReal) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [h_sum_c] at h_hoeff
        suffices h_exp_eq : Real.exp (-(↑m * t) ^ 2 / (2 * ↑(↑m * (1 / 2 : NNReal) ^ 2 : NNReal))) =
            Real.exp (-2 * ↑m * t ^ 2) by
          rw [h_exp_eq] at h_hoeff
          exact h_hoeff
        congr 1
        push_cast
        field_simp

/-! ## T2: Symmetrization Step -/

/-- Symmetrization: the probability of a large gap TrueErr-EmpErr
    is at most twice the probability of a large gap EmpErr'-EmpErr
    on the double sample.

    **References:** SSBD Lemma 4.5, Kakade-Tewari Lecture 19 Lemma 1 -/
theorem symmetrization_step {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set A := {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
    with hA_def
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hB_def
  suffices h_half : (1 : ℝ≥0∞) / 2 * μ A ≤ (μ.prod μ) B by
    have h2 : μ A ≤ 2 * ((1 : ℝ≥0∞) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact h2.trans (mul_le_mul_right h_half 2)
  set B' := MeasureTheory.toMeasurable (μ.prod μ) B with hB'_def
  have hB'_meas : MeasurableSet B' := MeasureTheory.measurableSet_toMeasurable _ _
  set f : (Fin m → X) → ℝ≥0∞ := fun xs => μ (Prod.mk xs ⁻¹' B') with hf_def
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  have h_cond : ∀ xs ∈ A, (1 : ℝ≥0∞) / 2 ≤ f xs := by
    intro xs hxs
    obtain ⟨h_star, h_star_in_C, h_gap⟩ := hxs
    set S_ghost := {xs' : Fin m → X | EmpiricalError X Bool h_star
        (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_star
        (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε / 2} with hS_ghost_def
    have h_ghost_sub_B : S_ghost ⊆ Prod.mk xs ⁻¹' B := by
      intro xs' hxs'
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def]
      exact ⟨h_star, h_star_in_C, hxs'⟩
    have h_B_sub_B' : Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B' :=
      Set.preimage_mono (MeasureTheory.subset_toMeasurable _ _)
    calc (1 : ℝ≥0∞) / 2
        ≤ μ S_ghost := by
          have hmeas_disagree : MeasurableSet {x | h_star x ≠ c x} :=
            (measurableSet_eq_fun (hmeas_C h_star h_star_in_C) hc_meas).compl
          have h_true_le_one : TrueErrorReal X h_star c D ≤ 1 := by
            simp only [TrueErrorReal, TrueError]
            have h_le : D {x | h_star x ≠ c x} ≤ 1 := by
              calc D {x | h_star x ≠ c x} ≤ D Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_le_of_le_ofReal one_pos.le
              (by rw [ENNReal.ofReal_one]; exact h_le)
          have h_emp_nonneg : 0 ≤ EmpiricalError X Bool h_star
              (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
            simp only [EmpiricalError]
            split
            · exact le_refl 0
            · apply div_nonneg
              · apply Finset.sum_nonneg
                intro i _
                simp only [zeroOneLoss]
                split <;> linarith
              · positivity
          by_cases hε1 : ε ≤ 1
          case neg =>
            push_neg at hε1
            have h_gap_bound : TrueErrorReal X h_star c D -
                EmpiricalError X Bool h_star
                (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≤ 1 := by
              linarith
            linarith
          case pos =>
          have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
          have hε2_le_one : ε / 2 ≤ 1 := by linarith
          have h_hoeff := hoeffding_one_sided D h_star c m hm (ε / 2) hε2_pos hε2_le_one
            hmeas_disagree
          have h_exp_le_half : Real.exp (-2 * ↑m * (ε / 2) ^ 2) ≤ 1 / 2 := by
            have h_exp_eq : -2 * ↑m * (ε / 2) ^ 2 = -(↑m * ε ^ 2 / 2) := by ring
            rw [h_exp_eq]
            have h_half : Real.log 2 ≤ ↑m * ε ^ 2 / 2 := by linarith
            have h_two_le_exp : (2 : ℝ) ≤ Real.exp (↑m * ε ^ 2 / 2) := by
              calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
                _ ≤ Real.exp (↑m * ε ^ 2 / 2) := Real.exp_le_exp_of_le h_half
            rw [Real.exp_neg]
            rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
            exact inv_anti₀ (by positivity) h_two_le_exp
          set H_set := {xs' : Fin m → X | EmpiricalError X Bool h_star
              (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≤
              TrueErrorReal X h_star c D - ε / 2} with hH_set_def
          have h_H_le_half : μ H_set ≤ 1 / 2 := by
            calc μ H_set
                ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * (ε / 2) ^ 2)) := h_hoeff
              _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h_exp_le_half
              _ = 1 / 2 := by
                  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
                  simp [ENNReal.ofReal_one]
          have h_prob : MeasureTheory.IsProbabilityMeasure μ := by
            rw [hμ_def]; infer_instance
          have h_compl_ge : 1 / 2 ≤ μ H_setᶜ := by
            have h_total : 1 ≤ μ H_set + μ H_setᶜ := by
              have : μ Set.univ ≤ μ H_set + μ H_setᶜ := by
                calc μ Set.univ = μ (H_set ∪ H_setᶜ) := by rw [Set.union_compl_self]
                  _ ≤ μ H_set + μ H_setᶜ := measure_union_le _ _
              rwa [measure_univ] at this
            have h_H_ne_top : μ H_set ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top
                (h_H_le_half.trans (by norm_num))
            calc (1 : ℝ≥0∞) / 2
                = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - μ H_set := tsub_le_tsub_left h_H_le_half 1
              _ ≤ (μ H_set + μ H_setᶜ) - μ H_set := tsub_le_tsub_right h_total (μ H_set)
              _ = μ H_setᶜ := ENNReal.add_sub_cancel_left h_H_ne_top
          have h_compl_sub : H_setᶜ ⊆ S_ghost := by
            intro xs' hxs'
            simp only [Set.mem_compl_iff, hH_set_def, Set.mem_setOf_eq, not_le] at hxs'
            simp only [hS_ghost_def, Set.mem_setOf_eq, ge_iff_le]
            linarith
          exact h_compl_ge.trans (MeasureTheory.measure_mono h_compl_sub)
      _ ≤ μ (Prod.mk xs ⁻¹' B') :=
          MeasureTheory.measure_mono (h_ghost_sub_B.trans h_B_sub_B')
  have h_markov : (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ :=
    mul_meas_ge_le_lintegral hf_meas _
  have h_prod : (μ.prod μ) B' = ∫⁻ xs, μ (Prod.mk xs ⁻¹' B') ∂μ :=
    MeasureTheory.Measure.prod_apply hB'_meas
  calc (1 : ℝ≥0∞) / 2 * μ A
      ≤ (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} := by
        apply mul_le_mul_right
        exact MeasureTheory.measure_mono h_cond
    _ ≤ ∫⁻ xs, f xs ∂μ := h_markov
    _ = (μ.prod μ) B' := h_prod.symm
    _ = (μ.prod μ) B := MeasureTheory.measure_toMeasurable B

/-- The number of distinct restriction patterns of C on any n points is at most GF(C,n).
    For z : Fin n → X, define patterns(z) = {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = (h(z i) ≠ c(z i))}.
    Then patterns(z).ncard ≤ GrowthFunction X C n by definition of GrowthFunction. -/
theorem restriction_pattern_count {X : Type u} [MeasurableSpace X] [Infinite X]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (n : ℕ) (z : Fin n → X) :
    Set.ncard {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} ≤
      GrowthFunction X C n := by
  classical
  let R : Set (Fin n → Bool) := {f | ∃ h ∈ C, ∀ i, f i = h (z i)}
  let ψ : (Fin n → Bool) → (Fin n → Bool) := fun f i => Bool.xor (f i) (c (z i))
  have hψ_inj : Function.Injective ψ := by
    intro f g hfg; funext i
    have hi := congr_fun hfg i; simp only [ψ] at hi
    revert hi; cases f i <;> cases g i <;> cases c (z i) <;> simp [Bool.xor]
  have hP_eq : {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} = ψ '' R := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_image, R, ψ]
    constructor
    · rintro ⟨h, hC, hp⟩
      refine ⟨fun i => h (z i), ⟨h, hC, fun i => rfl⟩, ?_⟩
      funext i; simp only [hp i]
      cases h (z i) <;> cases c (z i) <;> rfl
    · rintro ⟨f, ⟨h, hC, hf⟩, rfl⟩
      exact ⟨h, hC, fun i => by simp only [hf i]; cases h (z i) <;> cases c (z i) <;> rfl⟩
  rw [hP_eq, Set.ncard_image_of_injective R hψ_inj]
  let S₀ : Finset X := Finset.univ.image z
  have hS₀_card : S₀.card ≤ n :=
    (Finset.card_image_le).trans (by simp [Fintype.card_fin])
  obtain ⟨S, hS₀_sub, hS_card⟩ := Infinite.exists_superset_card_eq S₀ n hS₀_card
  have hz_mem : ∀ i : Fin n, z i ∈ S :=
    fun i => hS₀_sub (Finset.mem_image_of_mem z (Finset.mem_univ i))
  let R_S : Set (↥S → Bool) := {g | ∃ h ∈ C, ∀ x : ↥S, g x = h ↑x}
  let ρ : (↥S → Bool) → (Fin n → Bool) := fun g i => g ⟨z i, hz_mem i⟩
  have hR_sub : R ⊆ ρ '' R_S := by
    rintro f ⟨h, hC, hf⟩
    exact ⟨fun x => h ↑x, ⟨h, hC, fun x => rfl⟩, funext fun i => by simp only [ρ, hf i]⟩
  have hR_le_RS : R.ncard ≤ R_S.ncard :=
    (Set.ncard_le_ncard hR_sub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite R_S))
  have hR_S_eq : R_S.ncard =
      ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _).ncard := by
    congr 1; ext f; exact ⟨fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩,
                           fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩⟩
  have hbdd : BddAbove (Set.range fun (T : {T : Finset X // T.card = n}) =>
      ({f : ↥T.val → Bool | ∃ c_1 ∈ C, ∀ x : ↥T.val, c_1 ↑x = f x} : Set _).ncard) := by
    refine ⟨2 ^ n, ?_⟩
    rintro _ ⟨T, rfl⟩
    calc Set.ncard _ ≤ Set.ncard (Set.univ : Set (↥T.val → Bool)) :=
            Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card (↥T.val → Bool) := Set.ncard_univ _
      _ = Fintype.card (↥T.val → Bool) := Nat.card_eq_fintype_card
      _ = 2 ^ T.val.card := by simp [Fintype.card_pi, Fintype.card_bool]
      _ = 2 ^ n := by rw [T.2]
  exact hR_le_RS.trans (hR_S_eq ▸ le_csSup hbdd ⟨⟨S, hS_card⟩, rfl⟩)

/-- Generic finite exchangeability bound. Given a measure-preserving family of
    transformations on a probability space, a NullMeasurableSet S, and a pointwise
    bound on the sum of preimage indicators, conclude ν(S) ≤ B. -/
theorem finite_exchangeability_bound
    {Ω G : Type*} [MeasurableSpace Ω] [Fintype G] [Nonempty G]
    {ν : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ν]
    (T : G → Ω → Ω)
    (S : Set Ω)
    (hT : ∀ g, MeasureTheory.MeasurePreserving (T g) ν ν)
    (hS0 : MeasureTheory.NullMeasurableSet S ν)
    (B : ENNReal)
    (hpointwise :
      ∀ z, (∑ g : G,
        (((T g) ⁻¹' S).indicator (1 : Ω → ENNReal)) z)
          ≤ B * (Fintype.card G : ENNReal)) :
    ν S ≤ B := by
  classical
  let I : G → Ω → ENNReal := fun g => ((T g) ⁻¹' S).indicator 1
  have hI_ae : ∀ g ∈ (Finset.univ : Finset G), AEMeasurable (I g) ν := by
    intro g _
    have hpre0 : MeasureTheory.NullMeasurableSet ((T g) ⁻¹' S) ν :=
      hS0.preimage (hT g).quasiMeasurePreserving
    exact aemeasurable_one.indicator₀ hpre0
  have hmain :
      (Fintype.card G : ENNReal) * ν S ≤ B * (Fintype.card G : ENNReal) := by
    calc (Fintype.card G : ENNReal) * ν S
        = ∑ _g : G, ν S := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : G, ν ((T g) ⁻¹' S) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            exact ((hT g).measure_preimage hS0).symm
      _ = ∑ g : G, ∫⁻ z, I g z ∂ν := by
            refine Finset.sum_congr rfl ?_
            intro g _
            exact (MeasureTheory.lintegral_indicator_one₀
              (hS0.preimage (hT g).quasiMeasurePreserving)).symm
      _ = ∫⁻ z, ∑ g : G, I g z ∂ν := by
            exact (MeasureTheory.lintegral_finset_sum' Finset.univ hI_ae).symm
      _ ≤ ∫⁻ _z, B * (Fintype.card G : ENNReal) ∂ν := by
            exact MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hpointwise)
      _ = B * (Fintype.card G : ENNReal) := by
            simp [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hcard_ne_zero : (Fintype.card G : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card G : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (ENNReal.mul_le_mul_iff_left hcard_ne_zero hcard_ne_top).mp (by rwa [mul_comm] at hmain)

theorem exchangeability_chain_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (_hmeas_C : ∀ h ∈ C, Measurable h) (_hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (_hε2 : ε ≤ 2) (hC : C.Nonempty)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  intro μ
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hbound_def
  have hbound_nonneg : 0 ≤ bound := by
    apply mul_nonneg
    · exact Nat.cast_nonneg' (GrowthFunction X C (2 * m))
    · exact (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hE_def
  by_cases h_triv : 1 ≤ bound
  · -- Case 1: bound ≥ 1, so probability ≤ 1 ≤ bound
    have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := inferInstance
    calc (μ.prod μ) E
        ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
  · -- Case 2: bound < 1
    push_neg at h_triv
    obtain ⟨h₀, hh₀⟩ := hC
    classical
    set ν := MeasureTheory.Measure.pi (fun _ : Fin m => D.prod D) with hν_def
    set eqv := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
    have h_mp : MeasurePreserving (⇑eqv) ν (μ.prod μ) := by
      rw [hν_def]
      exact measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
    have h_meas_eq : (μ.prod μ) E = ν (eqv ⁻¹' E) := by
      rw [← h_mp.map_eq]; exact eqv.map_apply E
    rw [h_meas_eq]
    have hGF_pos : 0 < GrowthFunction X C (2 * m) := by
      obtain ⟨S, _, hS_card⟩ := Infinite.exists_superset_card_eq
        (∅ : Finset X) (2 * m) (by simp)
      have h1 : 1 ≤ Set.ncard
          ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _) := by
        apply Nat.one_le_iff_ne_zero.mpr
        have hmem : (fun (x : ↥S) => h₀ (↑x : X)) ∈
            ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _) :=
          ⟨h₀, hh₀, fun _ => rfl⟩
        exact Set.ncard_ne_zero_of_mem hmem (Set.toFinite _)
      have hbdd : BddAbove (Set.range fun (T : {T : Finset X // T.card = 2 * m}) =>
          ({f : ↥T.val → Bool | ∃ c_1 ∈ C, ∀ x : ↥T.val, c_1 ↑x = f x} : Set _).ncard) := by
        refine ⟨2 ^ (2 * m), ?_⟩
        rintro _ ⟨T, rfl⟩
        calc Set.ncard _ ≤ Set.ncard (Set.univ : Set (↥T.val → Bool)) :=
                Set.ncard_le_ncard (Set.subset_univ _)
          _ = Nat.card (↥T.val → Bool) := Set.ncard_univ _
          _ = Fintype.card (↥T.val → Bool) := Nat.card_eq_fintype_card
          _ = 2 ^ T.val.card := by simp [Fintype.card_pi, Fintype.card_bool]
          _ = 2 ^ (2 * m) := by rw [T.2]
      have h2 : Set.ncard ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _)
          ≤ GrowthFunction X C (2 * m) :=
        le_csSup hbdd ⟨⟨S, hS_card⟩, rfl⟩
      exact Nat.lt_of_lt_of_le Nat.one_pos (h1.trans h2)
    have h_DxD_sym : (D.prod D).map Prod.swap = D.prod D :=
      MeasureTheory.Measure.prod_swap (μ := D) (ν := D)
    let swap_fun (σ : SignVector m) : (Fin m → X × X) → (Fin m → X × X) :=
      fun z i => if σ i then (z i).swap else z i
    have h_swap_invol : ∀ σ, Function.Involutive (swap_fun σ) := by
      intro σ z; funext i; simp only [swap_fun]
      split <;> simp [Prod.swap_swap]
    have h_swap_meas : ∀ σ, Measurable (swap_fun σ) := by
      intro σ; apply measurable_pi_lambda; intro i
      by_cases hσi : σ i
      · simp only [swap_fun, hσi, ↓reduceIte]
        exact (measurable_pi_apply i |>.snd).prod (measurable_pi_apply i |>.fst)
      · simp only [swap_fun, hσi]
        exact measurable_pi_apply i
    let swap_eqv (σ : SignVector m) : MeasurableEquiv (Fin m → X × X) (Fin m → X × X) :=
      { toEquiv := (h_swap_invol σ).toPerm
        measurable_toFun := h_swap_meas σ
        measurable_invFun := by rw [(h_swap_invol σ).toPerm_symm]; exact h_swap_meas σ }
    have h_swap_pres : ∀ σ, ν.map (swap_fun σ) = ν := by
      intro σ; rw [hν_def]
      let f_σ : Fin m → (X × X) → (X × X) := fun i => if σ i then Prod.swap else id
      have h_eq_pointwise : swap_fun σ = fun z i => f_σ i (z i) := by
        funext z; funext i; simp only [swap_fun, f_σ]; split <;> simp
      rw [h_eq_pointwise]
      rw [MeasureTheory.Measure.pi_map_pi (fun i => by
        simp only [f_σ]; split
        · exact measurable_swap.aemeasurable
        · exact measurable_id.aemeasurable)]
      congr 1; funext i; simp only [f_σ]
      split
      · exact h_DxD_sym
      · exact MeasureTheory.Measure.map_id
    have h_swap_eq : ∀ σ A, ν (swap_fun σ ⁻¹' A) = ν A := by
      intro σ A
      have h1 : ν.map (⇑(swap_eqv σ)) A = ν ((swap_eqv σ) ⁻¹' A) :=
        (swap_eqv σ).map_apply A
      have h2 : (⇑(swap_eqv σ) : (Fin m → X × X) → (Fin m → X × X)) = swap_fun σ := rfl
      rw [h2] at h1
      rw [← h1, h_swap_pres]
    set S := eqv ⁻¹' E
    have hcard_pos : (0 : ℝ≥0∞) < (Fintype.card (SignVector m) : ℝ≥0∞) := by
      exact_mod_cast Fintype.card_pos (α := SignVector m)
    have h_sum_eq_mul : ∑ _σ : SignVector m, ν S =
        (Fintype.card (SignVector m) : ℝ≥0∞) * ν S := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_swap_sum : ∑ σ : SignVector m, ν (swap_fun σ ⁻¹' S) =
        ∑ _σ : SignVector m, ν S := by
      congr 1; ext σ; exact h_swap_eq σ S
    have h_per_z_bound : ∀ z : Fin m → X × X,
        ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ≥0∞)
        ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
            (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
      intro z

      let merged : Fin (2 * m) → X := fun j =>
        if h : j.val < m then (z ⟨j.val, by omega⟩).1
        else (z ⟨j.val - m, by omega⟩).2

      have h_pattern_count := restriction_pattern_count C c (2 * m) merged




      have h_markov_bound : ∀ (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
          ((Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) ≤
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        intro a ha
        have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        set t₀ := (m : ℝ) * ε / 2 with ht₀_def
        have ht₀_pos : 0 < t₀ := by positivity
        have ht₀_nn : 0 ≤ t₀ := ht₀_pos.le
        have h_mgf := rademacher_mgf_bound hm a 1 zero_le_one
          (fun i => ha i) t₀ ht₀_nn
        have h_filter_le : ∀ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
            Real.exp (t₀ * (ε / 2)) ≤
            Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
          intro σ hσ
          simp only [Finset.mem_filter] at hσ
          exact Real.exp_le_exp_of_le (by nlinarith [hσ.2])
        have h_sum_filter : (Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card *
            Real.exp (t₀ * (ε / 2)) ≤
            ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
              (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
              Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
          rw [← nsmul_eq_mul]
          exact Finset.card_nsmul_le_sum _ _ _ h_filter_le
        have h_filter_sub_all :
            ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
              (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
              Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
            ∑ σ : SignVector m,
              Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun σ _ _ => (Real.exp_pos _).le)
        have hSV_pos : (0 : ℝ) < Fintype.card (SignVector m) := Nat.cast_pos.mpr Fintype.card_pos
        set filt := Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2) with hfilt_def
        have h_all_sum_bound : ∑ σ : SignVector m,
            Real.exp (t₀ * ((1 / ↑m) * ∑ i, a i * boolToSign (σ i))) ≤
            (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) := by
          have hSV_ne : (Fintype.card (SignVector m) : ℝ) ≠ 0 := ne_of_gt hSV_pos
          have := mul_le_mul_of_nonneg_left h_mgf (le_of_lt hSV_pos)
          rwa [← mul_assoc, mul_one_div_cancel hSV_ne, one_mul] at this
        have h_chain : (filt.card : ℝ) * Real.exp (t₀ * (ε / 2)) ≤
            (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) :=
          (h_sum_filter.trans h_filter_sub_all).trans h_all_sum_bound
        have h_exp_pos : 0 < Real.exp (t₀ * (ε / 2)) := Real.exp_pos _
        have h_card_le : (filt.card : ℝ) ≤
            (Fintype.card (SignVector m) : ℝ) *
            Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
          le_div_iff₀ h_exp_pos |>.mpr h_chain
        calc (filt.card : ℝ) ≤ (Fintype.card (SignVector m) : ℝ) *
                Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
              h_card_le
          _ = (Fintype.card (SignVector m) : ℝ) *
                (Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2))) := by
              ring
          _ = (Fintype.card (SignVector m) : ℝ) *
                Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m) - t₀ * (ε / 2)) := by
              congr 1; rw [Real.exp_sub]
          _ = (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
              congr 1; rw [ht₀_def]; field_simp; ring_nf

      have h_bound_real : ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ) ≤
          (↑(GrowthFunction X C (2 * m)) : ℝ) *
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        let PatternSet := {p : Fin (2 * m) → Bool |
          ∃ h ∈ C, ∀ i, p i = decide (h (merged i) ≠ c (merged i))}
        have hPS_finite : PatternSet.Finite := Set.toFinite PatternSet
        let PS := hPS_finite.toFinset
        have hPS_card : PS.card ≤ GrowthFunction X C (2 * m) := by
          rw [show PS.card = PatternSet.ncard from
            (Set.ncard_eq_toFinset_card PatternSet hPS_finite).symm]
          exact h_pattern_count
        let patToCoeff (p : Fin (2 * m) → Bool) : Fin m → ℝ := fun i =>
          -((if p (⟨i.val + m, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0) -
            (if p (⟨i.val, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0))
        have h_ptc_bound : ∀ p : Fin (2 * m) → Bool, ∀ i : Fin m, |patToCoeff p i| ≤ 1 := by
          intro p i; simp only [patToCoeff, abs_neg]
          split <;> split <;> simp
        have h_gap_identity : ∀ (h : X → Bool) (σ : SignVector m),
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).2 i)) (c ((eqv (swap_fun σ z)).2 i))) -
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).1 i)) (c ((eqv (swap_fun σ z)).1 i))) =
            ∑ i : Fin m,
              patToCoeff (fun j => decide (h (merged j) ≠ c (merged j))) i *
              boolToSign (σ i) := by
          intro h σ
          rw [← Finset.sum_sub_distrib]
          congr 1; ext i
          simp only [eqv, swap_fun, patToCoeff, merged,
            MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
            MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
          have hi_lt : i.val < m := i.isLt
          have hi_plus_ge : ¬(i.val + m < m) := by omega
          have him : i.val + m - m = i.val := by omega
          simp only [hi_lt, ↓reduceDIte, hi_plus_ge, him]
          rcases Bool.eq_false_or_eq_true (σ i) with hσi | hσi <;> simp only [hσi]
          · -- σ i = false: not swapped, .2 = (z i).2, .1 = (z i).1
            simp only [boolToSign, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
          · -- σ i = true: swapped, .2 = (z i).1, .1 = (z i).2
            simp only [boolToSign, Prod.swap, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
        have h_filter_biUnion :
            Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S) ⊆
            PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
              (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)) := by
          intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
          have hσS : swap_fun σ z ∈ S := hσ
          simp only [S, Set.mem_preimage, hE_def, Set.mem_setOf_eq] at hσS
          obtain ⟨h, hC_h, hgap⟩ := hσS
          let p : Fin (2 * m) → Bool := fun j => decide (h (merged j) ≠ c (merged j))
          apply Finset.mem_biUnion.mpr
          refine ⟨p, hPS_finite.mem_toFinset.mpr ⟨h, hC_h, fun i => rfl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          have h_gid := h_gap_identity h σ
          simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hgap
          rw [div_sub_div_same] at hgap
          show (1 : ℝ) / ↑m * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2
          simp only [p] at hgap ⊢
          simpa [h_gid, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hgap
        have hexp_nn : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
        calc ((Finset.univ.filter (fun σ : SignVector m =>
                swap_fun σ z ∈ S)).card : ℝ)
            ≤ ((PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card h_filter_biUnion
          _ ≤ ∑ p ∈ PS, ((Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ PS,
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
              Finset.sum_le_sum (fun p _ => h_markov_bound (patToCoeff p) (h_ptc_bound p))
          _ = (PS.card : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (↑(GrowthFunction X C (2 * m)) : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast hPS_card
              · exact mul_nonneg (Nat.cast_nonneg' _) hexp_nn
          _ = (↑(GrowthFunction X C (2 * m)) : ℝ) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by ring
      exact_mod_cast ENNReal.ofReal_le_ofReal h_bound_real
    have hcard_ne_zero : (Fintype.card (SignVector m) : ℝ≥0∞) ≠ 0 :=
      ne_of_gt hcard_pos
    have hcard_ne_top : (Fintype.card (SignVector m) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have hbound_ennreal : ENNReal.ofReal bound =
        ENNReal.ofReal (↑(GrowthFunction X C (2 * m))) *
        ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
      rw [hbound_def, ENNReal.ofReal_mul (Nat.cast_nonneg' _)]
    have hS_nullmeas : MeasureTheory.NullMeasurableSet S ν := by
      show MeasureTheory.NullMeasurableSet (eqv ⁻¹' E) ν
      have : E = {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
        rfl
      rw [this]
      exact (hE_nullmeas.preimage h_mp.quasiMeasurePreserving)
    have h_swap_mp : ∀ σ : SignVector m, MeasureTheory.MeasurePreserving (swap_fun σ) ν ν := by
      intro σ
      exact ⟨h_swap_meas σ, h_swap_pres σ⟩
    have h_pointwise : ∀ z : Fin m → X × X,
        (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z)
        ≤ ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
      intro z
      have h_sum_eq_card : (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z) =
          ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal) := by
        simp only [Set.indicator_apply, Pi.one_apply, Set.mem_preimage]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h_sum_eq_card]
      calc ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal)
          ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
            h_per_z_bound z
        _ = ENNReal.ofReal (bound * (Fintype.card (SignVector m) : ℝ)) := by
            congr 1; rw [hbound_def]; ring
        _ = ENNReal.ofReal bound * ENNReal.ofReal (Fintype.card (SignVector m) : ℝ) := by
            rw [ENNReal.ofReal_mul hbound_nonneg]
        _ = ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
            congr 1; rw [ENNReal.ofReal_natCast]
    exact finite_exchangeability_bound swap_fun S h_swap_mp hS_nullmeas
      (ENNReal.ofReal bound) h_pointwise

/-- On the double sample, the probability that any hypothesis has
    EmpErr' - EmpErr ≥ ε/2 is bounded by GF(C,2m) · exp(-mε²/8).

    **References:** SSBD Theorem 6.7, Hoeffding (1963), Serfling (1974) -/
theorem double_sample_pattern_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin m => D))
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) *
    Real.exp (-(↑m * ε ^ 2 / 8)) with hbound_def
  have hbound_nonneg : 0 ≤ bound := by
    apply mul_nonneg
    · exact Nat.cast_nonneg' (GrowthFunction X C (2 * m))
    · exact (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i)))
      (zeroOneLoss Bool) ≥ ε / 2} with hE_def
  by_cases hC : C = ∅
  · -- Event is empty when C is empty
    have hE_empty : E = ∅ := by
      ext p; simp only [hE_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨h_hyp, h_in_C, _⟩
      rw [hC] at h_in_C; exact h_in_C
    rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
  · -- C is nonempty
    by_cases hε2 : 2 < ε
    · -- EmpiricalError ∈ [0,1], so gap ∈ [-1,1] and ε/2 > 1 makes event empty
      have hE_empty : E = ∅ := by
        ext p; simp only [hE_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ⟨h_hyp, h_in_C, h_gap⟩
        have h_emp_le : EmpiricalError X Bool h_hyp (fun i => (p.2 i, c (p.2 i)))
            (zeroOneLoss Bool) ≤ 1 := by
          simp only [EmpiricalError]
          split
          · linarith
          · next hm_ne =>
            have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
            rw [div_le_one hm_pos]
            calc Finset.univ.sum (fun i => zeroOneLoss Bool (h_hyp (p.2 i)) (c (p.2 i)))
                ≤ Finset.univ.sum (fun _ => (1 : ℝ)) :=
                  Finset.sum_le_sum (fun i _ => by simp [zeroOneLoss]; split <;> linarith)
              _ = ↑m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, mul_one]
        have h_emp_nn : 0 ≤ EmpiricalError X Bool h_hyp (fun i => (p.1 i, c (p.1 i)))
            (zeroOneLoss Bool) := by
          simp only [EmpiricalError]
          split
          · linarith
          · exact div_nonneg (Finset.sum_nonneg (fun i _ => by
              simp [zeroOneLoss]; split <;> linarith)) (Nat.cast_nonneg' m)
        linarith
      rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
    · -- ε ≤ 2
      push_neg at hε2
      by_cases h_triv : 1 ≤ bound
      · have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := by
          rw [hμ_def]; infer_instance
        calc (μ.prod μ) E
            ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
          _ = 1 := MeasureTheory.measure_univ
          _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
      · -- Case 4: C ≠ ∅, ε ∈ (0, 2], bound < 1
        push_neg at h_triv
        set μ_sum := MeasureTheory.Measure.pi
          (fun _ : Fin m ⊕ Fin m => D)
        set φ := MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin m ⊕ Fin m => X)
        have h_mp : MeasureTheory.MeasurePreserving φ μ_sum (μ.prod μ) := by
          show MeasureTheory.MeasurePreserving
            (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X))
            (MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin m => D))
            ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
              (MeasureTheory.Measure.pi (fun _ : Fin m => D)))
          exact MeasureTheory.measurePreserving_sumPiEquivProdPi
            (fun _ : Fin m ⊕ Fin m => D)
        have h_map : ∀ (S : Set ((Fin m → X) × (Fin m → X))),
            (μ_sum.map φ) S = μ_sum (φ ⁻¹' S) :=
          fun S => φ.map_apply S
        calc (μ.prod μ) E
            = μ_sum (φ ⁻¹' E) := by rw [← h_mp.map_eq]; exact h_map E
          _ ≤ ENNReal.ofReal bound := by
              rw [← show (μ.prod μ) E = μ_sum (φ ⁻¹' E) from by
                rw [← h_mp.map_eq]; exact h_map E]
              exact exchangeability_chain_bound D C c hmeas_C hc_meas m hm ε hε hε2
                (Set.nonempty_iff_ne_empty.mpr hC) hE_nullmeas

/-- Upper-tail Hoeffding: for iid Bernoulli(p) draws, the empirical average
    overshoots the mean by ≥ t with probability ≤ exp(-2mt²).

    This is the mirror of `hoeffding_one_sided` (which bounds the lower tail).
    The proof uses the same sub-Gaussian machinery with Z_i = indicator(x_i) - p
    (instead of p - indicator(x_i)). -/
theorem hoeffding_one_sided_upper {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≥ TrueErrorReal X h c D + t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set p := TrueErrorReal X h c D with hp_def
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  set Z : Fin m → (Fin m → X) → ℝ := fun i xs => indicator (xs i) - p with hZ_def
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set S := {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) ≥ p + t} with hS_def
  have h_set_sub : S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
    intro xs hxs
    simp only [Set.mem_setOf_eq] at hxs ⊢
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [hS_def, Set.mem_setOf_eq, EmpiricalError,
      Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hxs
    have h_div : p + t ≤ (∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))) / (m : ℝ) := hxs
    rw [le_div_iff₀ hm_pos] at h_div
    linarith
  calc μ S
      ≤ μ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} :=
        MeasureTheory.measure_mono h_set_sub
    _ = ENNReal.ofReal (μ.real {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : MeasureTheory.IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
        set g : X → ℝ := fun x => indicator x - p with hg_def
        have hZ_eq : ∀ i : Fin m, ∀ xs : Fin m → X, Z i xs = g (xs i) := by
          intros i xs; simp [hZ_def, hg_def]
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x; simp only [hind_def, zeroOneLoss]
          split
          · exact ⟨le_refl 0, zero_le_one⟩
          · exact ⟨zero_le_one, le_refl 1⟩
        have h_g_bound : ∀ x : X, g x ∈ Set.Icc (-p) (1 - p) := by
          intro x; have hix := h_ind_bound x
          simp only [hg_def, Set.mem_Icc] at hix ⊢
          constructor <;> linarith [hix.1, hix.2]
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          have hmeas_eq : MeasurableSet {a : X | h a = c a} := by
            have : {a : X | h a = c a} = {a : X | h a ≠ c a}ᶜ := by ext x; simp
            rw [this]; exact hmeas.compl
          exact Measurable.ite hmeas_eq measurable_const measurable_const
        have h_g_meas : Measurable g := h_ind_meas.sub measurable_const
        have h_g_ae_bound : ∀ᵐ x ∂D, g x ∈ Set.Icc (-p) (1 - p) :=
          Filter.Eventually.of_forall h_g_bound
        have h_int_ind : ∫ x, indicator x ∂D = p := by
          simp only [hind_def, zeroOneLoss, hp_def, TrueErrorReal, TrueError]
          have h_ite_eq : (fun x => if h x = c x then (0 : ℝ) else 1) =
              Set.indicator {x | h x ≠ c x} 1 := by
            ext x; simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
            by_cases hx : h x = c x <;> simp [hx]
          rw [h_ite_eq, integral_indicator_one hmeas]
          simp only [Measure.real]
        have h_int_g : ∫ x, g x ∂D = 0 := by
          simp only [hg_def]
          rw [integral_sub
            (Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound))
            (integrable_const p)]
          simp [h_int_ind]
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g
            ((‖(1 - p) - (-p)‖₊ / 2) ^ 2) D :=
          ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable h_g_ae_bound h_int_g
        have h_param_eq : ‖(1 - p) - (-p)‖₊ = (1 : NNReal) := by
          have hsub : (1 - p) - (-p) = (1 : ℝ) := by ring
          rw [hsub]; simp [nnnorm_one]
        have h_param_simp : (‖(1 - p) - (-p)‖₊ / 2) ^ 2 = ((1 : NNReal) / 2) ^ 2 := by
          rw [h_param_eq]
        rw [h_param_simp] at h_g_subG
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (xs : Fin m → X) => g (xs i)) μ := by
          rw [hμ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun xs : Fin m → X => g (xs i)) ((1 / 2 : NNReal) ^ 2) μ := by
          intro i
          have h_of_map : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (xs : Fin m → X) => xs i) ((1 / 2 : NNReal) ^ 2) μ := by
            apply ProbabilityTheory.HasSubgaussianMGF.of_map
              (measurable_pi_apply i).aemeasurable
            rw [hμ_def, MeasureTheory.measurePreserving_eval _ i |>.map_eq]
            exact h_g_subG
          exact h_of_map
        have h_eps_pos : (0 : ℝ) ≤ ↑m * t := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep
          (c := fun _ => (1 / 2 : NNReal) ^ 2)
          (s := Finset.univ)
          (fun i _ => h_subG_each i)
          h_eps_pos
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 / 2 : NNReal) ^ 2 : NNReal)) =
            ↑m * (1 / 2 : NNReal) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [h_sum_c] at h_hoeff
        suffices h_exp_eq : Real.exp (-(↑m * t) ^ 2 / (2 * ↑(↑m * (1 / 2 : NNReal) ^ 2 : NNReal))) =
            Real.exp (-2 * ↑m * t ^ 2) by
          rw [h_exp_eq] at h_hoeff
          exact h_hoeff
        congr 1
        push_cast
        field_simp

/-- Symmetrization step for the lower tail: P[∃h: EmpErr-TrueErr ≥ ε] ≤ 2·P_{double}[∃h: EmpErr_S-EmpErr_{S'} ≥ ε/2].

    Mirror of `symmetrization_step` for the opposite direction.
    Uses `hoeffding_one_sided_upper` instead of `hoeffding_one_sided`. -/
theorem symmetrization_step_lower {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set A := {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    with hA_def
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hB_def
  suffices h_half : (1 : ℝ≥0∞) / 2 * μ A ≤ (μ.prod μ) B by
    have h2 : μ A ≤ 2 * ((1 : ℝ≥0∞) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact h2.trans (mul_le_mul_right h_half 2)
  set B' := MeasureTheory.toMeasurable (μ.prod μ) B with hB'_def
  have hB'_meas : MeasurableSet B' := MeasureTheory.measurableSet_toMeasurable _ _
  set f : (Fin m → X) → ℝ≥0∞ := fun xs => μ (Prod.mk xs ⁻¹' B') with hf_def
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  have h_cond : ∀ xs ∈ A, (1 : ℝ≥0∞) / 2 ≤ f xs := by
    intro xs hxs
    obtain ⟨h_star, h_star_in_C, h_gap⟩ := hxs
    set S_ghost := {xs' : Fin m → X | EmpiricalError X Bool h_star
        (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_star
        (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥ ε / 2} with hS_ghost_def
    have h_ghost_sub_B : S_ghost ⊆ Prod.mk xs ⁻¹' B := by
      intro xs' hxs'
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def]
      exact ⟨h_star, h_star_in_C, hxs'⟩
    have h_B_sub_B' : Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B' :=
      Set.preimage_mono (MeasureTheory.subset_toMeasurable _ _)
    calc (1 : ℝ≥0∞) / 2
        ≤ μ S_ghost := by
          have hmeas_disagree : MeasurableSet {x | h_star x ≠ c x} :=
            (measurableSet_eq_fun (hmeas_C h_star h_star_in_C) hc_meas).compl
          have h_emp_nonneg : 0 ≤ EmpiricalError X Bool h_star
              (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
            simp only [EmpiricalError]
            split
            · exact le_refl 0
            · apply div_nonneg
              · apply Finset.sum_nonneg; intro i _
                simp only [zeroOneLoss]; split <;> linarith
              · positivity
          have h_true_le_one : TrueErrorReal X h_star c D ≤ 1 := by
            simp only [TrueErrorReal, TrueError]
            have h_le : D {x | h_star x ≠ c x} ≤ 1 := by
              calc D {x | h_star x ≠ c x} ≤ D Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_le_of_le_ofReal one_pos.le
              (by rw [ENNReal.ofReal_one]; exact h_le)
          by_cases hε1 : ε ≤ 1
          case neg =>
            push_neg at hε1
            have h_gap_bound : EmpiricalError X Bool h_star
                (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
                TrueErrorReal X h_star c D ≤ 1 := by
              have h_emp_le_one : EmpiricalError X Bool h_star
                  (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≤ 1 := by
                simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
                rw [div_le_one (Nat.cast_pos.mpr hm)]
                calc ∑ i : Fin m, zeroOneLoss Bool (h_star (xs i)) (c (xs i))
                    ≤ ∑ _i : Fin m, (1 : ℝ) := by
                      apply Finset.sum_le_sum; intro i _
                      simp only [zeroOneLoss]; split <;> linarith
                  _ = ↑m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              have h_true_nonneg : 0 ≤ TrueErrorReal X h_star c D := by
                simp only [TrueErrorReal, TrueError]; positivity
              linarith
            linarith
          case pos =>
          have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
          have hε2_le_one : ε / 2 ≤ 1 := by linarith
          have h_hoeff := hoeffding_one_sided_upper D h_star c m hm (ε / 2) hε2_pos hε2_le_one
            hmeas_disagree
          have h_exp_le_half : Real.exp (-2 * ↑m * (ε / 2) ^ 2) ≤ 1 / 2 := by
            have h_exp_eq : -2 * ↑m * (ε / 2) ^ 2 = -(↑m * ε ^ 2 / 2) := by ring
            rw [h_exp_eq]
            have h_half : Real.log 2 ≤ ↑m * ε ^ 2 / 2 := by linarith
            have h_two_le_exp : (2 : ℝ) ≤ Real.exp (↑m * ε ^ 2 / 2) := by
              calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
                _ ≤ Real.exp (↑m * ε ^ 2 / 2) := Real.exp_le_exp_of_le h_half
            rw [Real.exp_neg, show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
            exact inv_anti₀ (by positivity) h_two_le_exp
          set H_set := {xs' : Fin m → X | EmpiricalError X Bool h_star
              (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥
              TrueErrorReal X h_star c D + ε / 2} with hH_set_def
          have h_H_le_half : μ H_set ≤ 1 / 2 := by
            calc μ H_set
                ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * (ε / 2) ^ 2)) := h_hoeff
              _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h_exp_le_half
              _ = 1 / 2 := by
                  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
                  simp [ENNReal.ofReal_one]
          have h_prob : MeasureTheory.IsProbabilityMeasure μ := by
            rw [hμ_def]; infer_instance
          have h_compl_ge : 1 / 2 ≤ μ H_setᶜ := by
            have h_total : 1 ≤ μ H_set + μ H_setᶜ := by
              have : μ Set.univ ≤ μ H_set + μ H_setᶜ := by
                calc μ Set.univ = μ (H_set ∪ H_setᶜ) := by rw [Set.union_compl_self]
                  _ ≤ μ H_set + μ H_setᶜ := measure_union_le _ _
              rwa [measure_univ] at this
            have h_H_ne_top : μ H_set ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top
                (h_H_le_half.trans (by norm_num))
            calc (1 : ℝ≥0∞) / 2
                = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - μ H_set := tsub_le_tsub_left h_H_le_half 1
              _ ≤ (μ H_set + μ H_setᶜ) - μ H_set := tsub_le_tsub_right h_total (μ H_set)
              _ = μ H_setᶜ := ENNReal.add_sub_cancel_left h_H_ne_top
          have h_compl_sub : H_setᶜ ⊆ S_ghost := by
            intro xs' hxs'
            simp only [Set.mem_compl_iff, hH_set_def, Set.mem_setOf_eq, not_le] at hxs'
            simp only [hS_ghost_def, Set.mem_setOf_eq, ge_iff_le]
            linarith
          exact h_compl_ge.trans (MeasureTheory.measure_mono h_compl_sub)
      _ ≤ μ (Prod.mk xs ⁻¹' B') :=
          MeasureTheory.measure_mono (h_ghost_sub_B.trans h_B_sub_B')
  have h_markov : (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ :=
    mul_meas_ge_le_lintegral hf_meas _
  have h_prod : (μ.prod μ) B' = ∫⁻ xs, μ (Prod.mk xs ⁻¹' B') ∂μ :=
    MeasureTheory.Measure.prod_apply hB'_meas
  calc (1 : ℝ≥0∞) / 2 * μ A
      ≤ (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} := by
        apply mul_le_mul_right
        exact MeasureTheory.measure_mono h_cond
    _ ≤ ∫⁻ xs, f xs ∂μ := h_markov
    _ = (μ.prod μ) B' := h_prod.symm
    _ = (μ.prod μ) B := MeasureTheory.measure_toMeasurable B

/-! ## T4: Symmetrization Uniform Convergence Bound (two-sided) -/

/-- The symmetrization uniform convergence bound: two-sided version.
    P[∃h∈C: |TrueErr-EmpErr| ≥ ε] ≤ 4·GF(C,2m)·exp(-mε²/8).

    **References:** SSBD Theorem 6.7, Kakade-Tewari Lecture 19 -/
theorem symmetrization_uc_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε}
    ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set gf_exp := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hgf_exp_def
  have hgf_exp_nn : 0 ≤ gf_exp := mul_nonneg (Nat.cast_nonneg' _) (Real.exp_pos _).le
  set upper := {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
  have h_upper : μ upper ≤ ENNReal.ofReal (2 * gf_exp) := by
    have h1 := symmetrization_step D C c hmeas_C hc_meas m hm ε hε hm_large
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ upper ≤ 2 * (μ.prod μ) _ := h1
      _ ≤ 2 * ENNReal.ofReal gf_exp := by exact mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  set lower := {xs : Fin m → X | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
      TrueErrorReal X h c D ≥ ε}
  have h_lower : μ lower ≤ ENNReal.ofReal (2 * gf_exp) := by
    have h1 := symmetrization_step_lower D C c hmeas_C hc_meas m hm ε hε hm_large
    have h_swap : (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
      let swap_equiv : (Fin m → X) × (Fin m → X) ≃ᵐ (Fin m → X) × (Fin m → X) :=
        MeasurableEquiv.prodComm
      set S1 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      set S2 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      have h_preimage : ⇑swap_equiv ⁻¹' S2 = S1 := by
        ext p
        show (p.2, p.1) ∈ S2 ↔ p ∈ S1
        simp only [S1, S2, Set.mem_setOf_eq]
      have h_swap_eq_swap : (⇑swap_equiv : (Fin m → X) × (Fin m → X) → _) = Prod.swap := rfl
      have h_sym : (μ.prod μ).map swap_equiv = μ.prod μ := by
        rw [show (μ.prod μ).map ⇑swap_equiv = (μ.prod μ).map Prod.swap from by
          rw [h_swap_eq_swap]]
        exact MeasureTheory.Measure.prod_swap (μ := μ) (ν := μ)
      calc (μ.prod μ) S1
          = (μ.prod μ) (⇑swap_equiv ⁻¹' S2) := by rw [h_preimage]
        _ = ((μ.prod μ).map swap_equiv) S2 := by rw [swap_equiv.map_apply]
        _ = (μ.prod μ) S2 := by rw [h_sym]
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ lower ≤ 2 * (μ.prod μ) _ := h1
      _ = 2 * (μ.prod μ) _ := by rw [h_swap]
      _ ≤ 2 * ENNReal.ofReal gf_exp := mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have h_abs_sub : {xs : Fin m → X | ∃ h ∈ C,
      |TrueErrorReal X h c D -
       EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ⊆ upper ∪ lower := by
    intro xs ⟨h, hC, hgap⟩
    simp only [Set.mem_union]
    by_cases h_pos : TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ 0
    · exact Or.inl ⟨h, hC, by rwa [abs_of_nonneg h_pos] at hgap⟩
    · push_neg at h_pos
      have hgap' : -(TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)) ≥ ε := by
        rwa [abs_of_neg h_pos] at hgap
      exact Or.inr ⟨h, hC, by linarith⟩
  calc μ {xs | ∃ h ∈ C, |TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ≤ μ (upper ∪ lower) := MeasureTheory.measure_mono h_abs_sub
    _ ≤ μ upper + μ lower := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * gf_exp) + ENNReal.ofReal (2 * gf_exp) :=
        add_le_add h_upper h_lower
    _ = ENNReal.ofReal (2 * gf_exp + 2 * gf_exp) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    _ = ENNReal.ofReal (4 * gf_exp) := by ring_nf
    _ = ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := by rw [hgf_exp_def]; ring_nf

/-! ## T5: Arithmetic — Growth Function × Exponential ≤ δ -/


/-- Trivial bound: GrowthFunction ≤ 2^n for all concept classes.
    Each restriction to an n-element set yields a function in S → Bool,
    and there are at most 2^n such functions. -/
private lemma growth_function_le_two_pow {X : Type u}
    (C : ConceptClass X Bool) (n : ℕ) :
    GrowthFunction X C n ≤ 2 ^ n := by
  unfold GrowthFunction
  by_cases h_empty : (Set.range fun (S : { S : Finset X // S.card = n }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) = ∅
  · simp only [h_empty, csSup_empty]; exact Nat.zero_le _
  · -- Range is nonempty
    have h_ne : Set.Nonempty (Set.range fun (S : { S : Finset X // S.card = n }) =>
        ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) :=
      Set.nonempty_iff_ne_empty.mpr h_empty
    apply csSup_le h_ne
    rintro _ ⟨S, rfl⟩
    let T : Finset X := (↑S : Finset X)
    letI : Fintype ↥T := Finset.fintypeCoeSort T
    have hBound' : ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
        Set (↥T → Bool)).ncard ≤ 2 ^ n := by
      calc ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
              Set (↥T → Bool)).ncard
          ≤ Nat.card (↥T → Bool) := Set.ncard_le_card _
        _ = Nat.card Bool ^ Nat.card ↥T := Nat.card_fun
        _ = 2 ^ n := by simp [Nat.card_eq_fintype_card, Fintype.card_coe, T, S.prop]
    simpa [T] using hBound'

set_option maxHeartbeats 800000 in
theorem growth_exp_le_delta {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hv_bound : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ ∧
    2 * Real.log 2 ≤ ↑m * ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hv_pos : (0 : ℝ) < ↑v := Nat.cast_pos.mpr hv
  have hv1_pos : (0 : ℝ) < ↑v + 1 := by linarith
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase_pos : 0 < 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by positivity
  have hm_real_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have he_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hm_delta : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) ≤ ↑m * δ := by
    rwa [div_le_iff₀ hδ] at hm_bound
  have hv1_ge_2 : (2 : ℝ) ≤ ↑v + 1 := by
    have : (1 : ℝ) ≤ ↑v := Nat.one_le_cast.mpr hv; linarith
  have hfact_le : (↑((v + 1).factorial) : ℝ) ≤ (↑v + 1) ^ (v + 1) := by
    exact_mod_cast Nat.factorial_le_pow (v + 1)
  have hm_pow_ge_1 : (1 : ℝ) ≤ ↑m ^ v := by
    exact one_le_pow₀ (Nat.one_le_cast.mpr hm)
  have hexp_pow_ge_1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) := by
    exact one_le_pow₀ (by linarith)
  constructor
  · -- Part 1: 4 * GF(C, 2m) * exp(-mε²/8) ≤ δ
    by_cases hvm : v ≤ 2 * m
    · -- Case A: v ≤ 2m — use Sauer-Shelah + sum_choose_le_exp_pow
      have hgf_exp : (GrowthFunction X C (2 * m) : ℝ) ≤
          (Real.exp 1 * ↑(2 * m) / ↑v) ^ v := by
        have h1 : (GrowthFunction X C (2 * m) : ℝ) ≤
            ↑(∑ i ∈ Finset.range (v + 1), (2 * m).choose i) :=
          Nat.cast_le.mpr (hv_bound (2 * m) hvm)
        have h2 := sum_choose_le_exp_pow v (2 * m) hv hvm
        calc (GrowthFunction X C (2 * m) : ℝ) ≤ _ := h1
          _ = ∑ i ∈ Finset.range (v + 1), ↑((2 * m).choose i) := by push_cast; rfl
          _ ≤ _ := h2
      set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
      have ht_pos : 0 < t := by positivity
      have h_pow_exp : t ^ v * Real.exp (-t) ≤ ↑((v + 1).factorial) / t :=
        pow_mul_exp_neg_le_factorial_div ht_pos
      have h2m_eq : (↑(2 * m) : ℝ) = 16 * t / ε ^ 2 := by
        rw [ht_def]; field_simp; push_cast; ring
      set K := 16 * Real.exp 1 / (↑v * ε ^ 2) with hK_def
      have hK_pos : 0 < K := by rw [hK_def]; positivity
      have hgf_factor : (Real.exp 1 * ↑(2 * m) / ↑v) ^ v = K ^ v * t ^ v := by
        have : Real.exp 1 * ↑(2 * m) / ↑v = K * t := by
          rw [h2m_eq, hK_def, ht_def]
          have hv_ne : (↑v : ℝ) ≠ 0 := ne_of_gt hv_pos
          have hε2_ne : ε ^ 2 ≠ 0 := ne_of_gt hε2
          field_simp
        rw [this, mul_pow]
      have hB_eq : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 = K * ↑v * (↑v + 1) := by
        rw [hK_def]; field_simp
      have hCvv : K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤ ↑m * δ := by
        have : (K * ↑v * (↑v + 1)) ^ (v + 1) =
            K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
          rw [mul_pow, mul_pow]
        rw [← this, ← hB_eq]; exact hm_delta
      have hv_pow_ge_1 : (1 : ℝ) ≤ ↑v ^ v :=
        one_le_pow₀ (Nat.one_le_cast.mpr hv)
      have h_2_le_ev : (2 : ℝ) ≤ Real.exp 1 * ↑v ^ v := by
        have : Real.exp 1 * 1 ≤ Real.exp 1 * ↑v ^ v := by nlinarith [hv_pow_ge_1]
        linarith
      have hkey : 2 * ↑((v + 1).factorial) ≤
          Real.exp 1 * ↑v ^ v * (↑v + 1) ^ (v + 1) := by
        have hfact_nonneg : (0 : ℝ) ≤ ↑((v + 1).factorial) := Nat.cast_nonneg _
        have hv1_pow_pos : (0 : ℝ) < (↑v + 1) ^ (v + 1) := pow_pos hv1_pos (v + 1)
        nlinarith [hfact_le, h_2_le_ev]
      have hKeps : K * ε ^ 2 * ↑v ^ (v + 1) = 16 * Real.exp 1 * ↑v ^ v := by
        have hveps_ne : (↑v : ℝ) * ε ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hv_pos) (ne_of_gt hε2)
        have : K * (↑v * ε ^ 2) = 16 * Real.exp 1 := by
          rw [hK_def]; field_simp
        calc K * ε ^ 2 * ↑v ^ (v + 1)
            = K * (↑v * ε ^ 2) * ↑v ^ v := by rw [pow_succ]; ring
          _ = 16 * Real.exp 1 * ↑v ^ v := by rw [this]
      have hstepA : 32 * ↑((v + 1).factorial) ≤
          K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) := by nlinarith [hkey, hKeps]
      have hstepB : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v ≤
          ε ^ 2 * (↑m * δ) := by
        have : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v =
            ε ^ 2 * (K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) := by
          rw [show K ^ (v + 1) = K ^ v * K from pow_succ K v]; ring
        rw [this]; nlinarith [hCvv, hε2]
      have hcombine : 32 * ↑((v + 1).factorial) * K ^ v ≤ δ * ↑m * ε ^ 2 := by
        nlinarith [hstepA, hstepB, pow_pos hK_pos v]
      have hfinal : 4 * K ^ v * (↑((v + 1).factorial) / t) ≤ δ := by
        rw [ht_def, show 4 * K ^ v * (↑((v + 1).factorial) / (↑m * ε ^ 2 / 8)) =
            32 * ↑((v + 1).factorial) * K ^ v / (↑m * ε ^ 2) from by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑m * ε ^ 2)]
        linarith [hcombine]
      calc 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8))
          ≤ 4 * (K ^ v * t ^ v) * Real.exp (-t) := by
            rw [ht_def]; nlinarith [hgf_exp, hgf_factor,
              Real.exp_pos (-(↑m * ε ^ 2 / 8))]
        _ = 4 * K ^ v * (t ^ v * Real.exp (-t)) := by ring
        _ ≤ 4 * K ^ v * (↑((v + 1).factorial) / t) := by
            nlinarith [h_pow_exp, pow_pos hK_pos v]
        _ ≤ δ := hfinal
    · -- Case B: v > 2m — use trivial bound GF(C, 2m) ≤ 2^{2m}
      push_neg at hvm
      have hvm' : 2 * m + 1 ≤ v := by omega
      have hgf_trivial : GrowthFunction X C (2 * m) ≤ 2 ^ (2 * m) :=
        growth_function_le_two_pow C (2 * m)
      set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
      have ht_pos : 0 < t := by positivity
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      have hTaylor : t ^ (v + 1) / ↑((v + 1).factorial) ≤ Real.exp t :=
        Real.pow_div_factorial_le_exp t (le_of_lt ht_pos) (v + 1)
      have hTaylor2 : t ^ (v + 1) ≤ ↑((v + 1).factorial) * Real.exp t := by
        have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (v + 1)))).mp hTaylor
        linarith [mul_comm (Real.exp t) (↑((v + 1).factorial) : ℝ)]
      have hexp_le : Real.exp (-t) ≤ ↑((v + 1).factorial) / t ^ (v + 1) := by
        have hexp_t_pos := Real.exp_pos t
        have ht_pow_pos := pow_pos ht_pos (v + 1)
        rw [Real.exp_neg, le_div_iff₀ ht_pow_pos]
        calc (Real.exp t)⁻¹ * t ^ (v + 1) ≤ 1 * ↑((v + 1).factorial) := by
              rw [inv_mul_le_iff₀ hexp_t_pos, one_mul]
              linarith [hTaylor2]
          _ = ↑((v + 1).factorial) := one_mul _
      have hchain1 : 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤
          4 * (2 : ℝ) ^ (2 * m) * (↑((v + 1).factorial) / t ^ (v + 1)) := by
        have hgf_cast : (↑(GrowthFunction X C (2 * m)) : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
          exact_mod_cast hgf_trivial
        rw [ht_def]
        have hexp_pos := Real.exp_pos (-(↑m * ε ^ 2 / 8))
        have hfact_div_pos : (0 : ℝ) < ↑((v + 1).factorial) / t ^ (v + 1) := by positivity
        nlinarith [hgf_cast, hexp_le]
      suffices hchain2 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) ≤ δ * t ^ (v + 1) by
        have ht_pow_pos := pow_pos ht_pos (v + 1)
        have : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) ≤ δ := by
          exact div_le_of_le_mul₀ (le_of_lt ht_pow_pos) (le_of_lt hδ) hchain2
        have hrewrite : 4 * (2 : ℝ) ^ (2 * m) * (↑((v + 1).factorial) / t ^ (v + 1)) =
            4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) := by
          rw [mul_div_assoc']
        linarith [hchain1, hrewrite]
      rw [ht_def]
      have hm_delta_expand :
          (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤ ↑m * δ * (ε ^ 2) ^ (v + 1) := by
        have := hm_delta
        rw [div_pow, div_le_iff₀ (pow_pos hε2 (v + 1))] at this
        linarith
      have h_pow_bound : 4 * (2 : ℝ) ^ (2 * m) * (8 : ℝ) ^ (v + 1) ≤
          (16 : ℝ) ^ (v + 1) := by
        have h_2_pow : 4 * (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ (v + 1) := by
          have : (4 : ℝ) = 2 ^ 2 := by norm_num
          rw [this, ← pow_add]
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
        have : (16 : ℝ) ^ (v + 1) = (2 : ℝ) ^ (v + 1) * (8 : ℝ) ^ (v + 1) := by
          rw [show (16 : ℝ) = 2 * 8 from by norm_num, mul_pow]
        rw [this]
        exact mul_le_mul_of_nonneg_right h_2_pow (pow_nonneg (by norm_num) (v + 1))
      have hgoal_equiv : δ * (↑m * ε ^ 2 / 8) ^ (v + 1) =
          δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) / (8 : ℝ) ^ (v + 1) := by
        rw [div_pow]; ring
      rw [hgoal_equiv]
      rw [show 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) =
          (4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1)) /
          (8 : ℝ) ^ (v + 1) from by
        rw [mul_div_cancel_right₀]; exact pow_ne_zero _ (by norm_num)]
      rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0:ℝ) < 8) (v + 1))]
      have hfact_cast : (↑((v + 1).factorial) : ℝ) ≥ 0 := Nat.cast_nonneg _
      have hstep1 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1) ≤
          (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
        nlinarith [h_pow_bound, hfact_le,
          pow_pos (show (0:ℝ) < 16 by norm_num) (v + 1)]
      have hstep2 : (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤
          (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v := by
        rw [mul_pow, mul_pow]
        have h1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) * ↑m ^ v :=
          one_le_mul_of_one_le_of_one_le hexp_pow_ge_1 hm_pow_ge_1
        have h16pos := pow_pos (show (0:ℝ) < 16 by norm_num) (v + 1)
        have hv1pos := pow_pos hv1_pos (v + 1)
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt h16pos) (le_of_lt hv1pos))]
      have hstep3 : (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v ≤
          δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by
        have hmul : ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤
            ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) :=
          mul_le_mul_of_nonneg_left hm_delta_expand (pow_nonneg (Nat.cast_nonneg _) v)
        have hpow_eq : (↑m : ℝ) ^ (v + 1) = ↑m ^ v * ↑m := pow_succ (↑m : ℝ) v
        calc (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v
            = ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) := by ring
          _ ≤ ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) := hmul
          _ = δ * (↑m ^ v * ↑m) * (ε ^ 2) ^ (v + 1) := by ring
          _ = δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by rw [← hpow_eq]
      linarith [hstep1, hstep2, hstep3]
  · -- Part 2: 2 * log 2 ≤ m * ε²
    have hlog2_le_1 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]; linarith
    suffices h : 2 ≤ ↑m * ε ^ 2 by nlinarith
    by_cases hcase : ε ^ 2 ≤ 16 * Real.exp 1 * (↑v + 1)
    · have hbase_ge_1 : 1 ≤ 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by
        rw [le_div_iff₀ hε2]; linarith
      have hpow_ge : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤
          (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) :=
        le_self_pow₀ hbase_ge_1 (by omega)
      have : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤ ↑m * δ := by linarith [hm_delta]
      have : 16 * Real.exp 1 * (↑v + 1) ≤ ↑m * δ * ε ^ 2 := by
        rwa [div_le_iff₀ hε2] at this
      nlinarith
    · push_neg at hcase
      have hm_ge_1 : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm
      nlinarith

end
end Lax185574Proofs.Lib.EpsilonSource
