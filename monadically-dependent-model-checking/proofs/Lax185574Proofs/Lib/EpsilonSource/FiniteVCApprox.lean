/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/PureMath/FiniteVCApprox.lean.
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
import Lax185574Proofs.Lib.EpsilonSource.EmpiricalPMF

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000
open Finset Classical

/-- Expected value `∑ h, μ.prob h * f h` of a real-valued test under a finitely supported
distribution. The base expectation primitive of the approximation layer; specialised to
indicator tests in `boolTestExpectation`. -/
def trueExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h : H, μ.prob h * f h

/-- Expected value of a `Bool`-valued test under a finite distribution, via the
indicator embedding `if f h then 1 else 0`. The central quantity of the finite-VC
approximation layer: a TV bound on distributions translates to a uniform bound on test
expectations via `expectation_approx_of_tv`. -/
def boolTestExpectation {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) : ℝ :=
  trueExpectation μ (fun h => if f h then (1 : ℝ) else 0)

/-- A convex combination of values in `{0, 1}` is nonnegative. -/
lemma boolTestExpectation_nonneg {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    0 ≤ boolTestExpectation μ f :=
  Finset.sum_nonneg fun h _ =>
    mul_nonneg (μ.prob_nonneg h) (by simp only; split_ifs <;> norm_num)

/-- A convex combination of values in `{0, 1}` is at most `1`. -/
lemma boolTestExpectation_le_one {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    boolTestExpectation μ f ≤ 1 := by
  simp only [boolTestExpectation, trueExpectation]
  calc ∑ h : H, μ.prob h * (if f h then (1 : ℝ) else 0)
      ≤ ∑ h : H, μ.prob h := Finset.sum_le_sum fun h _ =>
        mul_le_of_le_one_right (μ.prob_nonneg h) (by split_ifs <;> norm_num)
    _ = 1 := μ.prob_sum_one

/-- Bridges the `FinitePMF` view and the sample-average view: the expectation of a
`Bool`-valued test under the empirical PMF of a sample equals the sample average
`(1/T) ∑_t f (s_t)`. This lets the MWU updates and the approximation transfer
principle live in the same distributional framework. -/
lemma boolTestExpectation_empirical_eq_avg
    {H : Type*} [Fintype H] [DecidableEq H]
    {T : ℕ} (hT : 0 < T) (hs : Fin T → H) (f : H → Bool) :
    boolTestExpectation (empiricalPMF hT hs) f =
    (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) / T := by
  simp only [boolTestExpectation, trueExpectation, empiricalPMF]
  conv_lhs => arg 2; ext h; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  have := Finset.card_eq_sum_card_fiberwise (f := hs)
    (s := univ) (t := univ) (fun _ _ => Finset.mem_univ _)
  conv_lhs => rw [show (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) =
    ∑ h : H, ∑ t ∈ univ.filter (fun t => hs t = h),
      (if f (hs t) then (1 : ℝ) else 0) from by
    rw [← Finset.sum_biUnion (s := univ)]
    · congr 1; ext t; simp
    · intro h₁ _ h₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro t _ ht1 ht2; exact hne (ht1.symm.trans ht2)]
  congr 1; ext h
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Maps a finite family of `Bool`-valued functions to its image as a family of
accepting sets. The set-system view is what Mathlib's `Finset.Shatters` and
`Finset.vcDim` consume, so this is the entry point from the function-class view to the
combinatorial VC machinery. -/
def boolFamilyToFinsetFamily {H : Type*} [Fintype H] [DecidableEq H]
    (A : Finset (H → Bool)) : Finset (Finset H) :=
  A.image (fun f => Finset.univ.filter (fun h => f h = true))

/-- VC dimension of a finite `Bool`-valued family, computed via the set-system image
`boolFamilyToFinsetFamily` and Mathlib's `Finset.vcDim`. Declared `noncomputable`
because the underlying `vcDim` is. -/
noncomputable def Finset.boolVCDim {H : Type*} [Fintype H] [DecidableEq H]
    (A : Finset (H → Bool)) : ℕ :=
  (boolFamilyToFinsetFamily A).vcDim

end
end Lax185574Proofs.Lib.EpsilonSource
