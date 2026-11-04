/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/Complexity/Generalization.lean.
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
import Lax185574Proofs.Lib.EpsilonSource.VCDimension

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000

/-- Empirical error: average loss on a finite sample. -/
noncomputable def EmpiricalError (X : Type u) (Y : Type v)
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y)
    (loss : LossFunction Y) : ℝ :=
  if m = 0 then 0
  else (Finset.univ.sum fun i => loss (h (S i).1) (S i).2) / m

/-- True error (0-1 loss, realizable case): D-probability of disagreement.
    This is what PACLearnable's success event measures. -/
noncomputable def TrueError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ENNReal :=
  D { x | h x ≠ c x }

/-- True error in ℝ: for use in bounds involving subtraction/absolute value.
    COUNTER-1 of TrueError. The toReal bridge loses information when the measure is ⊤. -/
noncomputable def TrueErrorReal (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ℝ :=
  (TrueError X h c D).toReal

/-- Key arithmetic lemma for PAC bound: for t > 0, t^d * exp(-t) ≤ (d+1)!/t.
    Follows from exp(t) ≥ t^(d+1)/(d+1)! (partial sum of Taylor series). -/
lemma pow_mul_exp_neg_le_factorial_div {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ d * Real.exp (-t) ≤ ↑((d + 1).factorial) / t := by
  have h1 : t ^ (d + 1) / ↑((d + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t (le_of_lt ht) (d + 1)
  have h2 : t ^ (d + 1) ≤ ↑((d + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (d + 1)))).mp h1
    linarith [mul_comm (Real.exp t) (↑(d + 1).factorial)]
  rw [pow_succ] at h2
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp : 0 < Real.exp t := Real.exp_pos t
  rw [le_div_iff₀ ht]
  calc t ^ d * Real.exp (-t) * t
      = t ^ d * t * Real.exp (-t) := by ring
    _ = t ^ (d + 1) * Real.exp (-t) := by rw [← pow_succ]
    _ ≤ ↑((d + 1).factorial) * Real.exp t * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (-t)))
    _ = ↑((d + 1).factorial) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end
end Lax185574Proofs.Lib.EpsilonSource
