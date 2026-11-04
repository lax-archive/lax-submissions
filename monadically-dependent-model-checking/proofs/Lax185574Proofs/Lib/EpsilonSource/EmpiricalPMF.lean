/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/PureMath/ApproxMinimax.lean.
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
import Lax185574Proofs.Lib.EpsilonSource.FinitePMF

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000
open Finset Classical

/-- Build FinitePMF from empirical frequencies of a finite sequence. -/
def empiricalPMF {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → α) : FinitePMF α where
  prob a := (univ.filter (fun t => rs t = a)).card / (T : ℝ)
  prob_nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum_one := by
    rw [← Finset.sum_div]
    suffices h : (∑ a : α, ((univ.filter (fun t : Fin T => rs t = a)).card : ℝ)) = T by
      rw [h]; exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := rs) (s := univ) (t := univ)
      (fun t _ => mem_univ (rs t))
    simp only [card_univ, Fintype.card_fin] at hfib
    exact_mod_cast hfib.symm

end
end Lax185574Proofs.Lib.EpsilonSource
