/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/Basic.lean.
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

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000

/-- A concept is a function from domain to label. This is the atomic unit that
    concept classes collect and learners try to approximate. -/
def Concept (X : Type u) (Y : Type v) := X → Y

/-- A concept class is a set of concepts. Used by every paradigm, complexity
    measure, and criterion.

    Primary definition: Set of functions. Used for PAC/agnostic PAC where
    concept classes are sets over which VC dimension, Rademacher complexity,
    covering numbers, etc. are measured. Alternative definitions below for
    contexts requiring decidability, enumerability, or measurability. -/
abbrev ConceptClass (X : Type u) (Y : Type v) := Set (Concept X Y)

/-- A loss function measures the discrepancy between a prediction and true label. -/
def LossFunction (Y : Type v) := Y → Y → ℝ

/-- The 0-1 loss for classification. -/
noncomputable def zeroOneLoss (Y : Type v) [DecidableEq Y] : LossFunction Y :=
  fun y₁ y₂ => if y₁ = y₂ then 0 else 1

end
end Lax185574Proofs.Lib.EpsilonSource
