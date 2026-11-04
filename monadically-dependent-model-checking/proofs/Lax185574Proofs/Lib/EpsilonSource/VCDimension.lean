/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta

Adapted from formal-learning-theory-kernel, commit
7511199db276505a464fb8548e9369fc6cbc2209, FLT_Proofs/Complexity/VCDimension.lean.
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

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.EpsilonSource

noncomputable section
universe u v
set_option maxHeartbeats 800000

/-- A set S ⊆ X is shattered by concept class C if every labeling of S
    is realized by some concept in C. -/
def Shatters (X : Type u) (C : ConceptClass X Bool) (S : Finset X) : Prop :=
  ∀ f : S → Bool, ∃ c ∈ C, ∀ x : S, c (x : X) = f x

/-- VC dimension of a concept class: the size of the largest shattered set.
    Returns ℕ∞ = WithTop ℕ. -/
noncomputable def VCDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ)

/-- Growth function (shattering coefficient): π_C(m) = max_{|S|=m} |{c|_S : c ∈ C}|.
    For each m-element set S, counts the number of distinct restrictions of C to S,
    then takes the supremum over all such S. -/
noncomputable def GrowthFunction (X : Type u)
    (C : ConceptClass X Bool) : ℕ → ℕ :=
  fun m => sSup (Set.range fun (S : { S : Finset X // S.card = m }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard)

end
end Lax185574Proofs.Lib.EpsilonSource
