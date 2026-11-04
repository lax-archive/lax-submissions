import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Analysis.Convex.StdSimplex

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-! Internal definitions used by the proof implementation. -/

namespace Lax185574Proofs.Lib.Internal.EpsilonNets

universe u

/-- A set meeting every range of probability at least `ε`. -/
def IsEpsilonNet {α : Type u} [DecidableEq α] (𝓕 : Finset (Finset α))
    (p : α → ℝ) (ε : ℝ) (S : Finset α) : Prop :=
  ∀ A ∈ 𝓕, ε ≤ ∑ x ∈ A, p x → (S ∩ A).Nonempty


end Lax185574Proofs.Lib.Internal.EpsilonNets
