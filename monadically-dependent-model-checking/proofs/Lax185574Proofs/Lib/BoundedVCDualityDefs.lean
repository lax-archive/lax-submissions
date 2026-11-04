import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/




namespace Lax185574Proofs.Lib.BoundedVCDuality

universe u

noncomputable def neighborhoodFamily {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.image (fun v => Finset.univ.filter (G.Adj v))

def Dominates {V : Type u} (G : SimpleGraph V) (S Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ x ∈ S, G.Adj x y

def Antidominates {V : Type u} (G : SimpleGraph V) (T X : Finset V) : Prop :=
  ∀ x ∈ X, ∃ y ∈ T, ¬ G.Adj x y



end Lax185574Proofs.Lib.BoundedVCDuality
