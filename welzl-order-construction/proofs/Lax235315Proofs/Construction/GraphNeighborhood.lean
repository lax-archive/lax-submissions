import Lax195003.WelzlOrdersNeighborhoodSetSystem

/-!
The radius-one bridge used at the final concept boundary.
-/

namespace Lax235315Proofs.Construction.GraphNeighborhood

open Lax195003.WelzlOrdersNeighborhoodSetSystem

/-- The submitted open `1`-neighborhood is the ordinary neighbor set. -/
theorem openNeighborhood_one_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) :
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ 1} =
      G.neighborSet v := by
  ext u
  constructor
  · rintro ⟨huv, w, hw⟩
    have hw0 : w.length ≠ 0 := by
      intro hzero
      exact huv (w.eq_of_length_eq_zero hzero).symm
    have hw1 : w.length = 1 := by omega
    exact w.adj_of_length_eq_one hw1
  · intro huv
    have hadj : G.Adj v u := by simpa using huv
    exact ⟨huv.ne.symm, hadj.toWalk, by simp⟩

/-- The radius-one neighborhood set system is exactly the family of open
vertex neighborhoods. -/
theorem neighborhoodSetSystem_one {n : ℕ} (G : SimpleGraph (Fin n)) :
    neighborhoodSetSystem G 1 =
      {X : Set (Fin n) | ∃ v : Fin n, X = G.neighborSet v} := by
  ext X
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, openNeighborhood_one_eq G v⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, (openNeighborhood_one_eq G v).symm⟩

end Lax235315Proofs.Construction.GraphNeighborhood
