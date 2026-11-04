import Lax185574.ClosureTheorem
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.ClosureTheorem` for the classes of the
archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ClosureTheorem

open Lax185574.Graphs Lax185574.Flips Lax185574.GraphBalls Lax185574.Partitions
open Lax185574Proofs.Interface

theorem closure_theorem (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C) (r : ℕ) :
    ∃ c s a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), ∃ Astar : Finset (Fin n),
        Astar.card ≤ a * (A.card + 1) ^ c ∧
        ∀ v : Fin n, v ∉ A →
          ∃ S : Finset (Fin n), S ⊆ Astar ∧ S.card ≤ s ∧
            ∃ H : SimpleGraph (Fin n),
              IsFlip G (atomicTypes G (S : Set (Fin n))) H ∧
              Disjoint (graphBall H r {v}) (A : Set (Fin n)) := by
  obtain ⟨c, s, a, h⟩ := Lax185574.ClosureTheorem.closure_theorem (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC) r
  exact ⟨c, s, a, fun n G hG => h (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.ClosureTheorem
