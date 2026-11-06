import Lax185574.BallTypes
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.BallTypes` for the classes of the archive,
derived from the concept.
-/

namespace Lax185574Proofs.Shim.BallTypes

open Lax185574.Graphs Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GraphBalls
open Lax185574Proofs.Interface

theorem ball_types (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax185574.DpMinimality.DpMinimal (ofOld C)) (r s : ℕ) :
    ∃ k t a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), ∃ Astar : Finset (Fin n), A ⊆ Astar ∧
        Astar.card ≤ a * (A.card + 1) ^ k ∧
        ∀ H : SimpleGraph (Fin n), IsDefinableFlip G s H → ∀ v : Fin n,
          Disjoint (graphBall H r {v}) (Astar : Set (Fin n)) →
            atomicTypeCount H (graphBall H r {v}) (A : Set (Fin n)) ≤ t := by
  obtain ⟨k, t, a, h⟩ := Lax185574.BallTypes.ball_types (ofOld C)
    hC r s
  exact ⟨k, t, a, fun n G hG => h (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.BallTypes
