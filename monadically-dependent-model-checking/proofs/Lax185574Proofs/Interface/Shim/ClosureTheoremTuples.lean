import Lax185574.ClosureTheoremTuples
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.ClosureTheoremTuples` for the classes of the
archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ClosureTheoremTuples

open Lax185574.Graphs Lax185574.Flips Lax185574.GraphBalls Lax185574Proofs.Interface

theorem closure_theorem_tuples (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax185574.DpMinimality.DpMinimal (ofOld C)) (r k : ℕ) :
    ∃ c s a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), ∃ family : Finset (SimpleGraph (Fin n)),
        family.card ≤ a * (A.card + 1) ^ c ∧
        (∀ H ∈ family, ∃ P : Setoid (Fin n),
          Nat.card (Quotient P) ≤ s ∧ IsFlip G P H) ∧
        ∀ v : Fin k → Fin n, (∀ i, v i ∉ A) →
          ∃ H ∈ family, Disjoint (graphBall H r (Set.range v)) (A : Set (Fin n)) := by
  obtain ⟨c, s, a, h⟩ := Lax185574.ClosureTheoremTuples.closure_theorem_tuples (ofOld C)
    hC r k
  exact ⟨c, s, a, fun n G hG => h (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.ClosureTheoremTuples
