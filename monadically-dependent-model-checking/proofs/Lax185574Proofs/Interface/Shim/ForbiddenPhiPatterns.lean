import Lax185574.ForbiddenPhiPatterns
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.ForbiddenPhiPatterns` for the classes of
the archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ForbiddenPhiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPatterns Lax185574Proofs.Interface

theorem forbidden_phi_patterns (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax185574.DpMinimality.DpMinimal (ofOld C))
    {p : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasPhiPattern G φ t t := by
  obtain ⟨t, ht⟩ := Lax185574.ForbiddenPhiPatterns.forbidden_phi_patterns (ofOld C)
    hC φ
  exact ⟨t, fun n G hG => ht (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.ForbiddenPhiPatterns
