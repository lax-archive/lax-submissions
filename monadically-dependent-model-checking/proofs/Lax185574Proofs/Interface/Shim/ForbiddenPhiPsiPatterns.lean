import Lax185574.ForbiddenPhiPsiPatterns
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.ForbiddenPhiPsiPatterns` for the classes of
the archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574Proofs.Interface

theorem forbidden_phiPsi_patterns (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasPattern G φ ψ t t := by
  obtain ⟨t, ht⟩ := Lax185574.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC) φ ψ
  exact ⟨t, fun n G hG => ht (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.ForbiddenPhiPsiPatterns
