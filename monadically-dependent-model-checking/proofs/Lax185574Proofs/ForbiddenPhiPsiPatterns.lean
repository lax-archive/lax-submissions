import Lax185574.DpMinimalPatterns
import Lax185574.ForbiddenPhiPsiPatterns
import Lax185574.MonadicDependenceDpMinimal

namespace Lax185574Proofs.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.PhiPsiPatterns

/--
---
conclusion: Lax185574.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns
---
The class is dp-minimal because it is monadically dependent, and a
dp-minimal class excludes `(φ, ψ)`-patterns of some order.
-/
theorem forbidden_phiPsi_patterns (C : GraphClass) (hC : MonadicallyDependent C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPattern G.toSimpleGraph φ ψ t t :=
  Lax185574.DpMinimalPatterns.forbidden_phiPsi_patterns C
    (Lax185574.MonadicDependenceDpMinimal.dpMinimal_of_monadicallyDependent C hC) φ ψ

end Lax185574Proofs.ForbiddenPhiPsiPatterns
