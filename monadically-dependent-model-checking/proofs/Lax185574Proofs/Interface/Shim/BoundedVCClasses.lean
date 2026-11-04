import Lax185574.BoundedVCClasses
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.BoundedVCClasses` for the classes of the
archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.BoundedVCClasses

open Lax185574.Graphs Lax185574.VCDimension Lax185574Proofs.Interface

theorem exists_vcDim_le (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → vcDim G ≤ d := by
  obtain ⟨d, hd⟩ := Lax185574.BoundedVCClasses.exists_vcDim_le (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC)
  exact ⟨d, fun n G hG => hd (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.BoundedVCClasses
