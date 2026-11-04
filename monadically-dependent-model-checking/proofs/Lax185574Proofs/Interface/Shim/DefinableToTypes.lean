import Lax185574.DefinableToTypes
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.DefinableToTypes` for the classes of the
archive, derived from the concept.
-/

namespace Lax185574Proofs.Shim.DefinableToTypes

open Lax185574.Graphs Lax185574.ConstructionSequences Lax185574.LocalDefinability
open Lax185574.Width Lax185574Proofs.Interface

theorem width_le_of_isRadiusDefinable (q : ℕ) :
    ∀ (C : Lax199508.GraphClasses.GraphClass),
      Lax710763.MonadicDependence.MonadicallyDependent C →
      ∀ q₀ : ℕ, ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ,
        ∀ (r s : ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
          (seq : List (Lax185574.PartialGraphs.PartialGraph (Fin n))),
          C n G → IsConstructionSequence G seq →
          IsRadiusDefinable G seq (r + 7 ^ q) c s q₀ →
          width r q seq ≤ F * (s + 1) ^ a := by
  intro C hC q₀
  obtain ⟨a, h⟩ := Lax185574.DefinableToTypes.width_le_of_isRadiusDefinable q (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC) q₀
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := h c
  exact ⟨F, fun r s n G seq hG => hF r s (Graph.ofSimpleGraph G) hG seq⟩

end Lax185574Proofs.Shim.DefinableToTypes
