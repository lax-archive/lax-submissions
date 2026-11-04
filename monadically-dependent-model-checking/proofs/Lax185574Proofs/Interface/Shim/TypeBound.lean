import Lax185574.TypeBound
import Lax185574Proofs.Interface.MDBridge

/-!
The statement of `Lax185574.TypeBound` for the classes of the archive,
derived from the concept.
-/

namespace Lax185574Proofs.Shim.TypeBound

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Graphs Lax185574.FirstOrderTypes Lax185574.Colorings Lax185574Proofs.Interface

theorem typeCountOver_le (C : Lax199508.GraphClasses.GraphClass)
    (hC : Lax710763.MonadicDependence.MonadicallyDependent C) (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (colors : Fin c → Set (Fin n)) (U : Finset (Fin n)),
          @typeCountOver (withColors Language.graph c) (Fin n)
              (expansion G colors) k q Set.univ (U : Set (Fin n)) ≤
            F * (U.card + 1) ^ a := by
  obtain ⟨a, h⟩ := Lax185574.TypeBound.typeCountOver_le (ofOld C)
    ((monadicallyDependent_ofOld_iff C).mpr hC) k q
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := h c
  exact ⟨F, fun n G hG => hF (Graph.ofSimpleGraph G) hG⟩

end Lax185574Proofs.Shim.TypeBound
