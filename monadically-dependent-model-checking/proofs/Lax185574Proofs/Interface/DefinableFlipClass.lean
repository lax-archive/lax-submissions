import Lax185574.FlipsMonadicallyDependent
import Lax185574Proofs.Interface.Classes

/-!
The class of definable flips of `Lax185574.FlipsMonadicallyDependent`
and the one for the classes of the archive.

`Old.definableFlipClass` is the class of the `s`-definable flips of a
class of the archive. The class of the `s`-definable flips of a graph
class is contained in it, after `toOld`, and conversely.
-/

namespace Lax185574Proofs.Interface.Old

/-- The class of all `s`-definable flips of graphs from the class `C`
of the archive. -/
def definableFlipClass (C : Lax199508.GraphClasses.GraphClass) (s : ℕ) :
    Lax199508.GraphClasses.GraphClass :=
  fun n H => ∃ G : SimpleGraph (Fin n), C n G ∧ Lax185574.DefinableFlips.IsDefinableFlip G s H

end Lax185574Proofs.Interface.Old

namespace Lax185574Proofs.Interface

open Lax185574.Graphs Lax185574.FlipsMonadicallyDependent

theorem definableFlipClass_subset_ofOld (C : GraphClass) (s : ℕ) :
    definableFlipClass C s ⊆ ofOld (Old.definableFlipClass (toOld C) s) := by
  rintro H ⟨G, hG, F, hF, rfl⟩
  exact ⟨G.toSimpleGraph, hG, hF⟩

theorem old_definableFlipClass_le (C : Lax199508.GraphClasses.GraphClass) (s n : ℕ)
    (H : SimpleGraph (Fin n)) (h : Old.definableFlipClass C s n H) :
    toOld (definableFlipClass (ofOld C) s) n H := by
  obtain ⟨G, hG, hH⟩ := h
  exact ⟨Graph.ofSimpleGraph G, hG, H, hH, rfl⟩

end Lax185574Proofs.Interface
