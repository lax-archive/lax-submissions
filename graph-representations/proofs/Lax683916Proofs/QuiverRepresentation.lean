import Lax683916.QuiverRepresentation

namespace Lax683916Proofs.QuiverRepresentation

open Lax683916.ThinSymmetricLooplessQuivers

universe u v

/--
---
conclusion: Lax683916.QuiverRepresentation.exists_simpleGraph_representation
---
The adjacency relation records whether the corresponding arrow type is
inhabited.

# Proof strategy

Symmetry and looplessness make inhabitation a simple-graph relation. For a
thin quiver, each arrow type is equivalent to the lifted proposition that it
is inhabited: send an arrow to its witness and choose a witness in the reverse
direction; subsingleton elimination proves the inverse laws.

# Attribution

Directly from thinness, symmetry, and looplessness.
-/
theorem exists_simpleGraph_representation {V : Type u}
    (Q : ThinSymmetricLooplessQuiver.{u, v} V) :
    ∃ G : SimpleGraph V, Nonempty (Isomorphic Q (ofSimpleGraph G)) := by
  let G : SimpleGraph V := {
    Adj := fun a b ↦ Nonempty (Q.quiver.Hom a b)
    symm := ⟨fun a b h ↦ (Q.symmetric a b).mp h⟩
    loopless := ⟨fun a h ↦ (Q.loopless a).false h.some⟩ }
  refine ⟨G, ⟨⟨fun a b ↦ ?_⟩⟩⟩
  exact {
    toFun := fun f ↦ ⟨⟨f⟩⟩
    invFun := fun h ↦ Classical.choice h.down
    left_inv := fun f ↦ @Subsingleton.elim _ (Q.thin a b) _ _
    right_inv := fun h ↦ by
      cases h
      rfl }

end Lax683916Proofs.QuiverRepresentation
