import Lax683916.DigraphRepresentation

namespace Lax683916Proofs.DigraphRepresentation

open Lax683916.SymmetricLooplessDigraphs
open Lax683916.DigraphRepresentation

universe u

/--
---
conclusion: Lax683916.DigraphRepresentation.simpleGraphEquiv
---
The two structures are identified by retaining the same adjacency relation.

# Proof strategy

Construct each direction by repackaging the adjacency relation together with
its symmetry and irreflexivity proofs. Both composites reduce to the original
structure.

# Attribution

Directly from the definitions of `SimpleGraph` and `Digraph`.
-/
theorem simpleGraphEquiv (V : Type u) :
    Nonempty (RepresentationEquiv V) := by
  exact ⟨{
    toEquiv := {
      toFun := fun G ↦ ⟨⟨G.Adj⟩, G.symm, G.loopless⟩
      invFun := fun D ↦ ⟨D.graph.Adj, D.symm, D.loopless⟩
      left_inv := fun G ↦ by
        cases G
        rfl
      right_inv := fun D ↦ by
        rcases D with ⟨⟨adj⟩, symm, loopless⟩
        rfl }
    map_adj := fun _ _ _ ↦ Iff.rfl }⟩

end Lax683916Proofs.DigraphRepresentation
