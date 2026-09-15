import Lax683916.NeighborhoodSetSystemRepresentation

namespace Lax683916Proofs.NeighborhoodSetSystemRepresentation

open Lax683916.NeighborhoodSetSystems
open Lax683916.NeighborhoodSetSystemRepresentation

universe u

/-- Regard a simple graph as its family of open neighborhoods. -/
def toNeighborhoodSetSystem {V : Type u} (G : SimpleGraph V) :
    NeighborhoodSetSystem V where
  neighborhood u := {v | G.Adj u v}
  symmetric u v := by
    change G.Adj u v ↔ G.Adj v u
    exact G.adj_comm u v
  loopless u := by
    change ¬G.Adj u u
    exact G.loopless.irrefl u

/-- Read symmetric loopless neighborhood membership as graph adjacency. -/
def toSimpleGraph {V : Type u} (N : NeighborhoodSetSystem V) :
    SimpleGraph V where
  Adj u v := v ∈ N.neighborhood u
  symm := ⟨fun u v h ↦ (N.symmetric u v).mp h⟩
  loopless := ⟨N.loopless⟩

private theorem left_inverse {V : Type u} (G : SimpleGraph V) :
    toSimpleGraph (toNeighborhoodSetSystem G) = G := by
  cases G
  rfl

private theorem right_inverse {V : Type u} (N : NeighborhoodSetSystem V) :
    toNeighborhoodSetSystem (toSimpleGraph N) = N := by
  cases N
  rfl

/-- The explicit equivalence underlying the representation theorem. -/
def equivalence (V : Type u) :
    SimpleGraph V ≃ NeighborhoodSetSystem V where
  toFun := toNeighborhoodSetSystem
  invFun := toSimpleGraph
  left_inv := left_inverse
  right_inv := right_inverse

/--
---
conclusion: Lax683916.NeighborhoodSetSystemRepresentation.simpleGraphEquiv
---
The neighborhood of a vertex consists exactly of its adjacent vertices.

# Proof strategy

Repackage adjacency as a vertex-indexed family of sets. Symmetry and
irreflexivity give the two neighborhood-system laws, and both round trips are
definitionally the original relation and laws.

# Attribution

Directly from the definition of the open neighborhood of a vertex.
-/
theorem simpleGraphEquiv (V : Type u) :
    Nonempty (RepresentationEquiv V) :=
  ⟨{
    toEquiv := equivalence V
    map_mem := fun _ _ _ ↦ Iff.rfl }⟩

end Lax683916Proofs.NeighborhoodSetSystemRepresentation
