import Lax683916.HypergraphRepresentation
import Lax683916Proofs.SetSystemRepresentation

namespace Lax683916Proofs.HypergraphRepresentation

open Lax683916.SpanningTwoUniformHypergraphs
open Lax683916.TwoUniformSetSystems
open Lax683916.HypergraphRepresentation

universe u

variable {V : Type u}

/-- Regard a 2-uniform set system as a spanning hypergraph. -/
def setSystemToHypergraph (S : TwoUniformSetSystem V) :
    SpanningTwoUniformHypergraph V where
  hypergraph := {
    vertexSet := Set.univ
    edgeSet := S.sets
    subset_vertexSet_of_mem_edgeSet' := fun _ _ ↦ Set.subset_univ _ }
  spanning := rfl
  twoUniform := S.twoUniform

/-- Forget the fixed spanning vertex set of a spanning 2-uniform hypergraph. -/
def hypergraphToSetSystem (H : SpanningTwoUniformHypergraph V) :
    TwoUniformSetSystem V where
  sets := H.hypergraph.edgeSet
  twoUniform := H.twoUniform

private theorem left_inverse (S : TwoUniformSetSystem V) :
    hypergraphToSetSystem (setSystemToHypergraph S) = S := by
  cases S
  rfl

private theorem right_inverse (H : SpanningTwoUniformHypergraph V) :
    setSystemToHypergraph (hypergraphToSetSystem H) = H := by
  rcases H with ⟨⟨vertices, edges, edge_subset⟩, spanning, uniform⟩
  simp only at spanning
  subst vertices
  rfl

/-- The equivalence between 2-uniform set systems and their spanning hypergraphs. -/
def setSystemEquivHypergraph (V : Type u) :
    TwoUniformSetSystem V ≃ SpanningTwoUniformHypergraph V where
  toFun := setSystemToHypergraph
  invFun := hypergraphToSetSystem
  left_inv := left_inverse
  right_inv := right_inverse

/--
---
conclusion: Lax683916.HypergraphRepresentation.simpleGraphEquiv
---
The set-system representation of a simple graph becomes a hypergraph by
declaring the full ground type to be its vertex set.

# Proof strategy

Compose the proved graph–set-system equivalence with the structural
equivalence that adds or forgets the fixed spanning vertex set.

# Attribution

Direct elementary correspondence, factored through 2-uniform set systems.
-/
theorem simpleGraphEquiv (V : Type u) :
    Nonempty (RepresentationEquiv V) :=
  ⟨{
    toEquiv := (Lax683916Proofs.SetSystemRepresentation.equivalence V).trans
      (setSystemEquivHypergraph V)
    map_pair := by
      intro G u v
      exact Lax683916Proofs.SetSystemRepresentation.pair_mem_toSetSystem_iff G u v }⟩

end Lax683916Proofs.HypergraphRepresentation
