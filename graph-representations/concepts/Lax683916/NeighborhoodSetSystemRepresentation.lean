import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax683916.NeighborhoodSetSystems

/-!
---
title: Neighborhood-set-system representation of simple graphs
type: theorem
---
Simple graphs on `V` are equivalent to symmetric loopless neighborhood set
systems indexed by `V`. The set assigned to `u` is exactly its open
neighborhood.

# Formalization notes

The equivalence retains the vertex type and adjacency relation exactly. An
unindexed family `Set (Set V)` would forget which vertex owns a neighborhood,
so the vertex indexing is essential for an equivalence with all simple
graphs.
-/

namespace Lax683916.NeighborhoodSetSystemRepresentation

open Lax683916.NeighborhoodSetSystems

universe u

/-- An equivalence that sends every graph to its vertex-indexed open neighborhoods. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between simple graphs and neighborhood set systems. -/
  toEquiv : SimpleGraph V ≃ NeighborhoodSetSystem V
  /-- Membership in the image neighborhood is exactly adjacency. -/
  map_mem : ∀ (G : SimpleGraph V) (u v : V),
    v ∈ (toEquiv G).neighborhood u ↔ G.Adj u v

/-- Simple graphs and symmetric loopless neighborhood set systems are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.NeighborhoodSetSystemRepresentation
