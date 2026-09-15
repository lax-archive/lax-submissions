import Mathlib.Data.Set.Basic

/-!
---
title: Neighborhood set system
type: definition
---
A neighborhood set system on `V` assigns a subset of `V` to every vertex.
Membership is symmetric, and no vertex belongs to its own neighborhood.

# Formalization notes

The family is indexed by `V`, rather than represented only by its range as a
`Set (Set V)`. Keeping the index records which vertex owns each neighborhood
and permits distinct vertices to have equal neighborhoods. The two laws are
exactly symmetry and irreflexivity of the associated membership relation.
-/

namespace Lax683916.NeighborhoodSetSystems

universe u

/-- A vertex-indexed family of open neighborhoods. -/
structure NeighborhoodSetSystem (V : Type u) where
  /-- The open neighborhood assigned to each vertex. -/
  neighborhood : V → Set V
  /-- Neighborhood membership is symmetric. -/
  symmetric : ∀ u v : V, v ∈ neighborhood u ↔ u ∈ neighborhood v
  /-- A vertex does not belong to its own open neighborhood. -/
  loopless : ∀ u : V, u ∉ neighborhood u

end Lax683916.NeighborhoodSetSystems
