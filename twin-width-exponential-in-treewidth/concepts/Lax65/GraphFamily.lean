import Lax48.TwinWidth

/-!
---
title: Families of graphs with unbounded twin-width
type: definition
---
A finite graph is a simple graph on a vertex set of the form {1, …, *n*}. A
family of graphs is a set of finite graphs; it has unbounded twin-width if
for every *d* it contains a graph of twin-width greater than *d*.
-/

namespace Lax65.GraphFamily

/-- A finite simple graph on the canonical vertex type `Fin n`. -/
structure FiniteGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin n)

/-- The family `F` contains graphs of arbitrarily large twin-width. -/
def HasUnboundedTwinWidth (F : Set FiniteGraph) : Prop :=
  ∀ d : ℕ, ∃ G ∈ F, d < Lax48.TwinWidth.twinWidth G.graph

end Lax65.GraphFamily
