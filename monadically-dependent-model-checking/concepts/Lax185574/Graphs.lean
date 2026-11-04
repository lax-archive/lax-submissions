import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Graphs and graph classes
type: definition
---
A *graph* has the vertices 0, 1, …, n − 1 for some n and a symmetric
and irreflexive adjacency relation. A *graph class* is a set of graphs.

# Formalization notes

The vertex count is part of the graph, so that a graph class is simply
a set of graphs and a graph can be passed to an algorithm as one value.
The fields are those of mathlib's `SimpleGraph` on `Fin n`, written out
so that the definition can be read without knowing mathlib.

The notions of graph theory in this submission are stated for mathlib's
`SimpleGraph`, whose library they use. A graph is turned into one by
`Graph.toSimpleGraph`, which keeps the vertices and the adjacency.
Conversely, `Graph.ofSimpleGraph` turns a simple graph on the vertices
0, 1, …, n − 1 into a graph.

A graph class need not be closed under isomorphism. Every notion applied
to graph classes in this submission is invariant under isomorphism
anyway.
-/

namespace Lax185574.Graphs

/-- A graph on the vertices `0, 1, …, n - 1`. -/
structure Graph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency relation. -/
  Adj : Fin n → Fin n → Prop
  /-- Adjacency is symmetric. -/
  symm : ∀ u v, Adj u v → Adj v u
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ v, ¬ Adj v v

/-- A graph class: a set of graphs. -/
abbrev GraphClass : Type := Set Graph

/-- The graph `G` as a mathlib `SimpleGraph` on its vertices
`0, 1, …, n - 1`, with the same adjacency. -/
def Graph.toSimpleGraph (G : Graph) : SimpleGraph (Fin G.n) where
  Adj := G.Adj
  symm := ⟨G.symm⟩
  loopless := ⟨G.loopless⟩

/-- The mathlib `SimpleGraph` `H` on the vertices `0, 1, …, n - 1` as a
graph, with the same adjacency. -/
def Graph.ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Graph :=
  ⟨n, H.Adj, fun _ _ h => H.adj_symm h, fun _ => H.irrefl⟩

end Lax185574.Graphs
