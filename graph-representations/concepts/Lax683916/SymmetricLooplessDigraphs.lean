import Mathlib.Combinatorics.Digraph.Basic

/-!
---
title: Symmetric loopless digraph
type: definition
---
A symmetric loopless digraph is a directed graph in which every arrow is
accompanied by its reverse and no vertex has an arrow to itself.

# Formalization notes

The directed graph is bundled with symmetry and irreflexivity of its
adjacency relation. These are exactly the two laws carried by a simple graph,
but the bundle keeps the underlying object visibly in `Digraph V`.
-/

namespace Lax683916.SymmetricLooplessDigraphs

/-- A directed graph whose adjacency relation is symmetric and irreflexive. -/
structure SymmetricLooplessDigraph (V : Type*) where
  /-- The underlying directed graph. -/
  graph : Digraph V
  /-- Every directed edge occurs in both orientations. -/
  symm : Std.Symm graph.Adj
  /-- No vertex is adjacent to itself. -/
  loopless : Std.Irrefl graph.Adj

end Lax683916.SymmetricLooplessDigraphs
