import Mathlib.Combinatorics.Hypergraph.Basic

/-!
---
title: Spanning 2-uniform hypergraph
type: definition
---
A spanning 2-uniform hypergraph on `V` has all elements of `V` as vertices
and every hyperedge contains exactly two vertices.

# Formalization notes

Spanning is stated by equality with `Set.univ`, because `Hypergraph V` keeps
an explicit vertex set inside the ambient type. A separate looplessness field
would be derivable: every edge has cardinality two and therefore cannot be a
singleton.
-/

namespace Lax683916.SpanningTwoUniformHypergraphs

/-- A hypergraph with full vertex set and two-element edges. -/
structure SpanningTwoUniformHypergraph (V : Type*) where
  /-- The underlying hypergraph. -/
  hypergraph : Hypergraph V
  /-- Every element of the ambient type is a vertex. -/
  spanning : hypergraph.vertexSet = Set.univ
  /-- Every hyperedge contains exactly two vertices. -/
  twoUniform : ∀ e ∈ hypergraph.edgeSet, Set.ncard e = 2

end Lax683916.SpanningTwoUniformHypergraphs
