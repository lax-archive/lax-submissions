import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax683916.SpanningTwoUniformHypergraphs

/-!
---
title: Hypergraph representation of simple graphs
type: theorem
---
Simple graphs on `V` are equivalent to spanning 2-uniform hypergraphs on
`V`. Graph edges become two-element hyperedges and no vertex is lost.

# Formalization notes

The representation is an equivalence of types. Spanning fixes the explicit
hypergraph vertex set, while 2-uniformity identifies the hyperedge set with
the ordinary unordered edges of a simple graph.
-/

namespace Lax683916.HypergraphRepresentation

open Lax683916.SpanningTwoUniformHypergraphs

universe u

/-- An equivalence that sends graph edges to two-element hyperedges. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ SpanningTwoUniformHypergraph V
  /-- A pair is a hyperedge in the image exactly when its two elements are adjacent. -/
  map_pair : ∀ (G : SimpleGraph V) (u v : V),
    {u, v} ∈ (toEquiv G).hypergraph.edgeSet ↔ G.Adj u v

/-- Simple graphs and spanning 2-uniform hypergraphs on the same vertices are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.HypergraphRepresentation
