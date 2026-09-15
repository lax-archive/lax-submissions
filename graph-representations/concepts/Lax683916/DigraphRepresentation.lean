import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax683916.SymmetricLooplessDigraphs

/-!
---
title: Digraph representation of simple graphs
type: theorem
---
Simple graphs on a vertex type `V` are equivalent to symmetric loopless
digraphs on `V`. The equivalence preserves the adjacency relation exactly.

# Formalization notes

Both structures consist of the same relation and the same two laws. The
statement is therefore an equivalence of types, rather than merely a pair of
conversions or an isomorphism after changing the vertex type.
-/

namespace Lax683916.DigraphRepresentation

open Lax683916.SymmetricLooplessDigraphs

universe u

/-- An equivalence that retains exactly the same adjacency relation. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ SymmetricLooplessDigraph V
  /-- A directed edge in the image is exactly an edge of the original simple graph. -/
  map_adj : ∀ (G : SimpleGraph V) (u v : V),
    (toEquiv G).graph.Adj u v ↔ G.Adj u v

/-- Simple graphs and symmetric loopless digraphs on the same vertices are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.DigraphRepresentation
