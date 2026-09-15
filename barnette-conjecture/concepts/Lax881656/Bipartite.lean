import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
---
title: Bipartite graphs
type: definition
---
A simple graph is bipartite when its vertices admit a proper coloring with two
colors: adjacent vertices always receive different colors.

# Formalization notes

The predicate is stated through the canonical graph-coloring interface. For a
simple graph this is equivalent to a partition of the vertices into two
independent sets, including in the presence of isolated vertices.
-/

set_option autoImplicit false

namespace Lax881656.Bipartite

/-- A simple graph is bipartite when it is properly colorable with two colors. -/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Colorable 2

end Lax881656.Bipartite
