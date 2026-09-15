import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: 3-connected graphs
type: definition
---
A finite simple graph is 3-connected when it has at least four vertices and
remains connected after deleting any set of at most two vertices.

# Formalization notes

Deleting a finite set `S` is represented by the induced graph on the subtype
of vertices outside `S`. The cardinality condition rules out the small graphs
for which deletion-connectivity alone would make the usual definition
degenerate.
-/

set_option autoImplicit false

namespace Lax881656.ThreeConnected

/-- A finite graph is 3-connected if deleting at most two vertices leaves a
connected graph, and the original graph has at least four vertices. -/
def IsThreeConnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected

end Lax881656.ThreeConnected
