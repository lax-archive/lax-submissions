import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax65.GraphFamily

/-!
---
title: Adding an apex can almost double twin-width
type: corollary
---
For every small *ε* > 0, there is a family *F* of graphs with unbounded
twin-width such that for every *G* ∈ *F*:
tww(*G*) > (2 − *ε*) tww(*G* − {*v*}), where *v* is a single vertex of *G*.

# Formalization notes

The vertex *v* depends on *G*: for every member of the family there is a
vertex whose deletion divides the twin-width by more than 2 − *ε*. The
statement is made for every *ε* > 0; the paper's "small" signals that the
bound is only of interest for small *ε*, since it weakens as *ε* grows.
Twin-width is the parameter of the prerequisite submission.
-/

namespace Lax65.ApexCorollary

open Lax48.TwinWidth Lax65.GraphFamily

/-- For every `ε > 0`, some family of graphs with unbounded twin-width has,
for each member `G`, a vertex `v` with `(2 - ε) tww (G - v) < tww G`. -/
axiom exists_family_twinWidth_deleteVertex_lt_twinWidth (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set FiniteGraph, HasUnboundedTwinWidth F ∧
      ∀ G ∈ F, ∃ v : Fin G.n,
        (2 - ε) * twinWidth (G.graph.induce {u | u ≠ v}) < twinWidth G.graph

end Lax65.ApexCorollary
