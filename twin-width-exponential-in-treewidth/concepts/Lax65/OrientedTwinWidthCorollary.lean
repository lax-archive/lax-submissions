import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax65.OrientedTwinWidth
import Lax65.GraphFamily

/-!
---
title: Twin-width exponential in oriented twin-width
type: corollary
---
For every small *ε* > 0, there is a family *F* of graphs with unbounded
twin-width such that for every *G* ∈ *F*:
tww(*G*) > 2^{(1−*ε*)(otww(*G*) − 1)}.

# Formalization notes

The statement is made for every *ε* > 0; the paper's "small" signals that the
bound is only of interest for small *ε*, since it weakens as *ε* grows.
Twin-width is the parameter of the prerequisite submission.
-/

namespace Lax65.OrientedTwinWidthCorollary

open Lax48.TwinWidth Lax65.OrientedTwinWidth Lax65.GraphFamily

/-- For every `ε > 0`, some family of graphs with unbounded twin-width has
`2 ^ ((1 - ε) (otww G - 1)) < tww G` for all its members. -/
axiom exists_family_two_rpow_orientedTwinWidth_lt_twinWidth
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set FiniteGraph, HasUnboundedTwinWidth F ∧
      ∀ G ∈ F,
        (2 : ℝ) ^ ((1 - ε) * ((orientedTwinWidth G.graph : ℝ) - 1)) <
          twinWidth G.graph

end Lax65.OrientedTwinWidthCorollary
