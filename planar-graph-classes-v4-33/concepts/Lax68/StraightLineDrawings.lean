import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

/-!
---
title: Straight-line graph drawings
type: definition
---

![Straight-line drawing illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/straight-line-drawing.svg "Straight-line drawing illustration")

A straight-line drawing assigns distinct points of the real plane to the
vertices of a simple graph and draws every edge as the segment between its
endpoints. No vertex lies inside an edge and disjoint edges do not meet.
This is the geometric drawing certificate used by the planar-graph concept.
-/

set_option autoImplicit false

namespace Lax68.StraightLineDrawings

abbrev Point := ℝ × ℝ

structure StraightLineDrawing {V : Type*} (G : SimpleGraph V) where
  point : V → Point
  injective : Function.Injective point
  noVertexOnEdge :
    ∀ {a b c : V},
      G.Adj a b →
      c ≠ a →
      c ≠ b →
      point c ∉ segment ℝ (point a) (point b)
  disjointEdges :
    ∀ {a b c d : V},
      G.Adj a b →
      G.Adj c d →
      Disjoint ({a, b} : Set V) ({c, d} : Set V) →
      Disjoint
        (segment ℝ (point a) (point b))
        (segment ℝ (point c) (point d))

def HasStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (StraightLineDrawing G)

end Lax68.StraightLineDrawings
