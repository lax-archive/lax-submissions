import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Lax68.StraightLineDrawings

/-!
---
title: Euler's formula
type: theorem
---
Let $G$ be a finite connected graph with a crossing-free straight-line drawing
in the plane. The *faces* of the drawing are the connected components of the
plane after removing all drawn points and edge segments. If the drawing has
$v$ vertices, $e$ edges and $f$ faces, then
$$v - e + f = 2.$$

The formula is stated as $v + f = e + 2$ in the extended natural numbers, so
that it also asserts that the number of faces is finite.
-/

set_option autoImplicit false

namespace Lax909950.EulerFormula

open Lax68.StraightLineDrawings

/-- The points of the plane covered by a straight-line drawing: the points of
the vertices together with the segments of the edges. -/
def image {V : Type*} {G : SimpleGraph V} (D : StraightLineDrawing G) : Set Point :=
  Set.range D.point ∪ ⋃ (a : V) (b : V) (_ : G.Adj a b), segment ℝ (D.point a) (D.point b)

/-- The faces of a straight-line drawing: the connected components of the
complement of its image. -/
def faces {V : Type*} {G : SimpleGraph V} (D : StraightLineDrawing G) : Set (Set Point) :=
  {F | ∃ x ∉ image D, F = connectedComponentIn (image D)ᶜ x}

/-- Euler's formula: a crossing-free straight-line drawing of a finite connected
graph with $v$ vertices and $e$ edges has exactly $f$ faces, where
$v + f = e + 2$. -/
axiom euler_formula {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (D : StraightLineDrawing G) :
  (Nat.card V : ℕ∞) + (faces D).encard = G.edgeSet.encard + 2

end Lax909950.EulerFormula
