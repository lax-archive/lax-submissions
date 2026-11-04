import Lax185574.GaifmanGraph

/-!
---
title: Balls around vertex sets in a graph
type: definition
---
For a graph G, a radius r ∈ ℕ and a set C ⊆ V(G), the ball

Ball^G_r[C] = { w ∈ V(G) : dist^G(c, w) ≤ r for some c ∈ C }

is the union of the balls Ball^G_r[c] of radius r around the vertices
c ∈ C. For a vertex v it is written Ball^G_r[v], and for a tuple v̄ it
is the ball around the set of entries of v̄.

The distance between two sets is the minimum distance between their
elements. So dist^G(X, A) > r holds if and only if Ball^G_r[X] is
disjoint from A.

# Formalization notes

The ball is defined for a simple graph and an arbitrary set of centers.
"Distance at most r" is `GaifmanGraph.WithinDist`, a walk of length at
most r. Vertices in different components are at infinite distance. The
paper writes the closed ball defined here as Ball^G_r(v).

Statements of the form dist^G(X, A) > r, for sets or for the entries of
a tuple, are expressed as disjointness of Ball^G_r[X] and A. This
matches the paper's own reformulation of separation as an empty
intersection of a ball with a set. If A is empty, the distance is
infinite and the condition holds.
-/

namespace Lax185574.GraphBalls

open Lax185574.GaifmanGraph

universe u

variable {V : Type u}

/-- `Ball^G_r[C]`: the vertices within distance `r` of some vertex of
`C`. -/
def graphBall (G : SimpleGraph V) (r : ℕ) (C : Set V) : Set V :=
  {w | ∃ c ∈ C, WithinDist G r c w}

end Lax185574.GraphBalls
