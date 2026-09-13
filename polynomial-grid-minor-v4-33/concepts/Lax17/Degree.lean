import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
---
title: Degree bounds
type: definition
---
For a finite simple graph, a vertex has degree at most \(d\) when its
neighbourhood has at most \(d\) vertices.  A graph has maximum degree at most
\(d\) when this holds at every vertex.

The definition is phrased through a finite set representing the neighbourhood.
It therefore does not require choosing a decidable adjacency relation.
-/

namespace Lax17.Degree

universe u

/-- `N` is the neighbourhood of `v` in `G`. -/
def IsNeighbourhood {V : Type u} (G : SimpleGraph V) (v : V)
    (N : Finset V) : Prop :=
  ∀ w : V, w ∈ N ↔ G.Adj v w

/-- The degree of `v` in `G` is at most `d`. -/
def AtMost {V : Type u} (G : SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighbourhood G v N ∧ N.card ≤ d

/-- The degree of `v` in `G` is exactly `d`. -/
def Exactly {V : Type u} (G : SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighbourhood G v N ∧ N.card = d

/-- Every vertex of `G` has degree at most `d`. -/
def MaximumAtMost {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, AtMost G v d

end Lax17.Degree
