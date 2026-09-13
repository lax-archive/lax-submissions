import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

/-!
---
title: 3-connected graphs and 4-colorability
type: definition
---
A graph is $3$-connected when it has at least 4 vertices and remains
connected after deleting any set of at most two vertices. A graph is
$m$-colorable when its vertices have a proper coloring with at most $m$
colors; in particular, $4$-colorability is the case $m = 4$.
-/

open Finset

namespace Lax10.ThreeConnectedAndColorable

universe u

variable {V : Type u}

/-- A simple graph is colorable with at most $m$ colors. -/
def KColorable (m : Nat) (G : SimpleGraph V) : Prop :=
  G.Colorable m

/-- The induced graph obtained after deleting the vertices in $S$. -/
def deleteVertices (G : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ S} :=
  G.induce {v : V | v ∉ S}

/-- The set $S$ separates two vertices that remain after its deletion. -/
def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y : {v : V // v ∉ S}, ¬ (deleteVertices G S).Reachable x y

/--
A graph is $3$-connected when it has at least 4 vertices and no vertex
separator of size at most two.
-/
def ThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Nat.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → ¬ IsVertexSeparator G S

end Lax10.ThreeConnectedAndColorable
