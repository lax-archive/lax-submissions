import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
---
title: Grids and walls
type: definition
---

![Grid and wall illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/d0f2a7021b6428f55a4524763f47a4312c74348f/planar-graph-classes-v4-33/assets/grid-wall.svg "Grid and wall illustration")

A nonempty rectangular grid has vertices in rows and columns, with edges
between orthogonally consecutive positions. A wall is the brick-wall subgraph
obtained by retaining alternating vertical grid edges.
-/

set_option autoImplicit false

namespace Lax68.GridsAndWalls

def consecutive (a b : ℕ) : Prop :=
  a + 1 = b ∨ b + 1 = a

def WallAdjacent {m n : ℕ} (u v : Fin m × Fin n) : Prop :=
  (u.1 = v.1 ∧ consecutive u.2.val v.2.val) ∨
  (u.2 = v.2 ∧
    consecutive u.1.val v.1.val ∧
    (Nat.min u.1.val v.1.val + u.2.val) % 2 = 0)

def HasGridShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ m n : ℕ,
    0 < m ∧
    0 < n ∧
    Nonempty
      (G ≃g (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n))

def HasWallShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ m n : ℕ,
    0 < m ∧
    0 < n ∧
    ∃ e : Fin m × Fin n ≃ V,
      ∀ u v,
        G.Adj (e u) (e v) ↔ WallAdjacent u v

def IsGrid {V : Type*} (G : SimpleGraph V) : Prop :=
  HasGridShape G

def IsWall {V : Type*} (G : SimpleGraph V) : Prop :=
  HasWallShape G

end Lax68.GridsAndWalls
