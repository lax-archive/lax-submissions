import Lax68

set_option autoImplicit false

namespace Lax68Proofs

/--
---
conclusion: Lax68.Outerplanar.outerplanar_planar
---
An outerplane drawing is, after forgetting its boundary condition, a planar
drawing.
-/
theorem outerplanar_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.Outerplanar.IsOuterplanar G →
    Lax68.Planar.IsPlanar G := by
  rintro ⟨drawing⟩
  exact ⟨drawing.toStraightLineDrawing⟩

/--
---
conclusion: Lax68.MaximalOuterplanar.maximalOuterplanar_outerplanar
---
Maximal outerplanarity includes outerplanarity.
-/
theorem maximalOuterplanar_outerplanar {V : Type*} {G : SimpleGraph V} :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h => h.1

/--
---
conclusion: Lax68.MaximalOuterplanar.maximalOuterplanar_planar
assumptions:
  - Lax68.MaximalOuterplanar.maximalOuterplanar_outerplanar
  - Lax68.Outerplanar.outerplanar_planar
---
Every maximal outerplanar graph is planar.
-/
theorem maximalOuterplanar_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.Outerplanar.outerplanar_planar
      (Lax68.MaximalOuterplanar.maximalOuterplanar_outerplanar h)

/--
---
conclusion: Lax68.Triangles.triangle_outerplanar
assumptions:
  - Lax68.MaximalOuterplanar.maximalOuterplanar_outerplanar
  - Lax68.Triangles.triangle_maximalOuterplanar
---
Every triangle is outerplanar.
-/
theorem triangle_outerplanar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Triangles.IsTriangle G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h =>
    Lax68.MaximalOuterplanar.maximalOuterplanar_outerplanar
      (Lax68.Triangles.triangle_maximalOuterplanar h)

/--
---
conclusion: Lax68.Triangles.triangle_planar
assumptions:
  - Lax68.Outerplanar.outerplanar_planar
  - Lax68.Triangles.triangle_outerplanar
---
Every triangle is planar.
-/
theorem triangle_planar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Triangles.IsTriangle G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.Outerplanar.outerplanar_planar
      (Lax68.Triangles.triangle_outerplanar h)

/--
---
conclusion: Lax68.Stars.star_outerplanar
assumptions:
  - Lax68.Stars.star_tree
  - Lax68.Trees.tree_outerplanar
---
Every star is outerplanar.
-/
theorem star_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Stars.IsStar G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h =>
    Lax68.Trees.tree_outerplanar
      (Lax68.Stars.star_tree h)

/--
---
conclusion: Lax68.Stars.star_planar
assumptions:
  - Lax68.Outerplanar.outerplanar_planar
  - Lax68.Stars.star_outerplanar
---
Every star is planar.
-/
theorem star_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Stars.IsStar G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.Outerplanar.outerplanar_planar
      (Lax68.Stars.star_outerplanar h)

/--
---
conclusion: Lax68.Ladders.ladder_grid
---
Every ladder is a two-row grid.
-/
theorem ladder_grid {V : Type*} {G : SimpleGraph V} :
    Lax68.Ladders.IsLadder G →
    Lax68.GridsAndWalls.IsGrid G := by
  rintro ⟨n, hn, hiso⟩
  exact ⟨n, 2, hn, by decide, hiso⟩

/--
---
conclusion: Lax68.Ladders.ladder_planar
assumptions:
  - Lax68.GridsAndWalls.grid_planar
  - Lax68.Ladders.ladder_grid
---
Every ladder is planar.
-/
theorem ladder_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.Ladders.IsLadder G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.GridsAndWalls.grid_planar
      (Lax68.Ladders.ladder_grid h)

/--
---
conclusion: Lax68.HalinGraphs.halin_planar
---
Every Halin graph is planar.
-/
theorem halin_planar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.HalinGraphs.IsHalin G →
    Lax68.Planar.IsPlanar G := by
  rintro ⟨construction⟩
  exact ⟨construction.drawing⟩

/--
---
conclusion: Lax68.Wheels.wheel_planar
assumptions:
  - Lax68.HalinGraphs.halin_planar
  - Lax68.Wheels.wheel_halin
---
Every wheel is planar.
-/
theorem wheel_planar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Wheels.IsWheel G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.HalinGraphs.halin_planar
      (Lax68.Wheels.wheel_halin h)

/--
---
conclusion: Lax68.Trees.tree_planar
assumptions:
  - Lax68.Outerplanar.outerplanar_planar
  - Lax68.Trees.tree_outerplanar
---
Every tree is planar.
-/
theorem tree_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Trees.IsTree G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.Outerplanar.outerplanar_planar
      (Lax68.Trees.tree_outerplanar h)

/--
---
conclusion: Lax68.Paths.path_outerplanar
assumptions:
  - Lax68.Paths.path_tree
  - Lax68.Trees.tree_outerplanar
---
Every path is outerplanar.
-/
theorem path_outerplanar {V : Type*} {G : SimpleGraph V} :
    Lax68.Paths.IsPath G →
    Lax68.Outerplanar.IsOuterplanar G := by
  intro h
  have ht := Lax68.Paths.path_tree h
  obtain ⟨n, _, ⟨e⟩⟩ := h
  let : Finite V := Finite.of_injective e e.injective
  exact Lax68.Trees.tree_outerplanar ht

/--
---
conclusion: Lax68.Paths.path_planar
assumptions:
  - Lax68.Outerplanar.outerplanar_planar
  - Lax68.Paths.path_outerplanar
---
Every path is planar.
-/
theorem path_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.Paths.IsPath G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.Outerplanar.outerplanar_planar
      (Lax68.Paths.path_outerplanar h)

/--
---
conclusion: Lax68.Triangulations.triangulationOf_planar
---
Every triangulation of a planar graph is planar.
-/
theorem triangulationOf_planar {V : Type*}
    {G T : SimpleGraph V} :
    Lax68.Planar.IsPlanar G →
    Lax68.Triangulations.IsTriangulationOf G T →
    Lax68.Planar.IsPlanar T :=
  fun _ h => h.2.2.1

end Lax68Proofs
