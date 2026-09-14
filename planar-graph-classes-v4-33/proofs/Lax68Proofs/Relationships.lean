import Lax68

set_option autoImplicit false

namespace Lax68Proofs

/--
---
conclusion: Lax68.PathTree.path_tree
---
The standard path is connected. In a cycle, its greatest vertex would have
two distinct neighbours below it, but a path has only one such neighbour.
-/
theorem path_tree {V : Type*} {G : SimpleGraph V} :
    Lax68.Paths.IsPath G → Lax68.Trees.IsTree G := by
  classical
  rintro ⟨n, hn, ⟨e⟩⟩
  apply e.isTree_iff.mpr
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  refine ⟨⟨SimpleGraph.pathGraph_preconnected n⟩, ?_⟩
  intro v p hp
  let S := p.support.toFinset
  have hS : S.Nonempty := ⟨v, by simp [S]⟩
  let m := S.max' hS
  have hm : m ∈ p.support := by
    simpa [S] using Finset.max'_mem S hS
  let q := p.rotate m hm
  have hq : q.IsCycle := hp.rotate hm
  have bound : ∀ x ∈ q.support, x ≤ m := by
    intro x hx
    apply Finset.le_max'
    simpa [S, q, SimpleGraph.Walk.mem_support_rotate_iff] using hx
  have hs := bound q.snd (q.getVert_mem_support 1)
  have ht := bound q.penultimate (q.getVert_mem_support (q.length - 1))
  have hsadj := SimpleGraph.pathGraph_adj.mp (q.adj_snd hq.not_nil)
  have htadj := SimpleGraph.pathGraph_adj.mp (q.adj_penultimate hq.not_nil)
  apply hq.snd_ne_penultimate
  apply Fin.ext
  change q.snd.val ≤ m.val at hs
  change q.penultimate.val ≤ m.val at ht
  omega

/--
---
conclusion: Lax68.StarTree.star_tree
---
A star is connected through its centre. A cycle would give a noncentral
vertex two distinct neighbours, although its only neighbour is the centre.
-/
theorem star_tree {V : Type*} {G : SimpleGraph V} :
    Lax68.Stars.IsStar G → Lax68.Trees.IsTree G := by
  classical
  rintro ⟨centre, universal, edges⟩
  have reach : ∀ v, G.Reachable centre v := by
    intro v
    by_cases h : centre = v
    · subst v; exact .rfl
    · exact (universal h).reachable
  let : Nonempty V := ⟨centre⟩
  refine ⟨⟨fun u v => (reach u).symm.trans (reach v)⟩, ?_⟩
  have noCycle : ∀ v, v ≠ centre → ∀ p : G.Walk v v, ¬p.IsCycle := by
    intro v hv p hp
    have hs := (edges (p.adj_snd hp.not_nil)).resolve_left hv
    have ht := (edges (p.adj_penultimate hp.not_nil)).resolve_right hv
    exact hp.snd_ne_penultimate (hs.trans ht.symm)
  intro v p hp
  by_cases hv : v = centre
  · subst v
    have hs : p.snd ≠ centre := (p.adj_snd hp.not_nil).ne.symm
    exact noCycle p.snd hs (p.rotate p.snd (p.getVert_mem_support 1))
      (hp.rotate _)
  · exact noCycle v hv p hp

/--
---
conclusion: Lax68.OuterplanarPlanar.outerplanar_planar
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
conclusion: Lax68.MaximalOuterplanarOuterplanar.maximalOuterplanar_outerplanar
---
Maximal outerplanarity includes outerplanarity.
-/
theorem maximalOuterplanar_outerplanar {V : Type*} {G : SimpleGraph V} :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h => h.1

/--
---
conclusion: Lax68.MaximalOuterplanarPlanar.maximalOuterplanar_planar
---
Every maximal outerplanar graph is planar.
-/
theorem maximalOuterplanar_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.OuterplanarPlanar.outerplanar_planar
      (maximalOuterplanar_outerplanar h)

/--
---
conclusion: Lax68.TriangleOuterplanar.triangle_outerplanar
---
Every triangle is outerplanar.
-/
theorem triangle_outerplanar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Triangles.IsTriangle G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h =>
    Lax68.MaximalOuterplanarOuterplanar.maximalOuterplanar_outerplanar
      (Lax68.TriangleMaximalOuterplanar.triangle_maximalOuterplanar h)

/--
---
conclusion: Lax68.TrianglePlanar.triangle_planar
---
Every triangle is planar.
-/
theorem triangle_planar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Triangles.IsTriangle G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.OuterplanarPlanar.outerplanar_planar
      (triangle_outerplanar h)

/--
---
conclusion: Lax68.StarOuterplanar.star_outerplanar
---
Every star is outerplanar.
-/
theorem star_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Stars.IsStar G →
    Lax68.Outerplanar.IsOuterplanar G :=
  fun h =>
    Lax68.TreeOuterplanar.tree_outerplanar
      (star_tree h)

/--
---
conclusion: Lax68.StarPlanar.star_planar
---
Every star is planar.
-/
theorem star_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Stars.IsStar G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.OuterplanarPlanar.outerplanar_planar
      (star_outerplanar h)

/--
---
conclusion: Lax68.LadderGrid.ladder_grid
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
conclusion: Lax68.LadderPlanar.ladder_planar
---
Every ladder is planar.
-/
theorem ladder_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.Ladders.IsLadder G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.GridPlanar.grid_planar
      (ladder_grid h)

/--
---
conclusion: Lax68.HalinPlanar.halin_planar
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
conclusion: Lax68.WheelPlanar.wheel_planar
---
Every wheel is planar.
-/
theorem wheel_planar
    {V : Type*} {G : SimpleGraph V} :
    Lax68.Wheels.IsWheel G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.HalinPlanar.halin_planar
      (Lax68.WheelHalin.wheel_halin h)

/--
---
conclusion: Lax68.TreePlanar.tree_planar
---
Every tree is planar.
-/
theorem tree_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Trees.IsTree G →
    Lax68.Planar.IsPlanar G :=
  fun h =>
    Lax68.OuterplanarPlanar.outerplanar_planar
      (Lax68.TreeOuterplanar.tree_outerplanar h)

/--
---
conclusion: Lax68.PathOuterplanar.path_outerplanar
---
Every path is outerplanar.
-/
theorem path_outerplanar {V : Type*} {G : SimpleGraph V} :
    Lax68.Paths.IsPath G →
    Lax68.Outerplanar.IsOuterplanar G := by
  intro h
  have ht := path_tree h
  obtain ⟨n, _, ⟨e⟩⟩ := h
  let : Finite V := Finite.of_injective e e.injective
  exact Lax68.TreeOuterplanar.tree_outerplanar ht

/--
---
conclusion: Lax68.PathPlanar.path_planar
---
A path is a tree, and every finite tree is planar. Finiteness follows from
the defining isomorphism to a standard finite path graph.
-/
theorem path_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.Paths.IsPath G →
    Lax68.Planar.IsPlanar G := by
  intro h
  have ht := Lax68.PathTree.path_tree h
  obtain ⟨n, _, ⟨e⟩⟩ := h
  let : Finite V := Finite.of_injective e e.injective
  exact Lax68.TreePlanar.tree_planar ht

/--
---
conclusion: Lax68.TriangulationPlanar.triangulationOf_planar
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
