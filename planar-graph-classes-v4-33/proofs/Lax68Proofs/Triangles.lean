import Lax68
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Lax68Proofs

open SimpleGraph

/-- Three explicit points on the unit circle, one for each vertex of `K₃`. -/
private def trianglePoint (i : Fin 3) : Lax68.StraightLineDrawings.Point :=
  if i = 0 then (1, 0)
  else if i = 1 then (0, 1)
  else (-1, 0)

private theorem trianglePoint_injective : Function.Injective trianglePoint := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [trianglePoint]

private theorem trianglePoint_onCircle (i : Fin 3) :
    (trianglePoint i).1 ^ 2 + (trianglePoint i).2 ^ 2 = (1 : ℝ) ^ 2 := by
  fin_cases i <;> norm_num [trianglePoint]

/-- Among the three chosen points, the third never lies on the segment joining
the other two. -/
private theorem trianglePoint_not_mem_segment
    {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) :
    trianglePoint k ∉ segment ℝ (trianglePoint i) (trianglePoint j) := by
  rintro ⟨a, b, ha, hb, hab, hp⟩
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num [trianglePoint] at *
  all_goals linarith

private theorem finThree_not_four_distinct (a b c d : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

/-- Transport the explicit triangular drawing along a graph isomorphism. -/
private def triangleOuterplaneDrawing {V : Type*} {G : SimpleGraph V}
    (e : G ≃g SimpleGraph.completeGraph (Fin 3)) :
    Lax68.Outerplanar.OuterplaneDrawing G where
  point v := trianglePoint (e v)
  injective := trianglePoint_injective.comp e.injective
  noVertexOnEdge := by
    intro a b c _ hca hcb
    apply trianglePoint_not_mem_segment
    · exact fun h => hca (e.injective h)
    · exact fun h => hcb (e.injective h)
  disjointEdges := by
    intro a b c d hab hcd hd
    exfalso
    have hac : a ≠ c := by
      intro h
      exact Set.disjoint_left.1 hd (show a ∈ ({a, b} : Set _) by simp)
        (show a ∈ ({c, d} : Set _) by simp [h])
    have had : a ≠ d := by
      intro h
      exact Set.disjoint_left.1 hd (show a ∈ ({a, b} : Set _) by simp)
        (show a ∈ ({c, d} : Set _) by simp [h])
    have hbc : b ≠ c := by
      intro h
      exact Set.disjoint_left.1 hd (show b ∈ ({a, b} : Set _) by simp)
        (show b ∈ ({c, d} : Set _) by simp [h])
    have hbd : b ≠ d := by
      intro h
      exact Set.disjoint_left.1 hd (show b ∈ ({a, b} : Set _) by simp)
        (show b ∈ ({c, d} : Set _) by simp [h])
    exact finThree_not_four_distinct (e a) (e b) (e c) (e d)
      (e.injective.ne hab.ne) (e.injective.ne hac) (e.injective.ne had)
      (e.injective.ne hbc) (e.injective.ne hbd) (e.injective.ne hcd.ne)
  radius := 1
  radius_pos := by norm_num
  onBoundary v := trianglePoint_onCircle (e v)

/--
---
conclusion: Lax68.TriangleMaximalOuterplanar.triangle_maximalOuterplanar
---
A triangle is transported to three explicit points on the unit circle. The
three sides do not cross, so this is an outerplane drawing. Completeness makes
the graph maximal: no further edge can be added on the same vertices.
-/
theorem triangle_maximalOuterplanar {V : Type*} {G : SimpleGraph V}
    (hG : Lax68.Triangles.IsTriangle G) :
    Lax68.MaximalOuterplanar.IsMaximalOuterplanar G := by
  obtain ⟨e⟩ := hG
  have complete : G = ⊤ := by
    apply eq_top_iff_forall_ne_adj.mpr
    intro a b hab
    exact e.map_adj_iff.mp (e.injective.ne hab)
  refine ⟨?_, ?_⟩
  · exact ⟨triangleOuterplaneDrawing e⟩
  · intro H h
    simp [complete] at h

end Lax68Proofs
