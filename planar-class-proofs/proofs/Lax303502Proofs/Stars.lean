import Lax303502Proofs.Circle
import Lax68.StarOuterplanar

set_option autoImplicit false

namespace Lax303502Proofs

/--
---
conclusion: Lax68.StarOuterplanar.star_outerplanar
---
Every finite star has a straight-line drawing with its vertices on a circle.

# Proof strategy

Choose distinct real parameters for the vertices and use the rational
parametrization of the unit circle. A tangent to the circle at any vertex
strictly separates that vertex from every chord with different endpoints.
All edges of the star contain its centre, so there are no vertex-disjoint
edges whose segments could cross. The construction includes the one-vertex
star.

# Attribution

Direct elementary circle construction. Diestel, *Graph Theory*, sixth edition,
Chapter 4, supplies the plane-drawing framework and the outerplanarity
definition in Exercise 23, but does not give this explicit parametrization.
The coordinate proof here is supplied in full and uses no planarity theorem.
-/
theorem star_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V} :
    Lax68.Stars.IsStar G → Lax68.Outerplanar.IsOuterplanar G := by
  classical
  intro ⟨centre, _, hedge⟩
  let := Fintype.ofFinite V
  let f : V → ℝ := fun v => ((Fintype.equivFin V v).val : ℝ)
  have hf : Function.Injective f := by
    intro u v h
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    dsimp [f] at h
    exact_mod_cast h
  let p : V → ℝ × ℝ := fun v => circlePoint (f v)
  have hp : Function.Injective p := circlePoint_injective.comp hf
  refine ⟨{
    point := p
    injective := hp
    noVertexOnEdge := ?_
    disjointEdges := ?_
    radius := 1
    radius_pos := by norm_num
    onBoundary := ?_
  }⟩
  · intro a b c _ hca hcb
    exact circle_not_mem_segment (circlePoint_onCircle _) (circlePoint_onCircle _)
      (circlePoint_onCircle _) (hp.ne hca) (hp.ne hcb)
  · intro a b c d hab hcd hd
    have hc₁ : centre ∈ ({a, b} : Set V) := by
      rcases hedge hab with h | h <;> simp [h]
    have hc₂ : centre ∈ ({c, d} : Set V) := by
      rcases hedge hcd with h | h <;> simp [h]
    exact (Set.disjoint_left.mp hd hc₁ hc₂).elim
  · intro v
    simpa using circlePoint_onCircle (f v)

end Lax303502Proofs
