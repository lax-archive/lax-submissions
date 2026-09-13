import Lax17Proofs.Source.ChekuriChuzhoySection5HindReduction
import Lax17Proofs.Source.MaderTheorem

namespace Lax17Proofs

universe u v w

/-!
# Edge doubling for the Section 5 terminal skeleton

Chekuri--Chuzhoy double every edge after the Hind--Oellermann reduction.  The
named-edge representation makes the operation literal: an edge copy is paired
with a Boolean tag.  This module proves the exact cut and degree formulas and
the resulting `2 * k` terminal edge-connectivity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Replace every named edge copy by two parallel copies. -/
def doubleEdges (H : FiniteEdgeIndexedGraph W) : FiniteEdgeIndexedGraph W where
  Edge := H.Edge × Bool
  left e := H.left e.1
  right e := H.right e.1
  end_ne e := H.end_ne e.1

@[simp] theorem doubleEdges_left (H : FiniteEdgeIndexedGraph W)
    (e : H.Edge × Bool) : H.doubleEdges.left e = H.left e.1 := rfl

@[simp] theorem doubleEdges_right (H : FiniteEdgeIndexedGraph W)
    (e : H.Edge × Bool) : H.doubleEdges.right e = H.right e.1 := rfl

@[simp] theorem doubleEdges_crosses (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) (e : H.Edge × Bool) :
    H.doubleEdges.Crosses X e ↔ H.Crosses X e.1 := by
  rfl

/-- The doubled boundary is the product of the old boundary with `Bool`. -/
noncomputable def doubleEdgesBoundaryEquiv (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) :
    H.doubleEdges.boundary X ≃ (H.boundary X ×ˢ (Finset.univ : Finset Bool)) :=
  { toFun := fun e => ⟨(e.1.1, e.1.2), by
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact (H.mem_boundary X e.1.1).2
        ((H.doubleEdges.mem_boundary X e.1).1 e.2)⟩
    invFun := fun e => ⟨(e.1.1, e.1.2), by
      apply (H.doubleEdges.mem_boundary X _).2
      exact (H.mem_boundary X e.1.1).1 (Finset.mem_product.mp e.2).1⟩
    left_inv := by intro e; exact Subtype.ext (Prod.ext rfl rfl)
    right_inv := by intro e; exact Subtype.ext (Prod.ext rfl rfl) }

theorem doubleEdges_boundary_card (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) :
    (H.doubleEdges.boundary X).card = 2 * (H.boundary X).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (H.doubleEdgesBoundaryEquiv X),
    Fintype.card_coe, Finset.card_product]
  simp [Nat.mul_comm]

/-- The doubled incidence set is the product of the old incidence set with
`Bool`. -/
noncomputable def doubleEdgesIncidentEquiv (H : FiniteEdgeIndexedGraph W)
    (w : W) :
    H.doubleEdges.incidentEdges w ≃
      (H.incidentEdges w ×ˢ (Finset.univ : Finset Bool)) :=
  { toFun := fun e => ⟨(e.1.1, e.1.2), by
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact (H.mem_incidentEdges w e.1.1).2
        ((H.doubleEdges.mem_incidentEdges w e.1).1 e.2)⟩
    invFun := fun e => ⟨(e.1.1, e.1.2), by
      apply (H.doubleEdges.mem_incidentEdges w _).2
      exact (H.mem_incidentEdges w e.1.1).1 (Finset.mem_product.mp e.2).1⟩
    left_inv := by intro e; exact Subtype.ext (Prod.ext rfl rfl)
    right_inv := by intro e; exact Subtype.ext (Prod.ext rfl rfl) }

theorem doubleEdges_degree (H : FiniteEdgeIndexedGraph W) (w : W) :
    H.doubleEdges.degree w = 2 * H.degree w := by
  unfold degree
  rw [← Fintype.card_coe, Fintype.card_congr (H.doubleEdgesIncidentEquiv w),
    Fintype.card_coe, Finset.card_product]
  simp [Nat.mul_comm]

theorem doubleEdges_degree_even (H : FiniteEdgeIndexedGraph W) (w : W) :
    Even (H.doubleEdges.degree w) := by
  rw [H.doubleEdges_degree w]
  exact even_two_mul _

/-- Element connectivity in `H` lower-bounds every terminal-separating edge
cut; doubling therefore gives the source's `2 * k` terminal edge threshold. -/
theorem TerminalElementConnectedAtLeast.doubleEdges_pairwise
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k)
    {a b : W} (ha : a ∈ terminals) (hb : b ∈ terminals) (hab : a ≠ b) :
    H.doubleEdges.PairwiseEdgeConnectedAtLeast a b (2 * k) := by
  intro X haX hbX
  let C : TerminalElementCut H terminals a b :=
    { removedVertices := ∅
      removedVertices_nonterminal := by simp
      removedEdges := H.boundary X
      side := X
      source_mem := haX
      target_not_mem := hbX
      side_disjoint_removed := by simp
      crossing_removed := by
        intro e _ _ he
        exact (H.mem_boundary X e).2 he }
  have hk : k ≤ (H.boundary X).card := by
    have := h ha hb hab C
    simpa [C, TerminalElementCut.order] using this
  rw [H.doubleEdges_boundary_card X]
  omega

/-- Pairwise terminal edge connectivity after doubling. -/
theorem TerminalElementConnectedAtLeast.doubleEdges_terminals
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k) :
    ∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals → a ≠ b →
      H.doubleEdges.PairwiseEdgeConnectedAtLeast a b (2 * k) := by
  intro a ha b hb hab
  exact h.doubleEdges_pairwise ha hb hab

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
