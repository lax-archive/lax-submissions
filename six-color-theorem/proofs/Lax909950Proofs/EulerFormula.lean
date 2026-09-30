import Lax909950Proofs.Forest
import Lax909950Proofs.Winding

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula

/-- Euler's formula for drawings of trees. -/
theorem euler_formula_of_isTree {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.IsTree) (D : StraightLineDrawing G) :
    (Nat.card V : ℕ∞) + (faces D).encard = G.edgeSet.encard + 2 := by
  classical
  have := Fintype.ofFinite V
  have hcard := hG.card_edgeFinset
  rw [encard_faces_of_isAcyclic D hG.isAcyclic, Nat.card_eq_fintype_card, ← hcard,
    Set.encard_eq_coe_toFinset_card, Set.toFinset_card, ← SimpleGraph.edgeFinset_card]
  push_cast
  ring

theorem euler_formula_aux {V : Type*} [Finite V] :
    ∀ (n : ℕ) {G : SimpleGraph V}, G.edgeSet.ncard = n → G.Connected →
      ∀ D : StraightLineDrawing G,
        (Nat.card V : ℕ∞) + (faces D).encard = G.edgeSet.encard + 2 := by
  intro n
  induction n with
  | zero =>
    intro G hn hG D
    refine euler_formula_of_isTree ⟨hG, ?_⟩ D
    have : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 hn
    intro v c hc
    cases c with
    | nil => exact hc.not_nil SimpleGraph.Walk.Nil.nil
    | cons h _ =>
      have : s(v, _) ∈ G.edgeSet := h
      simp_all
  | succ n ih =>
    intro G hn hG D
    by_cases hac : G.IsAcyclic
    · exact euler_formula_of_isTree ⟨hG, hac⟩ D
    obtain ⟨a, b, hab, hbr⟩ : ∃ a b, G.Adj a b ∧ ¬ G.IsBridge s(a, b) := by
      by_contra! h
      exact hac (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.2 h)
    have hG' := hG.connected_delete_edge_of_not_isBridge hbr
    have hE : (G.deleteEdges {s(a, b)}).edgeSet = G.edgeSet \ {s(a, b)} :=
      SimpleGraph.edgeSet_deleteEdges _
    have hmem : s(a, b) ∈ G.edgeSet := hab
    have hn' : (G.deleteEdges {s(a, b)}).edgeSet.ncard = n := by
      rw [hE, Set.ncard_sdiff_singleton_of_mem hmem]; omega
    have hrec := ih hn' hG' (restrictDrawing D (G.deleteEdges_le {s(a, b)}))
    have hne := edgeFace_ne_of_reachable D hab (SimpleGraph.isBridge_iff.not_left.1 hbr)
    rw [encard_faces_deleteEdge_of_ne D hab hne]
    have hEe : G.edgeSet.encard = (G.deleteEdges {s(a, b)}).edgeSet.encard + 1 := by
      rw [hE, Set.encard_sdiff_singleton_add_one hmem]
    rw [hEe, ← add_assoc, hrec]
    ring

/--
---
conclusion: Lax909950.EulerFormula.euler_formula
---
By induction on the number of edges. A tree has one face. Otherwise some edge lies
on a cycle; its two sides lie in different faces, and deleting it merges them.
-/
theorem euler_formula {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.Connected) (D : StraightLineDrawing G) :
    (Nat.card V : ℕ∞) + (faces D).encard = G.edgeSet.encard + 2 :=
  euler_formula_aux _ rfl hG D

end Lax909950Proofs
