import Lax303502Proofs.EdgeContraction

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph

/-- Three-connectivity, stated by deletion of at most two vertices. -/
def ThreeConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  4 ≤ Nat.card V ∧ ThreeRobust G

theorem threeRobust_preconnected {V : Type*} {G : SimpleGraph V}
    (h : ThreeRobust G) : G.Preconnected := by
  have hp := h ∅ (by simp)
  intro x y
  obtain ⟨p⟩ := hp ⟨x,by simp⟩ ⟨y,by simp⟩
  exact ⟨p.map (Embedding.induce _).toHom⟩

theorem threeConnected_has_edge {V : Type*} [Finite V] {G : SimpleGraph V}
    (h : ThreeConnected G) : ∃ x y, G.Adj x y := by
  classical
  let := Fintype.ofFinite V
  have hc : 1 < Fintype.card V := by
    have hh := h.1
    rw [Nat.card_eq_fintype_card] at hh
    omega
  have := Fintype.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  obtain ⟨y,hxy⟩ := (threeRobust_preconnected h.2).exists_adj_of_nontrivial x
  exact ⟨x,y,hxy⟩

/-- Contracting an edge deletes exactly one vertex. -/
theorem card_contract {V : Type*} [Finite V] (y : V) :
    Nat.card {v : V // v ≠ y} + 1 = Nat.card V := by
  classical
  let := Fintype.ofFinite V
  have hh := Fintype.card_subtype_compl (fun v : V => v = y)
  simp only [Fintype.card_subtype_eq] at hh
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  simp only [Nat.card_eq_fintype_card]
  rw [hh]
  omega

/-- Diestel, Lemma 3.2.4, now with the concrete contracted graph. -/
theorem exists_threeConnected_contraction {V : Type*} [Finite V] [DecidableEq V]
    {G : SimpleGraph V} (h : ThreeConnected G) (hcard : 5 ≤ Nat.card V) :
    ∃ (x y : V) (hxy : G.Adj x y), ThreeConnected (edgeContract G hxy.ne) ∧
      Nat.card {v : V // v ≠ y} < Nat.card V := by
  obtain ⟨x,y,hxy,he⟩ := exists_robust_edge h.2 (threeConnected_has_edge h)
  have hc := card_contract y
  exact ⟨x,y,hxy,⟨by omega,threeRobust_edgeContract hxy.ne h.2 he⟩,by omega⟩

/-- The smaller graph required in the three-connected Kuratowski induction.
This uses no drawing or planarity characterization theorem. -/
theorem exists_kuratowskiFree_threeConnected_contraction {V : Type*} [Finite V] [DecidableEq V]
    {G : SimpleGraph V} (h : ThreeConnected G) (hcard : 5 ≤ Nat.card V)
    (hfree : Lax68.GraphTopologicalMinors.IsKuratowskiFree G) :
    ∃ (x y : V) (hxy : G.Adj x y), ThreeConnected (edgeContract G hxy.ne) ∧
      Lax68.GraphTopologicalMinors.IsKuratowskiFree (edgeContract G hxy.ne) ∧
      Nat.card {v : V // v ≠ y} + 1 = Nat.card V := by
  obtain ⟨x,y,hxy,hc,_⟩ := exists_threeConnected_contraction h hcard
  exact ⟨x,y,hxy,hc,kuratowskiFree_edgeContract hxy hfree,card_contract y⟩

end Lax303502Proofs
