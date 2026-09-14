import Lax68

set_option autoImplicit false

namespace Lax68Proofs

open SimpleGraph Lax68.GraphMinors

private theorem branch_eq_of_mem {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {u v : W} {x : V}
    (hu : x ∈ M.branchSet u) (hv : x ∈ M.branchSet v) : u = v := by
  by_contra h
  exact Set.disjoint_left.mp (M.disjoint h) hu hv

private theorem branch_reachable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {u : W} {x y : V}
    (hx : x ∈ M.branchSet u) (hy : y ∈ M.branchSet u) : G.Reachable x y :=
  ((M.connected u).preconnected ⟨x, hx⟩ ⟨y, hy⟩).map
    (Embedding.induce (M.branchSet u)).toHom

private theorem minor_reachable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {u v : W} (h : H.Reachable u v) :
    ∀ {x y : V}, x ∈ M.branchSet u → y ∈ M.branchSet v → G.Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact fun hx hy => branch_reachable M hx hy
  | cons hab p ih =>
    intro x y hx hy
    obtain ⟨a, ha, b, hb, hab'⟩ := M.adjacent hab
    exact (branch_reachable M hx ha).trans (hab'.reachable.trans (ih hb hy))

/-- Deleting an edge between two branch sets leaves a model after deleting
the corresponding edge of the minor. -/
private def delete_model_edge {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel H G) {u v : W} (huv : u ≠ v) {x y : V}
    (hx : x ∈ M.branchSet u) (hy : y ∈ M.branchSet v) :
    MinorModel (H.deleteEdges {s(u, v)}) (G.deleteEdges {s(x, y)}) where
  branchSet := M.branchSet
  connected := by
    intro w
    have heq : (G.deleteEdges {s(x, y)}).induce (M.branchSet w) =
        G.induce (M.branchSet w) := by
      ext a b
      simp only [induce_adj, deleteEdges_adj, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · intro hab
        refine ⟨hab, ?_⟩
        intro he
        rcases Sym2.eq_iff.mp he with ⟨hax, hby⟩ | ⟨hay, hbx⟩
        · have hw_u := branch_eq_of_mem M (hax ▸ a.property) hx
          have hw_v := branch_eq_of_mem M (hby ▸ b.property) hy
          exact huv (hw_u.symm.trans hw_v)
        · have hw_v := branch_eq_of_mem M (hay ▸ a.property) hy
          have hw_u := branch_eq_of_mem M (hbx ▸ b.property) hx
          exact huv (hw_u.symm.trans hw_v)
    rw [heq]
    exact M.connected w
  disjoint := M.disjoint
  adjacent := by
    intro a b hab
    rw [deleteEdges_adj] at hab
    obtain ⟨hab, hne⟩ := hab
    obtain ⟨r, hr, t, ht, hrt⟩ := M.adjacent hab
    refine ⟨r, hr, t, ht, ?_⟩
    rw [deleteEdges_adj]
    refine ⟨hrt, ?_⟩
    intro he
    have he' : s(r, t) = s(x, y) := Set.mem_singleton_iff.mp he
    apply hne
    apply Set.mem_singleton_iff.mpr
    rcases Sym2.eq_iff.mp he' with ⟨hrx, hty⟩ | ⟨hry, htx⟩
    · have ha := branch_eq_of_mem M (hrx ▸ hr) hx
      have hb := branch_eq_of_mem M (hty ▸ ht) hy
      simp [ha, hb]
    · have ha := branch_eq_of_mem M (hry ▸ hr) hy
      have hb := branch_eq_of_mem M (htx ▸ ht) hx
      simp [ha, hb, Sym2.eq_swap]

/--
---
conclusion: Lax68.AcyclicMinors.acyclic_minor
---
Every edge of an acyclic graph is a bridge. If an edge of the minor had an
alternative route between its endpoints, that route would lift through the
connected branch sets after deleting a corresponding edge of the original
graph. This contradicts that edge being a bridge.
-/
theorem acyclic_minor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsAcyclic) (hminor : IsMinor H G) : H.IsAcyclic := by
  obtain ⟨M⟩ := hminor
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent huv
  have bridge := isAcyclic_iff_forall_adj_isBridge.mp hG hxy
  rw [isBridge_iff] at bridge ⊢
  intro hpath
  exact bridge (minor_reachable (delete_model_edge M huv.ne hx hy) hpath hx hy)

private theorem k4_not_acyclic : ¬K4.IsAcyclic := by
  intro h
  have bridge := isAcyclic_iff_forall_adj_isBridge.mp h (by decide : K4.Adj 0 1)
  apply (isBridge_iff.mp bridge)
  exact ⟨Walk.cons (v := 2) (by decide) (Walk.cons (by decide) Walk.nil)⟩

private theorem k23_not_acyclic : ¬K23.IsAcyclic := by
  intro h
  have bridge := isAcyclic_iff_forall_adj_isBridge.mp h
    (by simp [K23] : K23.Adj (Sum.inl 0) (Sum.inr 0))
  apply (isBridge_iff.mp bridge)
  exact ⟨Walk.cons (v := Sum.inr 1) (by simp [deleteEdges_adj, K23])
    (Walk.cons (v := Sum.inl 1) (by simp [deleteEdges_adj, K23])
      (Walk.cons (by simp [deleteEdges_adj, K23]) Walk.nil))⟩

/--
---
conclusion: Lax68.TreeOuterplanar.tree_outerplanar
---
A tree is acyclic, and so are all its minors. The triangle in `K₄` and the
four-cycle in `K₂,₃` therefore exclude both as minors. Apply the excluded-minor
characterization of outerplanarity, which remains open in this submission.
-/
theorem tree_outerplanar {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : Lax68.Trees.IsTree G) : Lax68.Outerplanar.IsOuterplanar G := by
  apply (Lax68.OuterplanarExcludedMinors.outerplanar_iff_excludedMinors
    (G := G) inferInstance).mpr
  exact ⟨fun h => k4_not_acyclic (Lax68.AcyclicMinors.acyclic_minor hG.isAcyclic h),
    fun h => k23_not_acyclic (Lax68.AcyclicMinors.acyclic_minor hG.isAcyclic h)⟩

end Lax68Proofs
