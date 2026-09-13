import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Tight deletion cuts in the Hind--Oellermann argument

These are the elementary cut calculations used after deletion of a named
nonterminal edge fails to preserve terminal element connectivity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {a b : W}

/-- Failure of the cut-form connectivity predicate supplies an explicit
ordered terminal pair and a cut below the claimed threshold. -/
theorem exists_terminalElementCut_order_lt_of_not_connectedAtLeast
    {k : Nat} (h : ¬ H.TerminalElementConnectedAtLeast terminals k) :
    ∃ a ∈ terminals, ∃ b ∈ terminals, a ≠ b ∧
      ∃ C : TerminalElementCut H terminals a b, C.order < k := by
  unfold TerminalElementConnectedAtLeast at h
  push Not at h
  exact h

namespace TerminalElementCut

/-- Change the distinguished terminal pair while retaining the same element
set and cut side. -/
def retarget (C : TerminalElementCut H terminals a b)
    {x y : W} (hx : x ∈ C.side) (hy : y ∉ C.side) :
    TerminalElementCut H terminals x y where
  removedVertices := C.removedVertices
  removedVertices_nonterminal := C.removedVertices_nonterminal
  removedEdges := C.removedEdges
  side := C.side
  source_mem := hx
  target_not_mem := hy
  side_disjoint_removed := C.side_disjoint_removed
  crossing_removed := C.crossing_removed

@[simp] theorem retarget_order (C : TerminalElementCut H terminals a b)
    {x y : W} (hx : x ∈ C.side) (hy : y ∉ C.side) :
    (C.retarget hx hy).order = C.order := rfl

omit [Fintype W] [DecidableEq W] in
/-- The deleted edge is not in the image of the surviving edge indices. -/
theorem deletedEdge_not_mem_survivingImage (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b) :
    e0 ∉ C.removedEdges.image Subtype.val := by
  classical
  intro he
  rcases Finset.mem_image.mp he with ⟨e, _heC, heq⟩
  exact e.2 heq

/-- Lifting a deletion cut adds exactly the deleted named edge. -/
theorem liftDelete_order_eq_add_one (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b) :
    (C.liftDelete H e0).order = C.order + 1 := by
  classical
  have himage : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr (by
      intro x _hx y _hy hxy
      exact Subtype.ext hxy)
  have hunion :
      (C.removedEdges.image Subtype.val ∪ {e0}).card =
        (C.removedEdges.image Subtype.val).card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_singleton_right]
      exact C.deletedEdge_not_mem_survivingImage e0
  simp only [TerminalElementCut.order, TerminalElementCut.liftDelete]
  rw [hunion, himage]
  omega

/-- Lift a deletion cut without adding the deleted edge when that edge cannot
be an available crossing edge of the cut. -/
noncomputable def liftDeleteWithoutDeletedEdge (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b)
    (hirrelevant : H.left e0 ∈ C.removedVertices ∨
      H.right e0 ∈ C.removedVertices ∨ ¬ H.Crosses C.side e0) :
    TerminalElementCut H terminals a b where
  removedVertices := C.removedVertices
  removedVertices_nonterminal := C.removedVertices_nonterminal
  removedEdges := C.removedEdges.image Subtype.val
  side := C.side
  source_mem := C.source_mem
  target_not_mem := C.target_not_mem
  side_disjoint_removed := C.side_disjoint_removed
  crossing_removed := by
    intro e hl hr hcross
    have he : e ≠ e0 := by
      intro heq
      subst e
      rcases hirrelevant with hleft | hright | hnotCross
      · exact hl hleft
      · exact hr hright
      · exact hnotCross hcross
    exact Finset.mem_image.mpr
      ⟨⟨e, he⟩, C.crossing_removed ⟨e, he⟩ hl hr hcross, rfl⟩

omit [Fintype W] [DecidableEq W] in
/-- Lifting without the deleted edge preserves the cut order exactly. -/
theorem liftDeleteWithoutDeletedEdge_order (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b)
    (hirrelevant : H.left e0 ∈ C.removedVertices ∨
      H.right e0 ∈ C.removedVertices ∨ ¬ H.Crosses C.side e0) :
    (C.liftDeleteWithoutDeletedEdge e0 hirrelevant).order = C.order := by
  classical
  have himage : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr (by
      intro x _hx y _hy hxy
      exact Subtype.ext hxy)
  simp [TerminalElementCut.order, liftDeleteWithoutDeletedEdge, himage]

end TerminalElementCut

/-- A deletion cut below the original connectivity threshold is crossed by
the deleted edge, and neither endpoint of that edge was removed. -/
theorem deletionCut_endpoint_not_removed_and_crosses
    {k : Nat} (hconn : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge) (ha : a ∈ terminals) (hb : b ∈ terminals) (hab : a ≠ b)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b)
    (hsmall : C.order < k) :
    H.left e0 ∉ C.removedVertices ∧
      H.right e0 ∉ C.removedVertices ∧ H.Crosses C.side e0 := by
  by_contra h
  push Not at h
  have hirrelevant : H.left e0 ∈ C.removedVertices ∨
      H.right e0 ∈ C.removedVertices ∨ ¬ H.Crosses C.side e0 := by
    tauto
  let C' := C.liftDeleteWithoutDeletedEdge e0 hirrelevant
  have hk := hconn ha hb hab C'
  have horder : C'.order = C.order :=
    C.liftDeleteWithoutDeletedEdge_order e0 hirrelevant
  omega

/-- Every deletion cut below `k` is tight: its order is exactly `k - 1`. -/
theorem deletionCut_order_eq_sub_one
    {k : Nat} (hconn : H.TerminalElementConnectedAtLeast terminals k)
    (e0 : H.Edge) (ha : a ∈ terminals) (hb : b ∈ terminals) (hab : a ≠ b)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b)
    (hsmall : C.order < k) : C.order = k - 1 := by
  have hk := hconn ha hb hab (C.liftDelete H e0)
  have horder := C.liftDelete_order_eq_add_one e0
  omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
