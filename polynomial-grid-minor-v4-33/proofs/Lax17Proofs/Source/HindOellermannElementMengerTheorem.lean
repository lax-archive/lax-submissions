import Lax17Proofs.Source.HindOellermannElementMenger
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# The exact element-Menger producer

This file translates a small separator in the capacity-expanded incidence
graph back to a terminal element cut.  The sharp finite vertex-Menger theorem
then rules out that separator under terminal element connectivity and yields
an exact-size path packing.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]

namespace ElementMengerGraph

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}

/-- Nonterminal vertices whose unique capacity-one nodes lie in `X`. -/
noncomputable def separatorRemovedVertices
    (X : Finset (ElementMengerNode H terminals k)) : Finset W := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ hv : v ∉ terminals,
      (.nonterminal ⟨v, hv⟩ : ElementMengerNode H terminals k) ∈ X

/-- Named edges whose capacity-one edge nodes lie in `X`. -/
noncomputable def separatorRemovedEdges
    (X : Finset (ElementMengerNode H terminals k)) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (.edge e : ElementMengerNode H terminals k) ∈ X

@[simp] theorem mem_separatorRemovedVertices_iff
    (X : Finset (ElementMengerNode H terminals k)) (v : W) :
    v ∈ separatorRemovedVertices X ↔
      ∃ hv : v ∉ terminals,
        (.nonterminal ⟨v, hv⟩ : ElementMengerNode H terminals k) ∈ X := by
  classical
  simp [separatorRemovedVertices]

omit [Fintype W] in
@[simp] theorem mem_separatorRemovedEdges_iff
    (X : Finset (ElementMengerNode H terminals k)) (e : H.Edge) :
    e ∈ separatorRemovedEdges X ↔
      (.edge e : ElementMengerNode H terminals k) ∈ X := by
  classical
  simp [separatorRemovedEdges]

/-- Fewer than `k` deleted expanded vertices leave a surviving copy of every
terminal. -/
theorem exists_terminal_copy_not_mem
    (X : Finset (ElementMengerNode H terminals k)) (hXcard : X.card < k)
    (v : W) (hv : v ∈ terminals) :
    ∃ i : Fin k,
      (.terminal ⟨v, hv⟩ i : ElementMengerNode H terminals k) ∉ X := by
  classical
  by_contra h
  push Not at h
  have hsub : terminalCopies (H := H) (terminals := terminals) (k := k) v ⊆ X := by
    intro x hx
    rcases (mem_terminalCopies_iff v x).mp hx with ⟨_hv, i, rfl⟩
    exact h i
  have hcopiesCard :
      (terminalCopies (H := H) (terminals := terminals) (k := k) v).card = k :=
    terminalCopies_card v hv
  have hkX : k ≤ X.card := by
    calc
      k = (terminalCopies (H := H) (terminals := terminals) (k := k) v).card :=
        hcopiesCard.symm
      _ ≤ X.card := Finset.card_le_card hsub
  omega

/-- Reachability from one surviving source copy, retaining survival of the
target node as part of the predicate. -/
private def NodeReachable
    (X : Finset (ElementMengerNode H terminals k)) (a : W)
    (x : ElementMengerNode H terminals k) : Prop :=
  ∃ (ha : a ∈ terminals) (i : Fin k),
    (.terminal ⟨a, ha⟩ i : ElementMengerNode H terminals k) ∉ X ∧
    x ∉ X ∧
    (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Reachable
      (.terminal ⟨a, ha⟩ i) x

private theorem nodeReachable_extend
    {X : Finset (ElementMengerNode H terminals k)} {a : W}
    {x y : ElementMengerNode H terminals k}
    (hx : NodeReachable X a x) (hy : y ∉ X)
    (hxy : (elementMengerGraph H terminals k).Adj x y) :
    NodeReachable X a y := by
  rcases hx with ⟨ha, i, hsource, hxX, hreach⟩
  exact ⟨ha, i, hsource, hy,
    hreach.trans (show
      (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Adj x y
      from ⟨hxy, hxX, hy⟩).reachable⟩

private theorem edgeNodeReachable_of_left_mem
    {X : Finset (ElementMengerNode H terminals k)} {a : W} (e : H.Edge)
    (he : (.edge e : ElementMengerNode H terminals k) ∉ X)
    (hleft : H.left e ∈ reachableSide X a) :
    NodeReachable X a (.edge e) := by
  classical
  by_cases hlt : H.left e ∈ terminals
  · rw [mem_reachableSide_terminal X a (H.left e) hlt] at hleft
    rcases hleft with ⟨ha, i, _hlt, j, hsource, hcopy, hreach⟩
    exact nodeReachable_extend
      ⟨ha, i, hsource, hcopy, hreach⟩ he
      ((terminal_left_adj (k := k) e hlt j).symm)
  · rw [mem_reachableSide_nonterminal X a (H.left e) hlt] at hleft
    rcases hleft with ⟨ha, i, hsource, hnode, hreach⟩
    exact nodeReachable_extend
      ⟨ha, i, hsource, hnode, hreach⟩ he
      ((nonterminal_left_adj (k := k) e hlt).symm)

private theorem edgeNodeReachable_of_right_mem
    {X : Finset (ElementMengerNode H terminals k)} {a : W} (e : H.Edge)
    (he : (.edge e : ElementMengerNode H terminals k) ∉ X)
    (hright : H.right e ∈ reachableSide X a) :
    NodeReachable X a (.edge e) := by
  classical
  by_cases hrt : H.right e ∈ terminals
  · rw [mem_reachableSide_terminal X a (H.right e) hrt] at hright
    rcases hright with ⟨ha, i, _hrt, j, hsource, hcopy, hreach⟩
    exact nodeReachable_extend
      ⟨ha, i, hsource, hcopy, hreach⟩ he
      ((terminal_right_adj (k := k) e hrt j).symm)
  · rw [mem_reachableSide_nonterminal X a (H.right e) hrt] at hright
    rcases hright with ⟨ha, i, hsource, hnode, hreach⟩
    exact nodeReachable_extend
      ⟨ha, i, hsource, hnode, hreach⟩ he
      ((nonterminal_right_adj (k := k) e hrt).symm)

private theorem right_mem_of_edgeNodeReachable
    {X : Finset (ElementMengerNode H terminals k)} {a : W} (e : H.Edge)
    (hXcard : X.card < k) (hright : H.right e ∉ separatorRemovedVertices X)
    (heReach : NodeReachable X a (.edge e)) :
    H.right e ∈ reachableSide X a := by
  classical
  by_cases hrt : H.right e ∈ terminals
  · rcases exists_terminal_copy_not_mem X hXcard (H.right e) hrt with ⟨j, hj⟩
    have hnode := nodeReachable_extend heReach hj
      (terminal_right_adj (k := k) e hrt j)
    rw [mem_reachableSide_terminal X a (H.right e) hrt]
    rcases hnode with ⟨ha, i, hsource, _hj, hreach⟩
    exact ⟨ha, i, hrt, j, hsource, hj, hreach⟩
  · have hnodeX :
        (.nonterminal ⟨H.right e, hrt⟩ : ElementMengerNode H terminals k) ∉ X := by
      intro hx
      exact hright ((mem_separatorRemovedVertices_iff X (H.right e)).2 ⟨hrt, hx⟩)
    have hnode := nodeReachable_extend heReach hnodeX
      (nonterminal_right_adj (k := k) e hrt)
    rw [mem_reachableSide_nonterminal X a (H.right e) hrt]
    rcases hnode with ⟨ha, i, hsource, _hnodeX, hreach⟩
    exact ⟨ha, i, hsource, hnodeX, hreach⟩

private theorem left_mem_of_edgeNodeReachable
    {X : Finset (ElementMengerNode H terminals k)} {a : W} (e : H.Edge)
    (hXcard : X.card < k) (hleft : H.left e ∉ separatorRemovedVertices X)
    (heReach : NodeReachable X a (.edge e)) :
    H.left e ∈ reachableSide X a := by
  classical
  by_cases hlt : H.left e ∈ terminals
  · rcases exists_terminal_copy_not_mem X hXcard (H.left e) hlt with ⟨j, hj⟩
    have hnode := nodeReachable_extend heReach hj
      (terminal_left_adj (k := k) e hlt j)
    rw [mem_reachableSide_terminal X a (H.left e) hlt]
    rcases hnode with ⟨ha, i, hsource, _hj, hreach⟩
    exact ⟨ha, i, hlt, j, hsource, hj, hreach⟩
  · have hnodeX :
        (.nonterminal ⟨H.left e, hlt⟩ : ElementMengerNode H terminals k) ∉ X := by
      intro hx
      exact hleft ((mem_separatorRemovedVertices_iff X (H.left e)).2 ⟨hlt, hx⟩)
    have hnode := nodeReachable_extend heReach hnodeX
      (nonterminal_left_adj (k := k) e hlt)
    rw [mem_reachableSide_nonterminal X a (H.left e) hlt]
    rcases hnode with ⟨ha, i, hsource, _hnodeX, hreach⟩
    exact ⟨ha, i, hsource, hnodeX, hreach⟩

private theorem walk_support_avoids
    {X : Finset (ElementMengerNode H terminals k)}
    {x y : ElementMengerNode H terminals k}
    (P : (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Walk x y)
    (hx : x ∉ X) : ∀ z ∈ P.support, z ∉ X := by
  induction P with
  | nil => simpa using hx
  | @cons x y z hxy P ih =>
      intro w hw
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hxy.2.1
      · exact ih hxy.2.2 w hw

private theorem terminal_not_mem_reachableSide_of_separator
    {X : Finset (ElementMengerNode H terminals k)} {a b : W}
    (hb : b ∈ terminals)
    (hsep : STSeparator (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b) X) :
    b ∉ reachableSide X a := by
  classical
  rw [mem_reachableSide_terminal X a b hb]
  rintro ⟨ha, i, hb', j, hsource, htarget, hreach⟩
  rcases hreach with ⟨Q⟩
  let Q' := Q.mapLe (avoidingGraph_le (H := H) (terminals := terminals) (k := k) X)
  let Qp := Q'.toPath
  let P : GraphPath (elementMengerGraph H terminals k) :=
    { source := .terminal ⟨a, ha⟩ i
      target := .terminal ⟨b, hb'⟩ j
      walk := (Qp : (elementMengerGraph H terminals k).Walk
        (.terminal ⟨a, ha⟩ i) (.terminal ⟨b, hb'⟩ j))
      isPath := Qp.property }
  rcases hsep P (Or.inl
      ⟨terminal_mem_terminalCopies a ha i,
        terminal_mem_terminalCopies b hb' j⟩) with ⟨z, hzP, hzX⟩
  have hzQp : z ∈ (Qp : (elementMengerGraph H terminals k).Walk
      (.terminal ⟨a, ha⟩ i) (.terminal ⟨b, hb'⟩ j)).support := by
    simpa [P, GraphPath.vertexSet] using hzP
  have hzQ' : z ∈ Q'.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset Q' hzQp
  have hzQ : z ∈ Q.support := by
    simpa [Q', _root_.SimpleGraph.Walk.support_mapLe_eq_support] using hzQ'
  exact (walk_support_avoids Q hsource z hzQ) hzX

/-- Translate a separator of cardinality below terminal capacity back to an
element cut in the original edge-indexed graph. -/
noncomputable def elementCutOfSeparator
    {a b : W} (ha : a ∈ terminals) (hb : b ∈ terminals)
    (X : Finset (ElementMengerNode H terminals k)) (hXcard : X.card < k)
    (hsep : STSeparator (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b) X) :
    TerminalElementCut H terminals a b where
  removedVertices := separatorRemovedVertices X
  removedVertices_nonterminal := by
    rw [Finset.disjoint_left]
    intro v hv hvt
    rcases (mem_separatorRemovedVertices_iff X v).mp hv with ⟨hvnt, _⟩
    exact hvnt hvt
  removedEdges := separatorRemovedEdges X
  side := reachableSide X a
  source_mem := by
    rw [mem_reachableSide_terminal X a a ha]
    rcases exists_terminal_copy_not_mem X hXcard a ha with ⟨i, hi⟩
    exact ⟨ha, i, ha, i, hi, hi, .refl _⟩
  target_not_mem := terminal_not_mem_reachableSide_of_separator hb hsep
  side_disjoint_removed := by
    rw [Finset.disjoint_left]
    intro v hvSide hvRemoved
    rcases (mem_separatorRemovedVertices_iff X v).mp hvRemoved with ⟨hvnt, hvX⟩
    rw [mem_reachableSide_nonterminal X a v hvnt] at hvSide
    rcases hvSide with ⟨_ha, _i, _hsource, hvNotX, _hreach⟩
    exact hvNotX hvX
  crossing_removed := by
    intro e hleft hright hcross
    by_contra heRemoved
    have heX : (.edge e : ElementMengerNode H terminals k) ∉ X := by
      simpa using heRemoved
    rcases hcross with ⟨hleftSide, hrightNotSide⟩ |
        ⟨hrightSide, hleftNotSide⟩
    · exact hrightNotSide
        (right_mem_of_edgeNodeReachable e hXcard hright
          (edgeNodeReachable_of_left_mem e heX hleftSide))
    · exact hleftNotSide
        (left_mem_of_edgeNodeReachable e hXcard hleft
          (edgeNodeReachable_of_right_mem e heX hrightSide))

/-- The translated element cut uses no more elements than the expanded-graph
separator. -/
theorem elementCutOfSeparator_order_le
    {a b : W} (ha : a ∈ terminals) (hb : b ∈ terminals)
    (X : Finset (ElementMengerNode H terminals k)) (hXcard : X.card < k)
    (hsep : STSeparator (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b) X) :
    (elementCutOfSeparator ha hb X hXcard hsep).order ≤ X.card := by
  classical
  let fv : {v // v ∈ separatorRemovedVertices X} ↪
      ElementMengerNode H terminals k :=
    ⟨fun v => .nonterminal ⟨v.1, by
        rcases (mem_separatorRemovedVertices_iff X v.1).mp v.2 with ⟨hv, _⟩
        exact hv⟩,
      by
        intro v w hvw
        apply Subtype.ext
        have hvw' := congrArg (elementMengerNodeEquiv H terminals k) hvw
        simpa using hvw'⟩
  let fe : {e // e ∈ separatorRemovedEdges X} ↪
      ElementMengerNode H terminals k :=
    ⟨fun e => .edge e.1, by
      intro e f hef
      apply Subtype.ext
      have hef' := congrArg (elementMengerNodeEquiv H terminals k) hef
      simpa using hef'⟩
  let Yv := Finset.univ.map fv
  let Ye := Finset.univ.map fe
  have hvSub : Yv ⊆ X := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨v, _hv, rfl⟩
    exact (mem_separatorRemovedVertices_iff X v.1).mp v.2 |>.choose_spec
  have heSub : Ye ⊆ X := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨e, _he, rfl⟩
    exact (mem_separatorRemovedEdges_iff X e.1).mp e.2
  have hdisj : Disjoint Yv Ye := by
    rw [Finset.disjoint_left]
    intro x hxv hxe
    rcases Finset.mem_map.mp hxv with ⟨v, _hv, rfl⟩
    rcases Finset.mem_map.mp hxe with ⟨e, _he, heq⟩
    have heq' := congrArg (elementMengerNodeEquiv H terminals k) heq
    simp at heq'
  have hYvcard : Yv.card = (separatorRemovedVertices X).card := by
    simp [Yv]
  have hYecard : Ye.card = (separatorRemovedEdges X).card := by
    simp [Ye]
  have hcard : (separatorRemovedVertices X).card +
      (separatorRemovedEdges X).card ≤ X.card := by
    calc
      (separatorRemovedVertices X).card +
          (separatorRemovedEdges X).card = Yv.card + Ye.card := by
            rw [hYvcard, hYecard]
      _ = (Yv ∪ Ye).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ X.card := Finset.card_le_card (Finset.union_subset hvSub heSub)
  simpa [elementCutOfSeparator, TerminalElementCut.order] using hcard

/-- Terminal element connectivity produces exactly `k` disjoint paths between
the `k` capacity copies of two distinct terminals. -/
theorem TerminalElementConnectedAtLeast.exists_elementMengerPathPacking
    (hconn : H.TerminalElementConnectedAtLeast terminals k)
    {a b : W} (ha : a ∈ terminals) (hb : b ∈ terminals) (hab : a ≠ b) :
    ∃ P : PathPacking (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b),
      P.card = k := by
  classical
  rcases Menger.finite_vertex_menger_sharp
      (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b) k with
    hpaths | ⟨X, hXcard, hsep⟩
  · exact HasAtLeastDisjointPaths.exists_exact hpaths
  · have hkOrder := hconn ha hb hab (elementCutOfSeparator ha hb X hXcard hsep)
    have hOrderX := elementCutOfSeparator_order_le ha hb X hXcard hsep
    omega

end ElementMengerGraph

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
