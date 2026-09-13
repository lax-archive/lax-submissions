import Lax17Proofs.Source.ChekuriChuzhoySection5Contraction

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 element connectivity

This module gives the parallel-edge-sensitive connectivity language needed for
journal Theorem 5.13.  An element cut explicitly removes nonterminal vertices
and named edge copies.  It therefore does not pass through `SimpleGraph`, where
parallel copies would be collapsed.

The elementary deletion and contraction bounds proved here each lose at most
one element.  The stronger Hind--Oellermann alternative, saying that one of the
two operations preserves the full connectivity value, is deliberately not
assumed.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Named-edge walks and contraction provenance -/

/-- A named edge joins two vertices, in either endpoint orientation. -/
def Joins (H : FiniteEdgeIndexedGraph W) (e : H.Edge) (x y : W) : Prop :=
  (H.left e = x ∧ H.right e = y) ∨
    (H.right e = x ∧ H.left e = y)

theorem joins_comm (H : FiniteEdgeIndexedGraph W) (e : H.Edge) (x y : W) :
    H.Joins e x y ↔ H.Joins e y x := by
  simp only [Joins]
  tauto

/-- A finite walk retaining the identity of every traversed edge copy. -/
inductive NamedEdgeWalk (H : FiniteEdgeIndexedGraph W) : W -> W -> Type u
  | nil (x : W) : NamedEdgeWalk H x x
  | cons {x y z : W} (e : H.Edge) (head : H.Joins e x y)
      (tail : NamedEdgeWalk H y z) : NamedEdgeWalk H x z

namespace NamedEdgeWalk

variable {H : FiniteEdgeIndexedGraph W} {x y z : W}

/-- The named edge copies traversed by a walk, with multiplicity and order. -/
def edgeList {x y : W} : H.NamedEdgeWalk x y -> List H.Edge
  | .nil _ => []
  | .cons e _ tail => e :: tail.edgeList

/-- Concatenate two named-edge walks. -/
def append {x y z : W} :
    H.NamedEdgeWalk x y -> H.NamedEdgeWalk y z -> H.NamedEdgeWalk x z
  | .nil _, Q => Q
  | .cons e he P, Q => .cons e he (P.append Q)

@[simp] theorem edgeList_nil (x : W) :
    (NamedEdgeWalk.nil (H := H) x).edgeList = [] := rfl

@[simp] theorem edgeList_cons {a b c : W} (e : H.Edge) (he : H.Joins e a b)
    (P : H.NamedEdgeWalk b c) :
    (NamedEdgeWalk.cons e he P).edgeList = e :: P.edgeList := rfl

@[simp] theorem edgeList_append (P : H.NamedEdgeWalk x y)
    (Q : H.NamedEdgeWalk y z) :
    (P.append Q).edgeList = P.edgeList ++ Q.edgeList := by
  induction P with
  | nil => rfl
  | cons e he P ih => simp [append, ih]

end NamedEdgeWalk

/-- A walk inside one contraction fiber.  Its only possible edge is the edge
being contracted. -/
structure ContractFiberBridge (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (x y : W) where
  walk : H.NamedEdgeWalk x y
  only_contracted : ∀ e ∈ walk.edgeList, e = e0

/-- Equal projected vertices can be joined in the original graph using zero or
one copies of the contracted edge. -/
theorem exists_contractFiberBridge (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    {x y : W}
    (hxy : ContractVertex.projection (p := H.left e0) (q := H.right e0) x =
      ContractVertex.projection (p := H.left e0) (q := H.right e0) y) :
    Nonempty (ContractFiberBridge H e0 x y) := by
  classical
  by_cases h : x = y
  · subst y
    exact ⟨⟨.nil x, by simp⟩⟩
  rcases ContractVertex.eq_or_both_endpoints_of_projection_eq hxy with h' | hends
  · exact (h h').elim
  rcases hends.1 with hx | hx <;> rcases hends.2 with hy | hy
  · exact (h (hx.trans hy.symm)).elim
  · subst x
    subst y
    exact ⟨⟨.cons e0 (Or.inl ⟨rfl, rfl⟩) (.nil _), by simp⟩⟩
  · subst x
    subst y
    exact ⟨⟨.cons e0 (Or.inr ⟨rfl, rfl⟩) (.nil _), by simp⟩⟩
  · exact (h (hx.trans hy.symm)).elim

/-- Provenance for a contracted walk.  The lift traverses only origins of its
surviving edges and copies of the single contracted edge. -/
structure ContractWalkProvenance (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    {a b : ContractVertex W (H.left e0) (H.right e0)}
    (P : (H.contractEdge e0).NamedEdgeWalk a b) where
  sourceOrigin : W
  targetOrigin : W
  source_projects : ContractVertex.projection
    (p := H.left e0) (q := H.right e0) sourceOrigin = a
  target_projects : ContractVertex.projection
    (p := H.left e0) (q := H.right e0) targetOrigin = b
  lift : H.NamedEdgeWalk sourceOrigin targetOrigin
  edge_provenance : ∀ e ∈ lift.edgeList,
    e = e0 ∨ ∃ f ∈ P.edgeList, e = f.1

/-- Every named-edge walk after contraction has a lift with explicit original
edge provenance. -/
theorem exists_contractWalkProvenance (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    {a b : ContractVertex W (H.left e0) (H.right e0)}
    (P : (H.contractEdge e0).NamedEdgeWalk a b) :
    Nonempty (ContractWalkProvenance H e0 P) := by
  classical
  induction P with
  | nil a =>
      rcases ContractVertex.projection_surjective
          (W := W) (p := H.left e0) (q := H.right e0) a with ⟨x, hx⟩
      exact ⟨{
        sourceOrigin := x
        targetOrigin := x
        source_projects := hx
        target_projects := hx
        lift := .nil x
        edge_provenance := by simp }⟩
  | @cons a c b e he P ih =>
      rcases ih with ⟨D⟩
      rcases he with he | he
      · have hbridge : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.right e.1) =
            ContractVertex.projection
              (p := H.left e0) (q := H.right e0) D.sourceOrigin := by
          calc
            _ = c := by simpa using he.2
            _ = _ := D.source_projects.symm
        rcases exists_contractFiberBridge H e0 hbridge with ⟨B⟩
        exact ⟨{
          sourceOrigin := H.left e.1
          targetOrigin := D.targetOrigin
          source_projects := by simpa using he.1
          target_projects := D.target_projects
          lift := .cons e.1 (Or.inl ⟨rfl, rfl⟩) (B.walk.append D.lift)
          edge_provenance := by
            intro f hf
            simp only [NamedEdgeWalk.edgeList_cons, NamedEdgeWalk.edgeList_append,
              List.mem_cons, List.mem_append] at hf
            rcases hf with rfl | hf | hf
            · exact Or.inr ⟨e, by simp, rfl⟩
            · exact Or.inl (B.only_contracted f hf)
            · rcases D.edge_provenance f hf with hfe | ⟨g, hg, hfg⟩
              · exact Or.inl hfe
              · exact Or.inr ⟨g, by simp [hg], hfg⟩ }⟩
      · have hbridge : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.left e.1) =
            ContractVertex.projection
              (p := H.left e0) (q := H.right e0) D.sourceOrigin := by
          calc
            _ = c := by simpa using he.2
            _ = _ := D.source_projects.symm
        rcases exists_contractFiberBridge H e0 hbridge with ⟨B⟩
        exact ⟨{
          sourceOrigin := H.right e.1
          targetOrigin := D.targetOrigin
          source_projects := by simpa using he.1
          target_projects := D.target_projects
          lift := .cons e.1 (Or.inr ⟨rfl, rfl⟩) (B.walk.append D.lift)
          edge_provenance := by
            intro f hf
            simp only [NamedEdgeWalk.edgeList_cons, NamedEdgeWalk.edgeList_append,
              List.mem_cons, List.mem_append] at hf
            rcases hf with rfl | hf | hf
            · exact Or.inr ⟨e, by simp, rfl⟩
            · exact Or.inl (B.only_contracted f hf)
            · rcases D.edge_provenance f hf with hfe | ⟨g, hg, hfg⟩
              · exact Or.inl hfe
              · exact Or.inr ⟨g, by simp [hg], hfg⟩ }⟩

/-! ## Element cuts -/

/-- A terminal-separating element cut.  Removed vertices must be
nonterminals; removed named edges retain parallel-edge multiplicity. -/
structure TerminalElementCut (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (a b : W) where
  removedVertices : Finset W
  removedVertices_nonterminal : Disjoint removedVertices terminals
  removedEdges : Finset H.Edge
  side : Finset W
  source_mem : a ∈ side
  target_not_mem : b ∉ side
  side_disjoint_removed : Disjoint side removedVertices
  crossing_removed : ∀ e, H.left e ∉ removedVertices ->
    H.right e ∉ removedVertices -> H.Crosses side e -> e ∈ removedEdges

namespace TerminalElementCut

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {a b : W}

/-- Number of removed elements. -/
def order (C : TerminalElementCut H terminals a b) : Nat :=
  C.removedVertices.card + C.removedEdges.card

end TerminalElementCut

/-- Crossing copies that remain after deleting a vertex set. -/
noncomputable def availableBoundary (H : FiniteEdgeIndexedGraph W)
    (removed side : Finset W) : Finset H.Edge := by
  classical
  exact H.boundary side |>.filter fun e =>
    H.left e ∉ removed ∧ H.right e ∉ removed

@[simp] theorem mem_availableBoundary (H : FiniteEdgeIndexedGraph W)
    (removed side : Finset W) (e : H.Edge) :
    e ∈ H.availableBoundary removed side ↔
      H.Crosses side e ∧ H.left e ∉ removed ∧ H.right e ∉ removed := by
  simp [availableBoundary]

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {a b : W}

/-- Canonicalize an element cut by removing exactly the available crossing
edge copies. -/
noncomputable def TerminalElementCut.canonical
    (C : TerminalElementCut H terminals a b) :
    TerminalElementCut H terminals a b where
  removedVertices := C.removedVertices
  removedVertices_nonterminal := C.removedVertices_nonterminal
  removedEdges := H.availableBoundary C.removedVertices C.side
  side := C.side
  source_mem := C.source_mem
  target_not_mem := C.target_not_mem
  side_disjoint_removed := C.side_disjoint_removed
  crossing_removed := by
    intro e hl hr hcross
    simp [hcross, hl, hr]

theorem TerminalElementCut.canonical_order_le
    (C : TerminalElementCut H terminals a b) :
    C.canonical.order <= C.order := by
  classical
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro e he
  change e ∈ H.availableBoundary C.removedVertices C.side at he
  rw [mem_availableBoundary] at he
  exact C.crossing_removed e he.2.1 he.2.2 he.1

/-- Every ordered pair of distinct terminals requires at least `k` removed
elements to separate. -/
def TerminalElementConnectedAtLeast (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) : Prop :=
  ∀ ⦃a⦄, a ∈ terminals -> ∀ ⦃b⦄, b ∈ terminals -> a ≠ b ->
    ∀ C : TerminalElementCut H terminals a b, k <= C.order

theorem TerminalElementConnectedAtLeast.mono
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k l : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k) (hlk : l <= k) :
    H.TerminalElementConnectedAtLeast terminals l := by
  intro a ha b hb hab C
  exact hlk.trans (h ha hb hab C)

theorem terminalElementConnectedAtLeast_zero
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) :
    H.TerminalElementConnectedAtLeast terminals 0 := by
  intro a ha b hb hab C
  exact Nat.zero_le _

/-- Equivalent canonical cut formula. -/
theorem terminalElementConnectedAtLeast_iff_availableBoundary
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat) :
    H.TerminalElementConnectedAtLeast terminals k ↔
      ∀ ⦃a⦄, a ∈ terminals -> ∀ ⦃b⦄, b ∈ terminals -> a ≠ b ->
        ∀ (removed side : Finset W), Disjoint removed terminals ->
          a ∈ side -> b ∉ side -> Disjoint side removed ->
            k <= removed.card + (H.availableBoundary removed side).card := by
  constructor
  · intro h a ha b hb hab removed side hnonterminal haSide hbSide hdisjoint
    let C : TerminalElementCut H terminals a b :=
      { removedVertices := removed
        removedVertices_nonterminal := hnonterminal
        removedEdges := H.availableBoundary removed side
        side := side
        source_mem := haSide
        target_not_mem := hbSide
        side_disjoint_removed := hdisjoint
        crossing_removed := by
          intro e hl hr hcross
          simp [hcross, hl, hr] }
    exact h ha hb hab C
  · intro h a ha b hb hab C
    have hcanonical := h ha hb hab C.removedVertices C.side
      C.removedVertices_nonterminal C.source_mem C.target_not_mem
      C.side_disjoint_removed
    exact hcanonical.trans (by
      simpa [TerminalElementCut.canonical, TerminalElementCut.order] using
        C.canonical_order_le)

/-- Terminal element connectivity is bounded by every terminal degree when a
second terminal exists. -/
theorem TerminalElementConnectedAtLeast.le_degree
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k)
    {a : W} (ha : a ∈ terminals) (hb : ∃ b ∈ terminals, b ≠ a) :
    k <= H.degree a := by
  rcases hb with ⟨b, hb, hba⟩
  have hcut := (terminalElementConnectedAtLeast_iff_availableBoundary
    H terminals k).mp h ha hb hba.symm (∅ : Finset W) ({a} : Finset W)
    (by simp) (by simp) (by simp [hba]) (by simp)
  simpa [availableBoundary, H.boundary_singleton a, degree] using hcut

/-! ## Deletion transport -/

/-- Lift a cut through deletion by additionally removing the deleted edge in
the original graph. -/
noncomputable def TerminalElementCut.liftDelete
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b) :
    TerminalElementCut H terminals a b where
  removedVertices := C.removedVertices
  removedVertices_nonterminal := C.removedVertices_nonterminal
  removedEdges := C.removedEdges.image Subtype.val ∪ {e0}
  side := C.side
  source_mem := C.source_mem
  target_not_mem := C.target_not_mem
  side_disjoint_removed := C.side_disjoint_removed
  crossing_removed := by
    intro e hl hr hcross
    by_cases he : e = e0
    · simp [he]
    have hremoved := C.crossing_removed ⟨e, he⟩ hl hr hcross
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨e, he⟩, hremoved, rfl⟩)

theorem TerminalElementCut.liftDelete_order_le_add_one
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (C : TerminalElementCut (H.deleteEdge e0) terminals a b) :
    (C.liftDelete H e0).order <= C.order + 1 := by
  classical
  have himage : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact Subtype.ext hxy)
  have hunion := Finset.card_union_le (C.removedEdges.image Subtype.val) {e0}
  simp only [TerminalElementCut.order, TerminalElementCut.liftDelete]
  simp only [Finset.card_singleton] at hunion
  omega

/-- Restrict an original cut to the surviving edge indices after deletion. -/
noncomputable def TerminalElementCut.restrictDelete
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (C : TerminalElementCut H terminals a b) :
    TerminalElementCut (H.deleteEdge e0) terminals a b where
  removedVertices := C.removedVertices
  removedVertices_nonterminal := C.removedVertices_nonterminal
  removedEdges := Finset.univ.filter fun e : (H.deleteEdge e0).Edge =>
    e.1 ∈ C.removedEdges
  side := C.side
  source_mem := C.source_mem
  target_not_mem := C.target_not_mem
  side_disjoint_removed := C.side_disjoint_removed
  crossing_removed := by
    intro e hl hr hcross
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact C.crossing_removed e.1 hl hr hcross

theorem TerminalElementCut.restrictDelete_order_le
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    (C : TerminalElementCut H terminals a b) :
    (C.restrictDelete H e0).order <= C.order := by
  classical
  let removed := (C.restrictDelete H e0).removedEdges
  have hinj : Set.InjOn (fun e : (H.deleteEdge e0).Edge => e.1) removed := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have himage : (removed.image fun e => e.1).card = removed.card :=
    Finset.card_image_iff.mpr hinj
  have hsubset : removed.image (fun e => e.1) ⊆ C.removedEdges := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    simpa [removed, TerminalElementCut.restrictDelete] using hf
  have hcard : removed.card <= C.removedEdges.card := by
    rw [← himage]
    exact Finset.card_le_card hsubset
  simpa [TerminalElementCut.order, removed, TerminalElementCut.restrictDelete] using
    Nat.add_le_add_left hcard C.removedVertices.card

/-- Adding back a deleted named edge cannot lower terminal element
connectivity. -/
theorem TerminalElementConnectedAtLeast.of_deleteEdge
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (e0 : H.Edge)
    (h : (H.deleteEdge e0).TerminalElementConnectedAtLeast terminals k) :
    H.TerminalElementConnectedAtLeast terminals k := by
  intro a ha b hb hab C
  exact (h ha hb hab (C.restrictDelete H e0)).trans
    (C.restrictDelete_order_le H e0)

/-- Deleting one named edge lowers terminal element connectivity by at most
one. -/
theorem TerminalElementConnectedAtLeast.deleteEdge_sub_one
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k) (e0 : H.Edge) :
    (H.deleteEdge e0).TerminalElementConnectedAtLeast terminals (k - 1) := by
  intro a ha b hb hab C
  have hk := h ha hb hab (C.liftDelete H e0)
  have horder := C.liftDelete_order_le_add_one H e0
  omega

/-! ## Contraction transport -/

/-- Pulling a contracted vertex set back increases cardinality by at most one,
because only the merged vertex has a two-element fiber. -/
theorem ContractVertex.preimageFinset_card_le_add_one
    {p q : W} (X : Finset (ContractVertex W p q)) :
    (ContractVertex.preimageFinset X).card <= X.card + 1 := by
  classical
  let Y := ContractVertex.preimageFinset X
  have hinj : Set.InjOn (ContractVertex.projection (p := p) (q := q))
      (Y.erase q) := by
    intro x hx y hy hxy
    have hxq : x ≠ q := by
      change x ∈ Y.erase q at hx
      exact (Finset.mem_erase.mp hx).1
    have hyq : y ≠ q := by
      change y ∈ Y.erase q at hy
      exact (Finset.mem_erase.mp hy).1
    rcases ContractVertex.eq_or_both_endpoints_of_projection_eq hxy with h | hends
    · exact h
    · rcases hends.1 with hxp | hxq' <;> rcases hends.2 with hyp | hyq'
      · exact hxp.trans hyp.symm
      · exact (hyq hyq').elim
      · exact (hxq hxq').elim
      · exact (hxq hxq').elim
  have himage : ((Y.erase q).image
      (ContractVertex.projection (p := p) (q := q))).card = (Y.erase q).card :=
    Finset.card_image_iff.mpr hinj
  have hsubset : (Y.erase q).image
      (ContractVertex.projection (p := p) (q := q)) ⊆ X := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    exact ContractVertex.mem_preimageFinset.mp (Finset.mem_of_mem_erase hw)
  have herase : Y.card <= (Y.erase q).card + 1 := by
    by_cases hq : q ∈ Y
    · rw [Finset.card_erase_add_one hq]
    · simp [Finset.erase_eq_of_notMem hq]
  calc
    Y.card <= (Y.erase q).card + 1 := herase
    _ = ((Y.erase q).image
        (ContractVertex.projection (p := p) (q := q))).card + 1 := by rw [himage]
    _ <= X.card + 1 := Nat.add_le_add_right (Finset.card_le_card hsubset) 1

/-- Lift a contracted cut to the original graph.  Surviving removed edges use
their original indices, while removed vertices are pulled back through the
contraction projection. -/
noncomputable def TerminalElementCut.liftContract
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b') :
    TerminalElementCut H terminals a b where
  removedVertices := ContractVertex.preimageFinset C.removedVertices
  removedVertices_nonterminal := by
    rw [Finset.disjoint_left]
    intro w hw hwt
    have hprojRemoved := ContractVertex.mem_preimageFinset.mp hw
    have hprojTerminal : ContractVertex.projection
        (p := H.left e0) (q := H.right e0) w ∈
        ContractVertex.terminalImage
          (p := H.left e0) (q := H.right e0) terminals :=
      Finset.mem_image.mpr ⟨w, hwt, rfl⟩
    exact Finset.disjoint_left.mp C.removedVertices_nonterminal
      hprojRemoved hprojTerminal
  removedEdges := C.removedEdges.image Subtype.val
  side := ContractVertex.preimageFinset C.side
  source_mem := by
    rw [ContractVertex.mem_preimageFinset, ha]
    exact C.source_mem
  target_not_mem := by
    rw [ContractVertex.mem_preimageFinset, hb]
    exact C.target_not_mem
  side_disjoint_removed := by
    rw [Finset.disjoint_left]
    intro w hwSide hwRemoved
    exact Finset.disjoint_left.mp C.side_disjoint_removed
      (ContractVertex.mem_preimageFinset.mp hwSide)
      (ContractVertex.mem_preimageFinset.mp hwRemoved)
  crossing_removed := by
    intro e hl hr hcross
    have hsurvives : H.SurvivesContraction e0 e := by
      intro heq
      rcases hcross with hcross | hcross
      · have hleft : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.left e) ∈ C.side := by
          simpa using hcross.1
        have hright : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.right e) ∉ C.side := by
          simpa using hcross.2
        exact hright (heq ▸ hleft)
      · have hright : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.right e) ∈ C.side := by
          simpa using hcross.1
        have hleft : ContractVertex.projection
            (p := H.left e0) (q := H.right e0) (H.left e) ∉ C.side := by
          simpa using hcross.2
        exact hleft (heq.symm ▸ hright)
    let f : (H.contractEdge e0).Edge := ⟨e, hsurvives⟩
    have hremoved : f ∈ C.removedEdges := C.crossing_removed f
      (by simpa [f] using hl) (by simpa [f] using hr)
      ((contractEdge_crosses_iff H e0 C.side f).mpr hcross)
    exact Finset.mem_image.mpr ⟨f, hremoved, rfl⟩

theorem TerminalElementCut.liftContract_order_le_add_one
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) (terminals : Finset W)
    {a' b' : ContractVertex W (H.left e0) (H.right e0)} {a b : W}
    (ha : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) a = a')
    (hb : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) b = b')
    (C : TerminalElementCut (H.contractEdge e0)
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) a' b') :
    (C.liftContract H e0 terminals ha hb).order <= C.order + 1 := by
  classical
  have hvertices := ContractVertex.preimageFinset_card_le_add_one C.removedVertices
  have hedges : (C.removedEdges.image Subtype.val).card = C.removedEdges.card :=
    Finset.card_image_iff.mpr (by
      intro x hx y hy hxy
      exact Subtype.ext hxy)
  simp only [TerminalElementCut.order, TerminalElementCut.liftContract]
  rw [hedges]
  omega

/-- Contracting a nonterminal named edge lowers terminal element connectivity
by at most one. -/
theorem TerminalElementConnectedAtLeast.contractEdge_sub_one
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (h : H.TerminalElementConnectedAtLeast terminals k) (e0 : H.Edge)
    (hp : H.left e0 ∉ terminals) (hq : H.right e0 ∉ terminals) :
    (H.contractEdge e0).TerminalElementConnectedAtLeast
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) (k - 1) := by
  have _hterminalCard := ContractVertex.terminalImage_card terminals hp hq
  intro a' ha' b' hb' hab C
  rw [ContractVertex.mem_terminalImage] at ha' hb'
  rcases ha' with ⟨a, ha, hpa⟩
  rcases hb' with ⟨b, hb, hpb⟩
  have hab' : a ≠ b := by
    intro heq
    subst b
    exact hab (hpa.symm.trans hpb)
  have hk := h ha hb hab' (C.liftContract H e0 terminals hpa hpb)
  have horder := C.liftContract_order_le_add_one H e0 terminals hpa hpb
  omega

/-! ## Exact remaining source boundary -/

/-- The at-least form of Hind--Oellermann, journal Theorem 5.13.  This is a
statement, not an assumption: proving it is the first non-elementary source
step after the transport lemmas above. -/
def HindOellermannDeletionContractionStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (e0 : H.Edge),
      H.left e0 ∉ terminals -> H.right e0 ∉ terminals ->
      H.TerminalElementConnectedAtLeast terminals k ->
        (H.deleteEdge e0).TerminalElementConnectedAtLeast terminals k ∨
          (H.contractEdge e0).TerminalElementConnectedAtLeast
            (ContractVertex.terminalImage
              (p := H.left e0) (q := H.right e0) terminals) k

end FiniteEdgeIndexedGraph

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
