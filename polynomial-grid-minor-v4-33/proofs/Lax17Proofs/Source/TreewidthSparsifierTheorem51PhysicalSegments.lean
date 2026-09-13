import Lax17Proofs.Source.TreewidthSparsifierTheorem51ExactRails

namespace Lax17Proofs

universe u v w

/-!
# Physical red-rail segments for Theorem 5.1

Step 2 of `treewidth-sparsifier.pdf`, Theorem 5.1 partitions each complete
red rail into contiguous physical subpaths.  A branch vertex is coloured by
the unique recorded local layer in which it is a branch vertex; every other
vertex receives a private colour.  Thus a heavy colour is necessarily a
recorded layer once the threshold is at least two.

This module applies the generic greedy decomposition to the exact rail support
and turns every resulting list segment back into an actual `GraphPath`.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open HeavySegments


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- A vertex is a branch vertex of recorded local layer `j`. -/
def IsBranchAt
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) (v : V) : Prop :=
  v ∈ branchVertexFinset (E.recordAt j).layer.localGraph

/-- A vertex cannot be a branch vertex in two different realized records. -/
theorem branchRecord_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin E.finalState.records.length} {v : V}
    (hj : E.IsBranchAt j v) (hk : E.IsBranchAt k v) :
    j = k := by
  rcases E.localBranchVertex_mem_localRedPath j hj with ⟨x, hx⟩
  rcases E.localBranchVertex_mem_localRedPath k hk with ⟨y, hy⟩
  exact E.localRedPath_record_unique hbudget hx hy

/-- The (unique when present) recorded layer responsible for a branch
vertex. -/
noncomputable def branchRecord?
    (E : ExpanderBlocks P count) (v : V) :
    Option (Fin E.finalState.records.length) := by
  classical
  exact
    if hex : ∃ j, E.IsBranchAt j v then
      some (Classical.choose hex)
    else
      none

/-- Colour used by the physical greedy segmentation.  Branch vertices are
coloured by their record; nonbranch vertices receive their own private
colour. -/
noncomputable def exactRailColour
    (E : ExpanderBlocks P count) (v : V) :
    Fin E.finalState.records.length ⊕ V :=
  match E.branchRecord? v with
  | some j => Sum.inl j
  | none => Sum.inr v

theorem exactRailColour_eq_record_of_branch
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) {v : V}
    (hv : E.IsBranchAt j v) :
    E.exactRailColour v = Sum.inl j := by
  classical
  let hex : ∃ k, E.IsBranchAt k v := ⟨j, hv⟩
  have hchosen :
      Classical.choose hex = j :=
    E.branchRecord_unique hbudget (Classical.choose_spec hex) hv
  rw [exactRailColour, branchRecord?]
  simp only [dif_pos hex]
  rw [hchosen]

theorem branch_of_exactRailColour_eq_record
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) {v : V}
    (hv : E.exactRailColour v = Sum.inl j) :
    E.IsBranchAt j v := by
  classical
  by_cases hex : ∃ k, E.IsBranchAt k v
  · simp only [exactRailColour, branchRecord?, dif_pos hex] at hv
    have hchosen : Classical.choose hex = j := by
      simpa using hv
    simpa [← hchosen] using Classical.choose_spec hex
  · simp [exactRailColour, branchRecord?, hex] at hv

theorem eq_of_exactRailColour_eq_private
    (E : ExpanderBlocks P count) {v w : V}
    (hcolour : E.exactRailColour w = Sum.inr v) :
    w = v := by
  classical
  unfold exactRailColour branchRecord? at hcolour
  split at hcolour
  · simp at hcolour
  · simpa using hcolour

theorem private_colour_count_le_count
    (E : ExpanderBlocks P count) (v : V) :
    ∀ s : List V,
      colourCount E.exactRailColour (Sum.inr v) s ≤ s.count v
  | [] => by simp [colourCount]
  | w :: s => by
      have ih := E.private_colour_count_le_count v s
      by_cases hcolour : E.exactRailColour w = Sum.inr v
      · have hwv := E.eq_of_exactRailColour_eq_private hcolour
        subst w
        simpa [colourCount, hcolour] using Nat.succ_le_succ ih
      ·
        by_cases hwv : w = v
        · subst w
          have hcount :
              s.count v ≤ (v :: s).count v := by simp
          have hle : colourCount E.exactRailColour (Sum.inr v) s ≤
              (v :: s).count v :=
            ih.trans hcount
          simpa [colourCount, hcolour] using hle
        · simpa [colourCount, hcolour, hwv] using ih

/-- Greedy physical segmentation of the exact support of one global red
rail. -/
noncomputable def exactRailSegmentation
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B) :
    Decomposition E.exactRailColour B
      (E.exactRailPath hbudget hrecords x).walk.support :=
  Classical.choice
    (exists_decomposition E.exactRailColour hB
      (E.exactRailPath hbudget hrecords x).walk.support)

@[simp] theorem exactRailSegmentation_flatten
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B) :
    (E.exactRailSegmentation hbudget hrecords x B hB).segments.flatten =
      (E.exactRailPath hbudget hrecords x).walk.support :=
  (E.exactRailSegmentation hbudget hrecords x B hB).flatten_segments

theorem exactRailSegment_nonempty
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments) :
    s ≠ [] := by
  have hmembers :=
    (E.exactRailSegmentation hbudget hrecords x B hB)
      |>.members_nonempty_of_input
  exact hmembers
    (E.exactRailPath hbudget hrecords x).walk.support_ne_nil s hs

/-- Every produced segment is a contiguous infix of its exact rail. -/
theorem exactRailSegment_isInfix
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments) :
    s <:+: (E.exactRailPath hbudget hrecords x).walk.support := by
  rw [← E.exactRailSegmentation_flatten hbudget hrecords x B hB]
  exact List.infix_of_mem_flatten hs

/-- The actual red-support path carried by a physical segment. -/
noncomputable def exactRailSegmentPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments) :
    GraphPath (E.redSupport hbudget) := by
  let hne := E.exactRailSegment_nonempty hbudget hrecords x B hB s hs
  let hinfix :=
    E.exactRailSegment_isInfix hbudget hrecords x B hB s hs
  let hchain :=
    (E.exactRailPath hbudget hrecords x).walk.isChain_adj_support.infix
      hinfix
  let W :=
    _root_.SimpleGraph.Walk.ofSupport s hne hchain
  refine {
    source := s.head hne
    target := s.getLast hne
    walk := W
    isPath := ?_
  }
  apply _root_.SimpleGraph.Walk.IsPath.mk'
  rw [_root_.SimpleGraph.Walk.support_ofSupport]
  exact hinfix.nodup
    (E.exactRailPath hbudget hrecords x).isPath.support_nodup

@[simp] theorem exactRailSegmentPath_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments) :
    (E.exactRailSegmentPath hbudget hrecords x B hB s hs).vertexSet =
      s.toFinset := by
  classical
  simp [exactRailSegmentPath, GraphPath.vertexSet]

/-- Per recorded layer, a physical rail segment contains at most `2 * B`
branch vertices. -/
theorem exactRailSegment_branch_count_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments)
    (j : Fin E.finalState.records.length) :
    colourCount E.exactRailColour (Sum.inl j) s ≤ 2 * B :=
  (E.exactRailSegmentation hbudget hrecords x B hB).bounded
    s hs (Sum.inl j)

/-- A private (nonbranch) colour occurs at most once in a physical segment,
because the complete exact rail is a path. -/
theorem exactRailSegment_private_count_le_one
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    (s : List V)
    (hs :
      s ∈ (E.exactRailSegmentation hbudget hrecords x B hB).segments)
    (v : V) :
    colourCount E.exactRailColour (Sum.inr v) s ≤ 1 := by
  have hnodup :
      s.Nodup :=
    (E.exactRailSegment_isInfix hbudget hrecords x B hB s hs).nodup
      (E.exactRailPath hbudget hrecords x).isPath.support_nodup
  exact (E.private_colour_count_le_count v s).trans
    ((List.nodup_iff_count_le_one.mp hnodup) v)

/-- If a rail is split into several physical segments and `B > 1`, each
segment is heavy in an actual recorded layer (never merely at a private
nonbranch colour). -/
theorem exactRailSegment_heavy_record_of_split
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 1 < B)
    (hmany :
      1 <
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments.length)
    (s : List V)
    (hs :
      s ∈
        (E.exactRailSegmentation hbudget hrecords x B
          (by omega)).segments) :
    ∃ j : Fin E.finalState.records.length,
      B ≤ colourCount E.exactRailColour (Sum.inl j) s := by
  obtain ⟨c, hc⟩ :=
    (E.exactRailSegmentation hbudget hrecords x B (by omega))
      |>.all_heavy_if_split hmany s hs
  rcases c with j | v
  · exact ⟨j, hc⟩
  · have hprivate :=
      E.exactRailSegment_private_count_le_one hbudget hrecords x B
        (by omega) s hs v
    omega

/-- A finite index for every physical segment of every exact rail. -/
abbrev ExactRailSegmentIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B) :=
  Σ x : Fin h,
    Fin (E.exactRailSegmentation hbudget hrecords x B hB).segments.length

/-- The vertex list carried by a globally indexed physical segment. -/
noncomputable def exactRailSegmentList
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) : List V :=
  (E.exactRailSegmentation hbudget hrecords i.1 B hB).segments.get i.2

theorem exactRailSegmentList_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    E.exactRailSegmentList hbudget hrecords B hB i ∈
      (E.exactRailSegmentation hbudget hrecords i.1 B hB).segments := by
  exact List.get_mem _ _

/-- The path carried by a globally indexed physical segment. -/
noncomputable def exactRailSegmentPathAt
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    GraphPath (E.redSupport hbudget) :=
  E.exactRailSegmentPath hbudget hrecords i.1 B hB
    (E.exactRailSegmentList hbudget hrecords B hB i)
    (E.exactRailSegmentList_mem hbudget hrecords B hB i)

@[simp] theorem exactRailSegmentPathAt_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.exactRailSegmentPathAt hbudget hrecords B hB i).vertexSet =
      (E.exactRailSegmentList hbudget hrecords B hB i).toFinset := by
  simp [exactRailSegmentPathAt]

theorem exactRailSegmentPathAt_vertexSet_subset_rail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.exactRailSegmentPathAt hbudget hrecords B hB i).vertexSet ⊆
      (E.exactRailPath hbudget hrecords i.1).vertexSet := by
  classical
  rw [E.exactRailSegmentPathAt_vertexSet]
  intro v hv
  have hvList :
      v ∈ E.exactRailSegmentList hbudget hrecords B hB i := by
    simpa using hv
  have hinfix :=
    E.exactRailSegment_isInfix hbudget hrecords i.1 B hB
      (E.exactRailSegmentList hbudget hrecords B hB i)
      (E.exactRailSegmentList_mem hbudget hrecords B hB i)
  have hvSupport :
      v ∈ (E.exactRailPath hbudget hrecords i.1).walk.support :=
    hinfix.sublist.subset hvList
  simpa [GraphPath.vertexSet] using hvSupport

/-- Distinct physical segments on the same rail have disjoint vertex lists. -/
theorem exactRailSegmentLists_disjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B)
    {i j :
      Fin (E.exactRailSegmentation hbudget hrecords x B hB).segments.length}
    (hij : i ≠ j) :
    List.Disjoint
      ((E.exactRailSegmentation hbudget hrecords x B hB).segments.get i)
      ((E.exactRailSegmentation hbudget hrecords x B hB).segments.get j) := by
  let D := E.exactRailSegmentation hbudget hrecords x B hB
  have hflatten : D.segments.flatten.Nodup := by
    rw [D.flatten_segments]
    exact (E.exactRailPath hbudget hrecords x).isPath.support_nodup
  have hpw : D.segments.Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hflatten).2
  rcases lt_or_gt_of_ne hij with hijLt | hjiLt
  · exact hpw.rel_get_of_lt hijLt
  · exact (hpw.rel_get_of_lt hjiLt).symm

/-- All globally indexed physical segments are pairwise node-disjoint. -/
theorem exactRailSegmentPathAt_nodeDisjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    {i j : ExactRailSegmentIndex E hbudget hrecords B hB}
    (hij : i ≠ j) :
    GraphPath.NodeDisjoint
      (E.exactRailSegmentPathAt hbudget hrecords B hB i)
      (E.exactRailSegmentPathAt hbudget hrecords B hB j) := by
  classical
  by_cases hrail : i.1 = j.1
  · rcases i with ⟨x, i⟩
    rcases j with ⟨y, j⟩
    simp only at hrail
    subst y
    have hij' : i ≠ j := by
      intro heq
      apply hij
      cases heq
      rfl
    have hlist :=
      E.exactRailSegmentLists_disjoint hbudget hrecords x B hB hij'
    rw [GraphPath.NodeDisjoint,
      E.exactRailSegmentPathAt_vertexSet,
      E.exactRailSegmentPathAt_vertexSet,
      Finset.disjoint_left]
    intro v hvi hvj
    exact List.disjoint_left.mp hlist
      (by simpa using hvi) (by simpa using hvj)
  · exact
      (E.exactRailPath_nodeDisjoint hbudget hrecords hrail).mono
        (E.exactRailSegmentPathAt_vertexSet_subset_rail
          hbudget hrecords B hB i)
        (E.exactRailSegmentPathAt_vertexSet_subset_rail
          hbudget hrecords B hB j)

/-- The finite node-disjoint family of all physical red-rail segments. -/
noncomputable def physicalSegmentPacking
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B) :
    PathPacking (E.redSupport hbudget) Finset.univ Finset.univ where
  Index := ExactRailSegmentIndex E hbudget hrecords B hB
  path := E.exactRailSegmentPathAt hbudget hrecords B hB
  connects := by
    intro i
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro i j hij
    exact E.exactRailSegmentPathAt_nodeDisjoint
      hbudget hrecords B hB hij

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
