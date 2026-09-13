import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorTrace
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Measures

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: cycle-erased full-column hill replacement

This module isolates the support bookkeeping needed in the hill-elimination
part of Chekuri--Chuzhoy Appendix B.  A column is kept as a full path between
the two boundary rows.  Replacing a hill excursion by a row interval and then
erasing cycles preserves those exact endpoints, the unique boundary contacts,
avoidance of the linkage outside the corridor, and disjointness from every
other column.

The final theorem also proves strict descent of the paper's second measure:
the number of column edges outside the current row-edge set.  Its input asks
for the concrete non-row edge in the deleted excursion; the Appendix B valley
argument produces that edge from the visit to the adjacent disjoint row.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {J : Type v} [Fintype J] [DecidableEq J]

open IndexedAuxiliaryPrefix

/-- The union of the edge sets of a finite family of full columns. -/
noncomputable def fullColumnFamilyEdgeSet
    (columns : J → GraphPath G) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun j : J => (columns j).edgeSet

/-- The edges used by the columns but not by any current row. -/
noncomputable def fullColumnNonRowEdgeSet
    (rowEdges : Finset (Sym2 V)) (columns : J → GraphPath G) :
    Finset (Sym2 V) :=
  fullColumnFamilyEdgeSet columns \ rowEdges

/-- The paper's hill-elimination measure, expressed through the common
`outsideFixedMeasure` API. -/
noncomputable def fullColumnNonRowEdgeMeasure
    (rowEdges : Finset (Sym2 V)) (columns : J → GraphPath G) : ℕ :=
  outsideFixedMeasure (fullColumnFamilyEdgeSet columns) rowEdges

theorem fullColumnNonRowEdgeMeasure_eq_card
    (rowEdges : Finset (Sym2 V)) (columns : J → GraphPath G) :
    fullColumnNonRowEdgeMeasure rowEdges columns =
      (fullColumnNonRowEdgeSet rowEdges columns).card := by
  rfl

/-- Replace one member of a finite column family. -/
noncomputable def replaceFullColumn
    (columns : J → GraphPath G) (selected : J) (replacement : GraphPath G) :
    J → GraphPath G :=
  fun j => if j = selected then replacement else columns j

@[simp] theorem replaceFullColumn_selected
    (columns : J → GraphPath G) (selected : J) (replacement : GraphPath G) :
    replaceFullColumn columns selected replacement selected = replacement := by
  simp [replaceFullColumn]

@[simp] theorem replaceFullColumn_of_ne
    (columns : J → GraphPath G) (selected : J) (replacement : GraphPath G)
    {j : J} (hj : j ≠ selected) :
    replaceFullColumn columns selected replacement j = columns j := by
  simp [replaceFullColumn, hj]

/-- A path starting on one member of a pairwise vertex-disjoint path family
cannot leave that member while using only edges of the family. -/
theorem graphPath_vertexSet_subset_row_of_edgeSet_subset_pairwiseUnion
    {I : Type v} [Fintype I] [DecidableEq I]
    (rows : I → GraphPath G)
    (hpairwise : Pairwise fun i j : I =>
      (rows i).NodeDisjoint (rows j))
    (base : I) (P : GraphPath G)
    (hsource : P.source ∈ (rows base).vertexSet)
    (hedges :
      P.edgeSet ⊆
        Finset.univ.biUnion fun i : I => (rows i).edgeSet) :
    P.vertexSet ⊆ (rows base).vertexSet := by
  classical
  have aux :
      ∀ {x y : V} (W : G.Walk x y),
        x ∈ (rows base).vertexSet →
          (∀ e : Sym2 V, e ∈ W.edges.toFinset →
            e ∈ Finset.univ.biUnion fun i : I => (rows i).edgeSet) →
          ∀ z : V, z ∈ W.support.toFinset →
            z ∈ (rows base).vertexSet := by
    intro x y W
    induction W with
    | nil =>
        intro hx _ z hz
        simp at hz
        simpa [hz] using hx
    | @cons x y z hxy W ih =>
        intro hx hWedges q hq
        have hqList : q ∈ x :: W.support := List.mem_toFinset.mp hq
        rcases List.mem_cons.1 hqList with rfl | hqtail
        · exact hx
        · have hfirstUnion :
              s(x, y) ∈
                Finset.univ.biUnion fun i : I => (rows i).edgeSet :=
            hWedges s(x, y) (by simp)
          rcases Finset.mem_biUnion.1 hfirstUnion with
            ⟨owner, _howner, hfirstOwner⟩
          have hends :
              x ∈ (rows owner).vertexSet ∧
                y ∈ (rows owner).vertexSet :=
            (rows owner).endpoints_mem_vertexSet_of_edgeSet hfirstOwner
          have howner_eq : owner = base := by
            by_contra hne
            exact Finset.disjoint_left.mp (hpairwise hne) hends.1 hx
          have hy : y ∈ (rows base).vertexSet := by
            simpa [howner_eq] using hends.2
          have htailEdges :
              ∀ e : Sym2 V, e ∈ W.edges.toFinset →
                e ∈ Finset.univ.biUnion fun i : I => (rows i).edgeSet := by
            intro e he
            exact hWedges e (by
              have heList : e ∈ W.edges := List.mem_toFinset.mp he
              exact List.mem_toFinset.mpr (by
                simpa using List.mem_cons_of_mem s(x, y) heList))
          exact ih hy htailEdges q (List.mem_toFinset.mpr hqtail)
  intro x hx
  have hxsupport : x ∈ P.walk.support.toFinset := by
    simpa [GraphPath.vertexSet] using hx
  exact aux P.walk hsource
    (by
      intro e he
      exact hedges (by simpa [GraphPath.edgeSet] using he))
    x hxsupport

/-- If a path starts on one row and meets a distinct row in a pairwise
vertex-disjoint row family, it uses an edge outside the union of row edges. -/
theorem exists_edge_not_mem_pairwiseRowEdgeUnion_of_hits_other
    {I : Type v} [Fintype I] [DecidableEq I]
    (rows : I → GraphPath G)
    (hpairwise : Pairwise fun i j : I =>
      (rows i).NodeDisjoint (rows j))
    {base other : I} (hbaseOther : base ≠ other)
    (P : GraphPath G)
    (hsource : P.source ∈ (rows base).vertexSet)
    (hhit : HitsGraphPath P (rows other)) :
    ∃ e : Sym2 V, e ∈ P.edgeSet ∧
      e ∉ Finset.univ.biUnion fun i : I => (rows i).edgeSet := by
  classical
  by_cases hedges :
      P.edgeSet ⊆
        Finset.univ.biUnion fun i : I => (rows i).edgeSet
  · have hvertices :
        P.vertexSet ⊆ (rows base).vertexSet :=
      graphPath_vertexSet_subset_row_of_edgeSet_subset_pairwiseUnion
        rows hpairwise base P hsource hedges
    rcases hhit with ⟨x, hx⟩
    have hxP := (Finset.mem_inter.1 hx).1
    have hxOther := (Finset.mem_inter.1 hx).2
    exact False.elim
      (Finset.disjoint_left.mp (hpairwise hbaseOther)
        (hvertices hxP) hxOther)
  · exact Finset.not_subset.mp hedges

/-- Data for one oriented hill replacement.

`left_before_right` uses the orientation of the full column from its lower
boundary endpoint to its upper boundary endpoint.  `rowInterval` is already
oriented from `left` to `right`; reversing a row interval before constructing
this input covers the other row orientation.

The `deleted_nonRow_edge` field is the local support conclusion used by the
strict-measure proof.  It is deliberately an edge witness rather than a
cardinality inequality, so the descent itself is proved below. -/
structure FullColumnHillInput
    (rowEdges : Finset (Sym2 V)) (outsideLinkageVertices : Finset V)
    (lowerBoundary upperBoundary : GraphPath G)
    (columns : J → GraphPath G) (selected : J) where
  left : V
  right : V
  left_mem_column : left ∈ (columns selected).vertexSet
  right_mem_column : right ∈ (columns selected).vertexSet
  left_before_right : (columns selected).Before left right
  rowInterval : GraphPath G
  rowInterval_source : rowInterval.source = left
  rowInterval_target : rowInterval.target = right
  rowInterval_edgeSet_subset_rows : rowInterval.edgeSet ⊆ rowEdges
  old_lowerBoundary_contact :
    (columns selected).vertexSet ∩ lowerBoundary.vertexSet =
      {(columns selected).source}
  old_upperBoundary_contact :
    (columns selected).vertexSet ∩ upperBoundary.vertexSet =
      {(columns selected).target}
  rowInterval_avoids_lowerBoundary :
    Disjoint rowInterval.vertexSet lowerBoundary.vertexSet
  rowInterval_avoids_upperBoundary :
    Disjoint rowInterval.vertexSet upperBoundary.vertexSet
  old_avoids_outsideLinkage :
    Disjoint (columns selected).vertexSet outsideLinkageVertices
  rowInterval_avoids_outsideLinkage :
    Disjoint rowInterval.vertexSet outsideLinkageVertices
  old_nodeDisjoint_other :
    ∀ j : J, j ≠ selected → (columns selected).NodeDisjoint (columns j)
  rowInterval_nodeDisjoint_other :
    ∀ j : J, j ≠ selected →
      Disjoint rowInterval.vertexSet (columns j).vertexSet
  deleted_nonRow_edge :
    ∃ e : Sym2 V,
      e ∈ ((columns selected).segmentOfBefore left_before_right).edgeSet ∧
        e ∉ rowEdges

namespace FullColumnHillInput

variable {rowEdges : Finset (Sym2 V)}
variable {outsideLinkageVertices : Finset V}
variable {lowerBoundary upperBoundary : GraphPath G}
variable {columns : J → GraphPath G} {selected : J}

/-- The retained prefix of the selected full column. -/
noncomputable def retainedPrefix
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    GraphPath G :=
  (columns selected).takeUntil H.left_mem_column

/-- The retained suffix of the selected full column. -/
noncomputable def suffix
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    GraphPath G :=
  (columns selected).dropUntil H.right_mem_column

/-- The deleted excursion between the two contacts on the selected column. -/
noncomputable def deletedSegment
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    GraphPath G :=
  (columns selected).segmentOfBefore H.left_before_right

/-- The replacement path: retained prefix, row interval, retained suffix,
followed by cycle erasure. -/
noncomputable def replacementPath
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    GraphPath G :=
  H.retainedPrefix.append3WithEqToPath H.rowInterval H.suffix
    (by simp [retainedPrefix, H.rowInterval_source])
    (by simp [suffix, H.rowInterval_target])

@[simp] theorem replacementPath_source
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.source = (columns selected).source := by
  rfl

@[simp] theorem replacementPath_target
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.target = (columns selected).target := by
  rfl

/-- Cycle erasure introduces no vertex outside the retained pieces. -/
theorem replacementPath_vertexSet_subset_parts
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.vertexSet ⊆
      H.retainedPrefix.vertexSet ∪ H.rowInterval.vertexSet ∪
        H.suffix.vertexSet := by
  exact GraphPath.append3WithEqToPath_vertexSet_subset
    H.retainedPrefix H.rowInterval H.suffix
      (by simp [retainedPrefix, H.rowInterval_source])
      (by simp [suffix, H.rowInterval_target])

/-- Cycle erasure introduces no edge outside the retained pieces. -/
theorem replacementPath_edgeSet_subset_parts
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.edgeSet ⊆
      H.retainedPrefix.edgeSet ∪ H.rowInterval.edgeSet ∪ H.suffix.edgeSet := by
  exact GraphPath.append3WithEqToPath_edgeSet_subset
    H.retainedPrefix H.rowInterval H.suffix
      (by simp [retainedPrefix, H.rowInterval_source])
      (by simp [suffix, H.rowInterval_target])

/-- A coarser vertex-support statement convenient for preservation proofs. -/
theorem replacementPath_vertexSet_subset_old_union_rowInterval
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.vertexSet ⊆
      (columns selected).vertexSet ∪ H.rowInterval.vertexSet := by
  intro x hx
  have hparts := H.replacementPath_vertexSet_subset_parts hx
  rcases Finset.mem_union.1 hparts with hpre_or_mid | hsuf
  · rcases Finset.mem_union.1 hpre_or_mid with hpre | hmid
    · exact Finset.mem_union.2 <| Or.inl <|
        (columns selected).takeUntil_vertexSet_subset H.left_mem_column hpre
    · exact Finset.mem_union.2 (Or.inr hmid)
  · exact Finset.mem_union.2 <| Or.inl <|
      (columns selected).dropUntil_vertexSet_subset H.right_mem_column hsuf

/-- A coarser edge-support statement convenient for preservation proofs. -/
theorem replacementPath_edgeSet_subset_old_union_rowInterval
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.edgeSet ⊆
      (columns selected).edgeSet ∪ H.rowInterval.edgeSet := by
  intro e he
  have hparts := H.replacementPath_edgeSet_subset_parts he
  rcases Finset.mem_union.1 hparts with hpre_or_mid | hsuf
  · rcases Finset.mem_union.1 hpre_or_mid with hpre | hmid
    · exact Finset.mem_union.2 <| Or.inl <|
        (columns selected).takeUntil_edgeSet_subset H.left_mem_column hpre
    · exact Finset.mem_union.2 (Or.inr hmid)
  · exact Finset.mem_union.2 <| Or.inl <|
      (columns selected).dropUntil_edgeSet_subset H.right_mem_column hsuf

/-- The deleted excursion meets the retained prefix only at `left`. -/
theorem deletedSegment_inter_prefix_endpoint
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected)
    {x : V} (hxdeleted : x ∈ H.deletedSegment.vertexSet)
    (hxprefix : x ∈ H.retainedPrefix.vertexSet) :
    x = H.left := by
  have hx_before_left :
      (columns selected).Before x H.left :=
    (columns selected).before_of_mem_takeUntil H.left_mem_column hxprefix
  have hleft_before_x :
      (columns selected).Before H.left x :=
    (columns selected).before_of_mem_segmentOfBefore_left
      H.left_before_right hxdeleted
  exact (columns selected).before_antisymm hx_before_left hleft_before_x

/-- The deleted excursion meets the retained suffix only at `right`. -/
theorem deletedSegment_inter_suffix_endpoint
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected)
    {x : V} (hxdeleted : x ∈ H.deletedSegment.vertexSet)
    (hxsuffix : x ∈ H.suffix.vertexSet) :
    x = H.right := by
  have hx_before_right :
      (columns selected).Before x H.right :=
    (columns selected).before_of_mem_segmentOfBefore_right
      H.left_before_right hxdeleted
  have hright_before_x :
      (columns selected).Before H.right x :=
    ⟨H.right_mem_column, hxsuffix⟩
  exact (columns selected).before_antisymm hx_before_right hright_before_x

/-- The deleted excursion and retained prefix share no edge. -/
theorem deletedSegment_edgeDisjoint_prefix
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.deletedSegment.EdgeDisjoint H.retainedPrefix :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := H.left) (by
      intro x hxdeleted hxprefix
      exact H.deletedSegment_inter_prefix_endpoint hxdeleted hxprefix)

/-- The deleted excursion and retained suffix share no edge. -/
theorem deletedSegment_edgeDisjoint_suffix
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.deletedSegment.EdgeDisjoint H.suffix :=
  IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_vertex_inter_subset_singleton
    (x := H.right) (by
      intro x hxdeleted hxsuffix
      exact H.deletedSegment_inter_suffix_endpoint hxdeleted hxsuffix)

/-- The replacement has the same unique contact with the lower boundary as
the original full column. -/
theorem replacementPath_lowerBoundary_contact
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.vertexSet ∩ lowerBoundary.vertexSet =
      {(columns selected).source} := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.1 hx with ⟨hxreplacement, hxlower⟩
    rcases Finset.mem_union.1
        (H.replacementPath_vertexSet_subset_old_union_rowInterval
          hxreplacement) with hxold | hxrow
    · have hxsingleton :
          x ∈ ({(columns selected).source} : Finset V) := by
        rw [← H.old_lowerBoundary_contact]
        exact Finset.mem_inter.2 ⟨hxold, hxlower⟩
      exact hxsingleton
    · exact False.elim
        (Finset.disjoint_left.mp H.rowInterval_avoids_lowerBoundary
          hxrow hxlower)
  · intro x hx
    have hxsource : x = (columns selected).source := by
      simpa using hx
    subst x
    have hsource_lower :
        (columns selected).source ∈ lowerBoundary.vertexSet := by
      have hsource_inter :
          (columns selected).source ∈
            (columns selected).vertexSet ∩ lowerBoundary.vertexSet := by
        rw [H.old_lowerBoundary_contact]
        simp
      exact (Finset.mem_inter.1 hsource_inter).2
    exact Finset.mem_inter.2
      ⟨by simpa using GraphPath.source_mem_vertexSet H.replacementPath,
        hsource_lower⟩

/-- The replacement has the same unique contact with the upper boundary as
the original full column. -/
theorem replacementPath_upperBoundary_contact
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    H.replacementPath.vertexSet ∩ upperBoundary.vertexSet =
      {(columns selected).target} := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.1 hx with ⟨hxreplacement, hxupper⟩
    rcases Finset.mem_union.1
        (H.replacementPath_vertexSet_subset_old_union_rowInterval
          hxreplacement) with hxold | hxrow
    · have hxsingleton :
          x ∈ ({(columns selected).target} : Finset V) := by
        rw [← H.old_upperBoundary_contact]
        exact Finset.mem_inter.2 ⟨hxold, hxupper⟩
      exact hxsingleton
    · exact False.elim
        (Finset.disjoint_left.mp H.rowInterval_avoids_upperBoundary
          hxrow hxupper)
  · intro x hx
    have hxtarget : x = (columns selected).target := by
      simpa using hx
    subst x
    have htarget_upper :
        (columns selected).target ∈ upperBoundary.vertexSet := by
      have htarget_inter :
          (columns selected).target ∈
            (columns selected).vertexSet ∩ upperBoundary.vertexSet := by
        rw [H.old_upperBoundary_contact]
        simp
      exact (Finset.mem_inter.1 htarget_inter).2
    exact Finset.mem_inter.2
      ⟨by simpa using GraphPath.target_mem_vertexSet H.replacementPath,
        htarget_upper⟩

/-- Cycle erasure preserves avoidance of all linkage vertices outside the
corridor. -/
theorem replacementPath_avoids_outsideLinkage
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    Disjoint H.replacementPath.vertexSet outsideLinkageVertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hxreplacement hxoutside
  rcases Finset.mem_union.1
      (H.replacementPath_vertexSet_subset_old_union_rowInterval
        hxreplacement) with hxold | hxrow
  · exact Finset.disjoint_left.mp H.old_avoids_outsideLinkage
      hxold hxoutside
  · exact Finset.disjoint_left.mp H.rowInterval_avoids_outsideLinkage
      hxrow hxoutside

/-- The replacement remains vertex-disjoint from every other full column. -/
theorem replacementPath_nodeDisjoint_other
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    ∀ j : J, j ≠ selected →
      H.replacementPath.NodeDisjoint (columns j) := by
  classical
  intro j hj
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hxreplacement hxother
  rcases Finset.mem_union.1
      (H.replacementPath_vertexSet_subset_old_union_rowInterval
        hxreplacement) with hxold | hxrow
  · exact Finset.disjoint_left.mp (H.old_nodeDisjoint_other j hj)
      hxold hxother
  · exact Finset.disjoint_left.mp (H.rowInterval_nodeDisjoint_other j hj)
      hxrow hxother

/-- Every edge in the updated family is either an old column edge or a current
row edge.  This is the common `outsideFixedMeasure` subset hypothesis. -/
theorem replacement_familyEdgeSet_subset_union_rows
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    fullColumnFamilyEdgeSet
        (replaceFullColumn columns selected H.replacementPath) ⊆
      fullColumnFamilyEdgeSet columns ∪ rowEdges := by
  classical
  rw [fullColumnFamilyEdgeSet, fullColumnFamilyEdgeSet]
  intro e he
  rcases Finset.mem_biUnion.1 he with ⟨j, _hj, hej⟩
  by_cases hjsel : j = selected
  · subst j
    have hereplacement : e ∈ H.replacementPath.edgeSet := by
      simpa using hej
    rcases Finset.mem_union.1
        (H.replacementPath_edgeSet_subset_old_union_rowInterval
          hereplacement) with heold | herow
    · exact Finset.mem_union.2 <| Or.inl <|
        Finset.mem_biUnion.2
          ⟨selected, Finset.mem_univ selected, heold⟩
    · exact Finset.mem_union.2
        (Or.inr (H.rowInterval_edgeSet_subset_rows herow))
  · have hejold : e ∈ (columns j).edgeSet := by
      simpa [replaceFullColumn, hjsel] using hej
    exact Finset.mem_union.2 <| Or.inl <|
      Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hejold⟩

/-- Replacing the selected column introduces no new non-row column edge. -/
theorem replacement_nonRowEdgeSet_subset
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    fullColumnNonRowEdgeSet rowEdges
        (replaceFullColumn columns selected H.replacementPath) ⊆
      fullColumnNonRowEdgeSet rowEdges columns := by
  classical
  intro e he
  rcases Finset.mem_sdiff.1 he with ⟨henew, henotrow⟩
  rw [fullColumnFamilyEdgeSet] at henew
  rcases Finset.mem_biUnion.1 henew with ⟨j, _hj, hej⟩
  have heoldFamily : e ∈ fullColumnFamilyEdgeSet columns := by
    rw [fullColumnFamilyEdgeSet]
    by_cases hjsel : j = selected
    · subst j
      have hereplacement : e ∈ H.replacementPath.edgeSet := by
        simpa using hej
      have heparts := H.replacementPath_edgeSet_subset_parts hereplacement
      rcases Finset.mem_union.1 heparts with hpre_or_mid | hesuffix
      · rcases Finset.mem_union.1 hpre_or_mid with heprefix | herow
        · exact Finset.mem_biUnion.2
            ⟨selected, Finset.mem_univ selected,
              (columns selected).takeUntil_edgeSet_subset
                H.left_mem_column heprefix⟩
        · exact False.elim
            (henotrow (H.rowInterval_edgeSet_subset_rows herow))
      · exact Finset.mem_biUnion.2
          ⟨selected, Finset.mem_univ selected,
            (columns selected).dropUntil_edgeSet_subset
              H.right_mem_column hesuffix⟩
    · have hejold : e ∈ (columns j).edgeSet := by
        simpa [replaceFullColumn, hjsel] using hej
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hejold⟩
  exact Finset.mem_sdiff.2 ⟨heoldFamily, henotrow⟩

/-- A non-row edge of the deleted excursion belongs to the old family and is
absent from the whole replacement family. -/
theorem deleted_nonRow_edge_missing_from_family
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    ∃ e : Sym2 V,
      e ∈ fullColumnFamilyEdgeSet columns ∧
        e ∉ rowEdges ∧
          e ∉ fullColumnFamilyEdgeSet
            (replaceFullColumn columns selected H.replacementPath) := by
  classical
  rcases H.deleted_nonRow_edge with ⟨e, hedeleted, henotrow⟩
  have heoldSelected : e ∈ (columns selected).edgeSet :=
    (columns selected).segmentOfBefore_edgeSet_subset
      H.left_before_right hedeleted
  have heoldFamily : e ∈ fullColumnFamilyEdgeSet columns := by
    rw [fullColumnFamilyEdgeSet]
    exact Finset.mem_biUnion.2
      ⟨selected, Finset.mem_univ selected, heoldSelected⟩
  refine ⟨e, heoldFamily, henotrow, ?_⟩
  intro henewFamily
  rw [fullColumnFamilyEdgeSet] at henewFamily
  rcases Finset.mem_biUnion.1 henewFamily with ⟨j, _hj, hej⟩
  by_cases hjsel : j = selected
  · subst j
    have hereplacement : e ∈ H.replacementPath.edgeSet := by
      simpa using hej
    have heparts := H.replacementPath_edgeSet_subset_parts hereplacement
    rcases Finset.mem_union.1 heparts with hpre_or_mid | hesuffix
    · rcases Finset.mem_union.1 hpre_or_mid with heprefix | herow
      · exact Finset.disjoint_left.mp
          H.deletedSegment_edgeDisjoint_prefix hedeleted heprefix
      · exact henotrow (H.rowInterval_edgeSet_subset_rows herow)
    · exact Finset.disjoint_left.mp
        H.deletedSegment_edgeDisjoint_suffix hedeleted hesuffix
  · have hejold : e ∈ (columns j).edgeSet := by
      simpa [replaceFullColumn, hjsel] using hej
    have hedgeDisjoint :
        (columns selected).EdgeDisjoint (columns j) :=
      IndexedAuxiliaryPrefix.graphPath_edgeDisjoint_of_nodeDisjoint
        (H.old_nodeDisjoint_other j hjsel)
    exact Finset.disjoint_left.mp hedgeDisjoint heoldSelected hejold

/-- Set-level form of the missing-edge theorem. -/
theorem deleted_nonRow_edge_missing_after_replacement
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    ∃ e : Sym2 V,
      e ∈ fullColumnNonRowEdgeSet rowEdges columns ∧
        e ∉ fullColumnNonRowEdgeSet rowEdges
          (replaceFullColumn columns selected H.replacementPath) := by
  rcases H.deleted_nonRow_edge_missing_from_family with
    ⟨e, heold, henotrow, henew⟩
  exact ⟨e, Finset.mem_sdiff.2 ⟨heold, henotrow⟩, by
    intro he
    exact henew (Finset.mem_sdiff.1 he).1⟩

/-- The non-row column-edge measure strictly decreases after the concrete
cycle-erased hill replacement. -/
theorem replacement_nonRowEdgeMeasure_lt
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    fullColumnNonRowEdgeMeasure rowEdges
        (replaceFullColumn columns selected H.replacementPath) <
      fullColumnNonRowEdgeMeasure rowEdges columns := by
  rcases H.deleted_nonRow_edge_missing_from_family with
    ⟨e, heold, henotrow, henew⟩
  exact outsideFixedMeasure_lt
    H.replacement_familyEdgeSet_subset_union_rows
    heold henotrow henew

/-- Cardinality spelling of `replacement_nonRowEdgeMeasure_lt`. -/
theorem replacement_nonRowEdgeSet_card_lt
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    (fullColumnNonRowEdgeSet rowEdges
      (replaceFullColumn columns selected H.replacementPath)).card <
        (fullColumnNonRowEdgeSet rowEdges columns).card := by
  exact H.replacement_nonRowEdgeMeasure_lt

end FullColumnHillInput

/-- The proof-producing output of one full-column hill replacement. -/
structure FullColumnHillReplacement
    {rowEdges : Finset (Sym2 V)}
    {outsideLinkageVertices : Finset V}
    {lowerBoundary upperBoundary : GraphPath G}
    {columns : J → GraphPath G} {selected : J}
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) where
  path : GraphPath G
  source_eq : path.source = (columns selected).source
  target_eq : path.target = (columns selected).target
  lowerBoundary_contact :
    path.vertexSet ∩ lowerBoundary.vertexSet = {path.source}
  upperBoundary_contact :
    path.vertexSet ∩ upperBoundary.vertexSet = {path.target}
  avoids_outsideLinkage :
    Disjoint path.vertexSet outsideLinkageVertices
  nodeDisjoint_other :
    ∀ j : J, j ≠ selected → path.NodeDisjoint (columns j)
  edgeSet_subset_retained :
    path.edgeSet ⊆
      H.retainedPrefix.edgeSet ∪ H.rowInterval.edgeSet ∪ H.suffix.edgeSet
  nonRowMeasure_strict :
    fullColumnNonRowEdgeMeasure rowEdges
        (replaceFullColumn columns selected path) <
      fullColumnNonRowEdgeMeasure rowEdges columns

/-- Construct the full invariant-preserving, strictly descending hill
replacement. -/
noncomputable def FullColumnHillInput.toReplacement
    {rowEdges : Finset (Sym2 V)}
    {outsideLinkageVertices : Finset V}
    {lowerBoundary upperBoundary : GraphPath G}
    {columns : J → GraphPath G} {selected : J}
    (H : FullColumnHillInput rowEdges outsideLinkageVertices
      lowerBoundary upperBoundary columns selected) :
    FullColumnHillReplacement H where
  path := H.replacementPath
  source_eq := H.replacementPath_source
  target_eq := H.replacementPath_target
  lowerBoundary_contact := by
    simpa using H.replacementPath_lowerBoundary_contact
  upperBoundary_contact := by
    simpa using H.replacementPath_upperBoundary_contact
  avoids_outsideLinkage := H.replacementPath_avoids_outsideLinkage
  nodeDisjoint_other := H.replacementPath_nodeDisjoint_other
  edgeSet_subset_retained := H.replacementPath_edgeSet_subset_parts
  nonRowMeasure_strict := H.replacement_nonRowEdgeMeasure_lt

namespace AuxiliaryCorridor

variable {L : PerfectPathPacking G A B} {activeCount : ℕ}

/-- The finite union of all linkage paths outside a displayed corridor. -/
noncomputable def outsideLinkageVertexSet
    (C : AuxiliaryCorridor L activeCount) : Finset V :=
  Finset.univ.biUnion fun j : L.Index =>
    if j ∈ Set.range C.index then ∅ else (L.path j).vertexSet

/-- Pointwise avoidance of every outside linkage path is equivalent to
disjointness from their finite union. -/
theorem avoidsOutside_iff_disjoint_outsideLinkageVertexSet
    (C : AuxiliaryCorridor L activeCount) (P : GraphPath G) :
    C.AvoidsOutside P ↔
      Disjoint P.vertexSet C.outsideLinkageVertexSet := by
  classical
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro x hxP hxoutside
    rw [outsideLinkageVertexSet] at hxoutside
    rcases Finset.mem_biUnion.1 hxoutside with ⟨j, _hj, hxj⟩
    by_cases hjcorridor : j ∈ Set.range C.index
    · simp [hjcorridor] at hxj
    · exact Finset.disjoint_left.mp (h j hjcorridor) hxP
        (by simpa [hjcorridor] using hxj)
  · intro h j hjoutside
    rw [Finset.disjoint_left]
    intro x hxP hxj
    exact Finset.disjoint_left.mp h hxP (by
      rw [outsideLinkageVertexSet]
      exact Finset.mem_biUnion.2
        ⟨j, Finset.mem_univ j, by simpa [hjoutside] using hxj⟩)

/-- A path starting on one active corridor row and meeting a distinct active
row contains an edge outside the union of all active-row edges.  This is the
local support fact used to obtain the deleted edge in the hill measure. -/
theorem exists_edge_not_mem_activeEdgeSet_of_starts_hits_other
    (C : AuxiliaryCorridor L activeCount)
    {row lower : Fin activeCount} (hrowLower : row ≠ lower)
    (P : GraphPath G)
    (hsource : P.source ∈ (C.activePath row).vertexSet)
    (hhit : HitsGraphPath P (C.activePath lower)) :
    ∃ e : Sym2 V, e ∈ P.edgeSet ∧ e ∉ C.activeEdgeSet := by
  classical
  have hpairwise :
      Pairwise fun i j : Fin activeCount =>
        (C.activePath i).NodeDisjoint (C.activePath j) := by
    intro i j hij
    apply C.path_nodeDisjoint
    intro hpositions
    apply hij
    apply Fin.ext
    have hvalues := congrArg Fin.val hpositions
    simpa [AuxiliaryCorridor.activePosition] using hvalues
  simpa [AuxiliaryCorridor.activeEdgeSet] using
    (exists_edge_not_mem_pairwiseRowEdgeUnion_of_hits_other
      (rows := C.activePath) hpairwise hrowLower P hsource hhit)

end AuxiliaryCorridor

/-- A hill-replacement input attached directly to the invariant-preserving
`FullBoundaryColumnFamily` state from the corridor trace module.

Unlike `FullColumnHillInput`, this structure does not repeat any invariant of
the old column family.  It contains only the selected hill, the inserted row
interval, and the local facts about that interval. -/
structure FullBoundaryColumnHillInput
    {L : PerfectPathPacking G A B} {activeCount : ℕ}
    {C : AuxiliaryCorridor L activeCount}
    (rowEdges : Finset (Sym2 V))
    (F : FullBoundaryColumnFamily L activeCount J C)
    (selected : J) where
  left : V
  right : V
  left_mem_column : left ∈ (F.column selected).vertexSet
  right_mem_column : right ∈ (F.column selected).vertexSet
  left_before_right : (F.column selected).Before left right
  rowInterval : GraphPath G
  rowInterval_source : rowInterval.source = left
  rowInterval_target : rowInterval.target = right
  rowInterval_edgeSet_subset_rows : rowInterval.edgeSet ⊆ rowEdges
  rowInterval_avoids_lowerBoundary :
    Disjoint rowInterval.vertexSet
      (C.rowPath ⟨0, by omega⟩).vertexSet
  rowInterval_avoids_upperBoundary :
    Disjoint rowInterval.vertexSet
      (C.rowPath ⟨activeCount + 1, by omega⟩).vertexSet
  rowInterval_avoidsOutside : C.AvoidsOutside rowInterval
  rowInterval_nodeDisjoint_other :
    ∀ j : J, j ≠ selected →
      Disjoint rowInterval.vertexSet (F.column j).vertexSet
  deleted_nonRow_edge :
    ∃ e : Sym2 V,
      e ∈ ((F.column selected).segmentOfBefore left_before_right).edgeSet ∧
        e ∉ rowEdges

namespace FullBoundaryColumnHillInput

variable {L : PerfectPathPacking G A B} {activeCount : ℕ}
variable {C : AuxiliaryCorridor L activeCount}
variable {rowEdges : Finset (Sym2 V)}
variable {F : FullBoundaryColumnFamily L activeCount J C}
variable {selected : J}

/-- Forget the corridor wrapper and expose the finite support data consumed by
the generic cycle-erasure theorem. -/
noncomputable def toFullColumnHillInput
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    FullColumnHillInput rowEdges C.outsideLinkageVertexSet
      (C.rowPath ⟨0, by omega⟩)
      (C.rowPath ⟨activeCount + 1, by omega⟩)
      F.column selected where
  left := H.left
  right := H.right
  left_mem_column := H.left_mem_column
  right_mem_column := H.right_mem_column
  left_before_right := H.left_before_right
  rowInterval := H.rowInterval
  rowInterval_source := H.rowInterval_source
  rowInterval_target := H.rowInterval_target
  rowInterval_edgeSet_subset_rows := H.rowInterval_edgeSet_subset_rows
  old_lowerBoundary_contact := F.lower_contact selected
  old_upperBoundary_contact := F.upper_contact selected
  rowInterval_avoids_lowerBoundary :=
    H.rowInterval_avoids_lowerBoundary
  rowInterval_avoids_upperBoundary :=
    H.rowInterval_avoids_upperBoundary
  old_avoids_outsideLinkage :=
    (C.avoidsOutside_iff_disjoint_outsideLinkageVertexSet
      (F.column selected)).1 (F.avoidsOutside selected)
  rowInterval_avoids_outsideLinkage :=
    (C.avoidsOutside_iff_disjoint_outsideLinkageVertexSet
      H.rowInterval).1 H.rowInterval_avoidsOutside
  old_nodeDisjoint_other := by
    intro j hj
    exact F.pairwise_nodeDisjoint hj.symm
  rowInterval_nodeDisjoint_other := H.rowInterval_nodeDisjoint_other
  deleted_nonRow_edge := H.deleted_nonRow_edge

/-- The concrete cycle-erased replacement path for a corridor-family hill. -/
noncomputable def replacementPath
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    GraphPath G :=
  H.toFullColumnHillInput.replacementPath

@[simp] theorem replacementPath_source
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    H.replacementPath.source = (F.column selected).source :=
  H.toFullColumnHillInput.replacementPath_source

@[simp] theorem replacementPath_target
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    H.replacementPath.target = (F.column selected).target :=
  H.toFullColumnHillInput.replacementPath_target

/-- The corridor predicate, rather than merely its finite-union encoding, is
preserved by the cycle-erased replacement. -/
theorem replacementPath_avoidsOutside
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    C.AvoidsOutside H.replacementPath := by
  apply
    (C.avoidsOutside_iff_disjoint_outsideLinkageVertexSet
      H.replacementPath).2
  exact H.toFullColumnHillInput.replacementPath_avoids_outsideLinkage

/-- Update the full-column state itself.  Row hits are intentionally absent
from the construction: `column_hits_every_row` derives them from the preserved
boundary and outside-avoidance fields. -/
noncomputable def replacedFamily
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    FullBoundaryColumnFamily L activeCount J C where
  column := replaceFullColumn F.column selected H.replacementPath
  pairwise_nodeDisjoint := by
    intro i j hij
    by_cases hi : i = selected
    · subst i
      have hj : j ≠ selected := by
        intro h
        exact hij h.symm
      simpa [replaceFullColumn, hj] using
        H.toFullColumnHillInput.replacementPath_nodeDisjoint_other j hj
    · by_cases hj : j = selected
      · subst j
        have hrep :
            H.replacementPath.NodeDisjoint (F.column i) :=
          H.toFullColumnHillInput.replacementPath_nodeDisjoint_other i hi
        simpa [replaceFullColumn, hi] using
          GraphPath.nodeDisjoint_symm hrep
      · simpa [replaceFullColumn, hi, hj] using
          F.pairwise_nodeDisjoint hij
  lower_contact := by
    intro i
    by_cases hi : i = selected
    · subst i
      simpa [replacementPath] using
        H.toFullColumnHillInput.replacementPath_lowerBoundary_contact
    · simpa [replaceFullColumn, hi] using F.lower_contact i
  upper_contact := by
    intro i
    by_cases hi : i = selected
    · subst i
      simpa [replacementPath] using
        H.toFullColumnHillInput.replacementPath_upperBoundary_contact
    · simpa [replaceFullColumn, hi] using F.upper_contact i
  avoidsOutside := by
    intro i
    by_cases hi : i = selected
    · subst i
      simpa [replaceFullColumn] using H.replacementPath_avoidsOutside
    · simpa [replaceFullColumn, hi] using F.avoidsOutside i

/-- The replacement path meets every boundary and active row by the generic
no-skip theorem from `ChekuriChuzhoyTheoremB1CorridorTrace`. -/
theorem replacementPath_hits_every_row
    (H : FullBoundaryColumnHillInput rowEdges F selected)
    (q : Fin (activeCount + 2)) :
    HitsLinkagePath (L := L) H.replacementPath (C.index q) := by
  simpa [replacedFamily, replaceFullColumn] using
    H.replacedFamily.column_hits_every_row selected q

/-- Updating the corridor-family state strictly decreases the number of
column edges outside the active-row edge union. -/
theorem replacedFamily_nonRowMeasure_strict
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    fullColumnNonRowEdgeMeasure rowEdges H.replacedFamily.column <
      fullColumnNonRowEdgeMeasure rowEdges F.column := by
  simpa [replacedFamily, replacementPath] using
    H.toFullColumnHillInput.replacement_nonRowEdgeMeasure_lt

/-- Packaged proof-producing result for the corridor-family replacement. -/
noncomputable def toReplacement
    (H : FullBoundaryColumnHillInput rowEdges F selected) :
    FullColumnHillReplacement H.toFullColumnHillInput :=
  H.toFullColumnHillInput.toReplacement

end FullBoundaryColumnHillInput

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
