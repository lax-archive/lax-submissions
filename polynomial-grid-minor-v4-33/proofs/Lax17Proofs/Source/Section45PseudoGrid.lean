import Lax17Proofs.Source.Section42ActualPaths
import Lax17Proofs.Source.HappyClusterCore
import Lax17Proofs.Source.PathPackingSupportDegree
import Lax17Proofs.Source.Section45

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Sections 4.3--4.5 from a pseudo-grid slicing

This module builds the per-slice support graph used in the paper, applies
Theorem 4.11 there, and records a connected happy cluster with its retained
row indices.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

namespace PathSlicing

/-- The selected row segments after Section 4.3 cleanup. -/
noncomputable def cleanedRows
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    PathPacking G Finset.univ Finset.univ :=
  (sigma.sliceRowPacking i).restrictIndexSet O.rows

/-- The selected auxiliary paths after Section 4.3 cleanup. -/
noncomputable def cleanedAux
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    PathPacking G S T :=
  Q.restrictIndexSet O.paths

/-- The paper's graph `H'_i`: precisely the union of the cleaned row segments
and cleaned auxiliary paths in one slice. -/
noncomputable def cleanedSupportGraph
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    _root_.SimpleGraph V :=
  (sigma.cleanedRows Q i O).spanningGraph ⊔
    (sigma.cleanedAux Q i O).spanningGraph

noncomputable def cleanedRowsInSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    PathPacking (sigma.cleanedSupportGraph Q i O)
      Finset.univ Finset.univ :=
  (sigma.cleanedRows Q i O).inSpanningGraph.mapLe le_sup_left

noncomputable def cleanedAuxInSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    PathPacking (sigma.cleanedSupportGraph Q i O) S T :=
  (sigma.cleanedAux Q i O).inSpanningGraph.mapLe le_sup_right

@[simp] theorem cleanedRowsInSupport_path_vertexSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D)
    (r : (sigma.cleanedRowsInSupport Q i O).Index) :
    ((sigma.cleanedRowsInSupport Q i O).path r).vertexSet =
      ((sigma.sliceRowPacking i).path r.1).vertexSet := by
  simp [cleanedRowsInSupport, cleanedRows, PathPacking.mapLe]

@[simp] theorem cleanedRowsInSupport_path_source
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D)
    (r : (sigma.cleanedRowsInSupport Q i O).Index) :
    ((sigma.cleanedRowsInSupport Q i O).path r).source =
      ((sigma.sliceRowPacking i).path r.1).source := by
  rfl

@[simp] theorem cleanedRowsInSupport_path_target
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D)
    (r : (sigma.cleanedRowsInSupport Q i O).Index) :
    ((sigma.cleanedRowsInSupport Q i O).path r).target =
      ((sigma.sliceRowPacking i).path r.1).target := by
  rfl

@[simp] theorem cleanedAuxInSupport_path_vertexSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D)
    (q : (sigma.cleanedAuxInSupport Q i O).Index) :
    ((sigma.cleanedAuxInSupport Q i O).path q).vertexSet =
      (Q.path q.1).vertexSet := by
  simp [cleanedAuxInSupport, cleanedAux, PathPacking.mapLe]

@[simp] theorem cleanedRowsInSupport_card
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    (sigma.cleanedRowsInSupport Q i O).card = O.rows.card := by
  change (sigma.cleanedRows Q i O).card = O.rows.card
  exact PathPacking.restrictIndexSet_card _ _

@[simp] theorem cleanedAuxInSupport_card
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    (sigma.cleanedAuxInSupport Q i O).card = O.paths.card := by
  change (sigma.cleanedAux Q i O).card = O.paths.card
  exact PathPacking.restrictIndexSet_card _ _

/-- Restricting both sides of the cleaned intersecting pair and viewing them
in their exact support graph preserves all intersection degrees. -/
theorem cleaned_intersecting
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    (sigma.cleanedRowsInSupport Q i O).IntersectingPathSetPair
      (sigma.cleanedAuxInSupport Q i O)
      Finset.univ Finset.univ w D := by
  classical
  have hbase := O.actual_intersecting sigma Q i
  constructor
  · intro r _hr
    have hr := hbase.1 r.1 r.2
    have hcard :
        ((sigma.cleanedRowsInSupport Q i O).intersectingRightIndices
            (sigma.cleanedAuxInSupport Q i O) Finset.univ r).card =
          ((sigma.sliceRowPacking i).intersectingRightIndices
            Q O.paths r.1).card := by
      refine Finset.card_bij (fun q _hq => q.1) ?_ ?_ ?_
      · intro q hq
        rw [PathPacking.mem_intersectingRightIndices] at hq ⊢
        exact ⟨q.2, by simpa [PathPacking.PathsIntersect] using hq.2⟩
      · intro q _hq q' _hq' hqq'
        exact Subtype.ext hqq'
      · intro q hq
        rw [PathPacking.mem_intersectingRightIndices] at hq
        let q' : (sigma.cleanedAuxInSupport Q i O).Index :=
          ⟨q, hq.1⟩
        refine ⟨q', ?_, rfl⟩
        rw [PathPacking.mem_intersectingRightIndices]
        exact
          ⟨Finset.mem_univ _,
            by simpa [q', PathPacking.PathsIntersect] using hq.2⟩
    rw [hcard]
    exact hr
  · intro q _hq
    have hq := hbase.2 q.1 q.2
    have hcard :
        ((sigma.cleanedRowsInSupport Q i O).intersectingLeftIndices
            (sigma.cleanedAuxInSupport Q i O) Finset.univ q).card =
          ((sigma.sliceRowPacking i).intersectingLeftIndices
            Q O.rows q.1).card := by
      refine Finset.card_bij (fun r _hr => r.1) ?_ ?_ ?_
      · intro r hr
        rw [PathPacking.mem_intersectingLeftIndices] at hr ⊢
        exact ⟨r.2, by simpa [PathPacking.PathsIntersect] using hr.2⟩
      · intro r _hr r' _hr' hrr'
        exact Subtype.ext hrr'
      · intro r hr
        rw [PathPacking.mem_intersectingLeftIndices] at hr
        let r' : (sigma.cleanedRowsInSupport Q i O).Index :=
          ⟨r, hr.1⟩
        refine ⟨r', ?_, rfl⟩
        rw [PathPacking.mem_intersectingLeftIndices]
        exact
          ⟨Finset.mem_univ _,
            by simpa [r', PathPacking.PathsIntersect] using hr.2⟩
    rw [hcard]
    exact hq

/-! ## Theorem 4.11 in one cleaned slice -/

open Section44
open Section44.PathPacking

/-- The vertices used by all row segments and auxiliary paths assigned to one
slice.  The cleaned support graph is a subgraph on this set. -/
noncomputable def sliceSupportVertexSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T) (i : Fin M) :
    Finset V :=
  (sigma.sliceRowPacking i).vertexSet ∪
    (Q.restrictIndexSet (sigma.pathsInSlice Q i)).vertexSet

/-- The exact vertices of the cleaned row and auxiliary subfamilies. -/
noncomputable def cleanedSupportVertexSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    Finset V :=
  (sigma.cleanedRows Q i O).vertexSet ∪
    (sigma.cleanedAux Q i O).vertexSet

theorem cleanedSupportGraph_le
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    sigma.cleanedSupportGraph Q i O ≤ G :=
  sup_le
    (sigma.cleanedRows Q i O).spanningGraph_le
    (sigma.cleanedAux Q i O).spanningGraph_le

theorem cleanedSupportGraph_support_subset_sliceSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i w D) :
    (sigma.cleanedSupportGraph Q i O).support ⊆
      sigma.cleanedSupportVertexSet Q i O := by
  classical
  intro v hv
  change v ∈ sigma.cleanedSupportVertexSet Q i O
  rw [cleanedSupportVertexSet, Finset.mem_union]
  rw [_root_.SimpleGraph.mem_support] at hv
  rcases hv with ⟨z, hvz⟩
  rcases hvz with hvz | hvz
  · left
    rcases
        ((sigma.cleanedRows Q i O).spanningGraph_adj_iff_exists_path_edge).1
          hvz with ⟨⟨r, he⟩, _⟩
    apply (sigma.cleanedRows Q i O).mem_vertexSet.2
    exact ⟨r, (GraphPath.endpoints_mem_vertexSet_of_edgeSet _ he).1⟩
  · right
    rcases
        ((sigma.cleanedAux Q i O).spanningGraph_adj_iff_exists_path_edge).1
          hvz with ⟨⟨q, he⟩, _⟩
    exact
      (sigma.cleanedAux Q i O).mem_vertexSet.2
        ⟨q, (GraphPath.endpoints_mem_vertexSet_of_edgeSet _ he).1⟩

/-- The connected happy cluster selected in one slice, expressed using the
original row indices. -/
structure SliceHappyCoreData
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {ell Dhat : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat)) where
  cluster : Finset V
  rows : Finset R.Index
  cluster_connected : IsCluster G cluster
  cluster_subset_support : cluster ⊆ sigma.cleanedSupportVertexSet Q i O
  rows_subset : rows ⊆ O.rows
  row_card : Dhat ≤ rows.card
  row_path_contained :
    ∀ r ∈ rows,
      ((sigma.sliceRowPacking i).path r).vertexSet ⊆ cluster
  weak :
    WeakEdgeWellLinkedIn G cluster
      ((rows.image fun r => ((sigma.sliceRowPacking i).path r).source) ∪
        (rows.image fun r => ((sigma.sliceRowPacking i).path r).target))
      ell

/-- Chuzhoy--Tan Theorem 4.11 applied to one cleaned slice. -/
theorem exists_sliceHappyCoreData
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {ell Dhat : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat))
    (hell : 0 < ell) (hDhat : 0 < Dhat)
    (hscale : 8 * ell ≤ Dhat)
    (hpaths : O.paths.Nonempty) :
    Nonempty (sigma.SliceHappyCoreData Q i O) := by
  classical
  let Pclean := sigma.cleanedRowsInSupport Q i O
  let Qclean := sigma.cleanedAuxInSupport Q i O
  have hinter :
      Pclean.IntersectingPathSetPair Qclean Finset.univ Finset.univ
        (4 * ell) (2 * Dhat) := by
    simpa [Pclean, Qclean] using sigma.cleaned_intersecting Q i O
  let Output :=
    Classical.choice
      (Section44.PathPacking.theorem411
        Pclean Qclean Finset.univ Finset.univ hell hDhat hinter hscale)
  have hrowsPos : 0 < O.rows.card := by
    obtain ⟨q, hq⟩ := hpaths
    let qclean : Qclean.Index := ⟨q, hq⟩
    have hleft :
        2 * Dhat ≤
          (Pclean.intersectingLeftIndices Qclean Finset.univ qclean).card :=
      hinter.2 qclean (Finset.mem_univ _)
    have hbound :
        (Pclean.intersectingLeftIndices Qclean Finset.univ qclean).card ≤
          O.rows.card := by
      calc
        (Pclean.intersectingLeftIndices Qclean Finset.univ qclean).card
            ≤ (Finset.univ : Finset Pclean.Index).card :=
          Finset.card_le_card
            (PathPacking.intersectingLeftIndices_subset
              Pclean Qclean Finset.univ qclean)
        _ = O.rows.card := by
          change Pclean.card = O.rows.card
          simpa [Pclean] using sigma.cleanedRowsInSupport_card Q i O
    omega
  have hIpos :
      0 < (Finset.univ : Finset Pclean.Index).card := by
    change 0 < Pclean.card
    rw [show Pclean.card = O.rows.card by
      simpa [Pclean] using sigma.cleanedRowsInSupport_card Q i O]
    exact hrowsPos
  have hretainedPos : 0 < Output.retained.card := by
    have hquarter := Output.quarter_retained
    omega
  obtain ⟨r₀, hr₀⟩ := Finset.card_pos.mp hretainedPos
  obtain ⟨c, hr₀c⟩ := Output.retained_contained r₀ hr₀
  obtain ⟨Ccore, hCconnected, hCsub, hcontained, hweakCore⟩ :=
    Section44.exists_connected_happy_core
      Pclean Finset.univ (Output.cluster c) hell hDhat (Output.happy c)
  let Jclean := containedInCluster Pclean Finset.univ Ccore
  let rows : Finset R.Index := Jclean.image fun r => r.1
  have hvalInjective :
      Function.Injective (fun r : Pclean.Index => r.1) := by
    intro a b hab
    exact Subtype.ext hab
  have hrowsCard : rows.card = Jclean.card := by
    simpa [rows] using Finset.card_image_of_injective Jclean hvalInjective
  have hDrows : Dhat ≤ rows.card := by
    rw [hrowsCard]
    change Dhat ≤ (containedInCluster Pclean Finset.univ Ccore).card
    rw [hcontained]
    exact (Output.happy c).2
  have hrowsSubset : rows ⊆ O.rows := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
    exact r'.2
  have hrowContained :
      ∀ r ∈ rows,
        ((sigma.sliceRowPacking i).path r).vertexSet ⊆ Ccore := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
    have hr'data :=
      (mem_containedInCluster Pclean Finset.univ Ccore r').1 hr'J
    intro v hv
    exact hr'data.2 (by simpa [Pclean] using hv)
  have hterminalSubset :
      (rows.image fun r => ((sigma.sliceRowPacking i).path r).source) ∪
          (rows.image fun r => ((sigma.sliceRowPacking i).path r).target) ⊆
        endpointSetInCluster Pclean Finset.univ Ccore := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
      rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
      apply (mem_endpointSetInCluster Pclean Finset.univ Ccore _).2
      exact Or.inl ⟨r', hr'J, by simp [Pclean]⟩
    · rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
      rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
      apply (mem_endpointSetInCluster Pclean Finset.univ Ccore _).2
      exact Or.inr ⟨r', hr'J, by simp [Pclean]⟩
  have hweak :
      WeakEdgeWellLinkedIn (sigma.cleanedSupportGraph Q i O) Ccore
        ((rows.image fun r => ((sigma.sliceRowPacking i).path r).source) ∪
          (rows.image fun r => ((sigma.sliceRowPacking i).path r).target))
        ell :=
    WeakEdgeWellLinkedIn.mono_terminals hweakCore hterminalSubset
  have hcoreSupport :
      Ccore ⊆ sigma.cleanedSupportVertexSet Q i O := by
    have hr₀J : r₀ ∈ Jclean := by
      change r₀ ∈ containedInCluster Pclean Finset.univ Ccore
      rw [hcontained]
      exact hr₀c
    have htCore :
        (Pclean.path r₀).source ∈ Ccore :=
      ((mem_containedInCluster Pclean Finset.univ Ccore r₀).1 hr₀J).2
        (GraphPath.source_mem_vertexSet _)
    have htSupport :
        (Pclean.path r₀).source ∈ sigma.cleanedSupportVertexSet Q i O := by
      change (Pclean.path r₀).source ∈
        (sigma.cleanedSupportVertexSet Q i O : Finset V)
      rw [cleanedSupportVertexSet, Finset.mem_union]
      left
      apply (sigma.cleanedRows Q i O).mem_vertexSet.2
      refine ⟨r₀, ?_⟩
      change ((sigma.cleanedRows Q i O).path r₀).source ∈
        ((sigma.cleanedRows Q i O).path r₀).vertexSet
      exact GraphPath.source_mem_vertexSet _
    intro v hvC
    by_cases hvt : v = (Pclean.path r₀).source
    · simpa [hvt] using htSupport
    · have hreachInduced :
          ((sigma.cleanedSupportGraph Q i O).induce
              {x : V | x ∈ Ccore}).Reachable
            ⟨v, hvC⟩ ⟨(Pclean.path r₀).source, htCore⟩ :=
        hCconnected.preconnected _ _
      have hreach :
          (sigma.cleanedSupportGraph Q i O).Reachable
            v (Pclean.path r₀).source :=
        hreachInduced.map
          (_root_.SimpleGraph.Embedding.induce
            {x : V | x ∈ Ccore}).toHom
      exact
        sigma.cleanedSupportGraph_support_subset_sliceSupport Q i O
          (_root_.SimpleGraph.mem_support_of_reachable hvt hreach)
  refine ⟨{
    cluster := Ccore
    rows := rows
    cluster_connected :=
      IsCluster.mono_graph hCconnected
        (sigma.cleanedSupportGraph_le Q i O)
    cluster_subset_support := hcoreSupport
    rows_subset := hrowsSubset
    row_card := hDrows
    row_path_contained := hrowContained
    weak :=
      WeakEdgeWellLinkedIn.mono_graph hweak
        (sigma.cleanedSupportGraph_le Q i O)
  }⟩

/-! ## Disjointness of different cleaned slices -/

theorem cut_ne_of_mem_cleanedRows
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {ell Dhat : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat))
    (hell : 0 < ell) {r : R.Index} (hr : r ∈ O.rows) :
    sigma.cut r i.castSucc ≠ sigma.cut r i.succ := by
  classical
  have hpos :
      0 < (sigma.segmentIntersectingRightIndices Q i O.paths r).card := by
    have h := O.intersecting.1 r hr
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  rcases (sigma.mem_segmentIntersectingRightIndices Q i O.paths r q).1 hq with
    ⟨_hq, v, _hvQ, hvSlice⟩
  intro hcuts
  have hback :
      (R.path r).Before v (sigma.cut r i.castSucc) := by
    simpa [hcuts] using hvSlice.2.2.1
  exact hvSlice.2.2.2.1
    ((R.path r).before_antisymm hback hvSlice.2.1)

theorem sliceRowPath_source_ne_target_of_mem_cleanedRows
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {ell Dhat : ℕ}
    (O : sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat))
    (hell : 0 < ell) {r : R.Index} (hr : r ∈ O.rows) :
    ((sigma.sliceRowPacking i).path r).source ≠
      ((sigma.sliceRowPacking i).path r).target := by
  classical
  have hpos :
      0 < (sigma.segmentIntersectingRightIndices Q i O.paths r).card := by
    have h := O.intersecting.1 r hr
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  have hqO :
      q ∈ O.paths :=
    ((sigma.mem_segmentIntersectingRightIndices Q i O.paths r q).1 hq).1
  have hmeet :
      PathPacking.PathsIntersect
        ((sigma.sliceRowPacking i).path r) (Q.path q) :=
    (sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
      Q (O.paths_subset hqO)).1
      ((sigma.mem_segmentIntersectingRightIndices Q i O.paths r q).1 hq).2
  rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvRow, hvQ⟩
  have hvSlice :
      sigma.SliceInterior r i v :=
    (sigma.mem_pathsInSlice Q i q).1 (O.paths_subset hqO)
      hvQ (sigma.sliceRowPath_vertexSet_subset i r hvRow)
  intro hst
  have hvEq :=
    GraphPath.eq_source_of_source_eq_target_of_mem_vertexSet
      ((sigma.sliceRowPacking i).path r) hst hvRow
  exact hvSlice.2.2.2.1 (by
    simpa [sigma.sliceRowPath_source] using hvEq)

theorem sliceRowPath_source_injective
    (sigma : PathSlicing R M) (i : Fin M) :
    Function.Injective fun r : R.Index =>
      ((sigma.sliceRowPacking i).path r).source := by
  intro r s hrs
  change ((sigma.sliceRowPacking i).path r).source =
    ((sigma.sliceRowPacking i).path s).source at hrs
  by_contra hne
  exact Finset.disjoint_left.mp ((sigma.sliceRowPacking i).node_disjoint hne)
    (GraphPath.source_mem_vertexSet _)
    (by
      rw [hrs]
      exact GraphPath.source_mem_vertexSet _)

theorem sliceRowPath_target_injective
    (sigma : PathSlicing R M) (i : Fin M) :
    Function.Injective fun r : R.Index =>
      ((sigma.sliceRowPacking i).path r).target := by
  intro r s hrs
  change ((sigma.sliceRowPacking i).path r).target =
    ((sigma.sliceRowPacking i).path s).target at hrs
  by_contra hne
  exact Finset.disjoint_left.mp ((sigma.sliceRowPacking i).node_disjoint hne)
    (GraphPath.target_mem_vertexSet _)
    (by
      rw [hrs]
      exact GraphPath.target_mem_vertexSet _)

theorem sliceRowPath_disjoint_of_ne
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i ≠ j)
    {r s : R.Index}
    (hri : sigma.cut r i.castSucc ≠ sigma.cut r i.succ)
    (hsj : sigma.cut s j.castSucc ≠ sigma.cut s j.succ) :
    Disjoint ((sigma.sliceRowPacking i).path r).vertexSet
      ((sigma.sliceRowPacking j).path s).vertexSet := by
  classical
  by_cases hrs : r = s
  · subst s
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply
        (R.path r).segmentOfBefore_dropLast_disjoint_of_target_before_source
          (sigma.cut_monotone r (Fin.castSucc_le_succ i))
          (sigma.cut_monotone r (Fin.castSucc_le_succ j))
          (sigma.cut_monotone r (by
            apply Fin.mk_le_mk.2
            exact Nat.succ_le_iff.2 hij))
          hri
    · exact
        ((R.path r).segmentOfBefore_dropLast_disjoint_of_target_before_source
          (sigma.cut_monotone r (Fin.castSucc_le_succ j))
          (sigma.cut_monotone r (Fin.castSucc_le_succ i))
          (sigma.cut_monotone r (by
            apply Fin.mk_le_mk.2
            exact Nat.succ_le_iff.2 hji))
          (by simpa using hsj)).symm
  · exact (R.toPathPacking.node_disjoint hrs).mono
      (sigma.sliceRowPath_vertexSet_subset i r)
      (sigma.sliceRowPath_vertexSet_subset j s)

theorem not_mem_sliceRowPath_of_sliceInterior_ne
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i ≠ j)
    {r : R.Index} {v : V} (hvi : sigma.SliceInterior r i v) :
    v ∉ ((sigma.sliceRowPacking j).path r).vertexSet := by
  intro hvj
  have hvjClosed :
      v ∈ ((R.path r).segmentOfBefore
        (sigma.cut_monotone r (Fin.castSucc_le_succ j))).vertexSet :=
    ((R.path r).segmentOfBefore
      (sigma.cut_monotone r (Fin.castSucc_le_succ j)))
      |>.dropLast_vertexSet_subset hvj
  have hjLeft :
      (R.path r).Before (sigma.cut r j.castSucc) v :=
    (R.path r).before_of_mem_segmentOfBefore_left
      (sigma.cut_monotone r (Fin.castSucc_le_succ j)) hvjClosed
  have hjRight :
      (R.path r).Before v (sigma.cut r j.succ) :=
    (R.path r).before_of_mem_segmentOfBefore_right
      (sigma.cut_monotone r (Fin.castSucc_le_succ j)) hvjClosed
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hmiddle :
        (R.path r).Before (sigma.cut r i.succ)
          (sigma.cut r j.castSucc) :=
      sigma.cut_monotone r (by
        apply Fin.mk_le_mk.2
        exact Nat.succ_le_iff.2 hij)
    have hback :
        (R.path r).Before (sigma.cut r i.succ) v :=
      (R.path r).before_trans hmiddle hjLeft
    exact hvi.2.2.2.2
      ((R.path r).before_antisymm hvi.2.2.1 hback)
  · have hmiddle :
        (R.path r).Before (sigma.cut r j.succ)
          (sigma.cut r i.castSucc) :=
      sigma.cut_monotone r (by
        apply Fin.mk_le_mk.2
        exact Nat.succ_le_iff.2 hji)
    have hback :
        (R.path r).Before v (sigma.cut r i.castSucc) :=
      (R.path r).before_trans hjRight hmiddle
    exact hvi.2.2.2.1
      ((R.path r).before_antisymm hback hvi.2.1)

theorem cleanedSupportVertexSet_disjoint
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (hintersects : PathPackingIntersectsLinkage R Q)
    {i j : Fin M} (hij : i ≠ j) {ell Dhat : ℕ}
    (Oi : sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat))
    (Oj : sigma.SliceIntersectingSubfamilies Q j (4 * ell) (2 * Dhat))
    (hell : 0 < ell) :
    Disjoint (sigma.cleanedSupportVertexSet Q i Oi)
      (sigma.cleanedSupportVertexSet Q j Oj) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [cleanedSupportVertexSet, Finset.mem_union] at hvi hvj
  rcases hvi with hri | hqi <;> rcases hvj with hrj | hqj
  · rcases (sigma.cleanedRows Q i Oi).mem_vertexSet.1 hri with
      ⟨r, hvr⟩
    rcases (sigma.cleanedRows Q j Oj).mem_vertexSet.1 hrj with
      ⟨s, hvs⟩
    exact Finset.disjoint_left.mp
      (sigma.sliceRowPath_disjoint_of_ne hij
        (sigma.cut_ne_of_mem_cleanedRows Q i Oi hell r.2)
        (sigma.cut_ne_of_mem_cleanedRows Q j Oj hell s.2))
      hvr hvs
  · rcases (sigma.cleanedRows Q i Oi).mem_vertexSet.1 hri with
      ⟨r, hvr⟩
    rcases (sigma.cleanedAux Q j Oj).mem_vertexSet.1 hqj with
      ⟨q, hvq⟩
    have hvSlice :
        sigma.SliceInterior r.1 j v :=
      (sigma.mem_pathsInSlice Q j q.1).1
        (Oj.paths_subset q.2) hvq
        (sigma.sliceRowPath_vertexSet_subset i r.1 hvr)
    exact (sigma.not_mem_sliceRowPath_of_sliceInterior_ne
      (Ne.symm hij) hvSlice) hvr
  · rcases (sigma.cleanedAux Q i Oi).mem_vertexSet.1 hqi with
      ⟨q, hvq⟩
    rcases (sigma.cleanedRows Q j Oj).mem_vertexSet.1 hrj with
      ⟨r, hvr⟩
    have hvSlice :
        sigma.SliceInterior r.1 i v :=
      (sigma.mem_pathsInSlice Q i q.1).1
        (Oi.paths_subset q.2) hvq
        (sigma.sliceRowPath_vertexSet_subset j r.1 hvr)
    exact (sigma.not_mem_sliceRowPath_of_sliceInterior_ne hij hvSlice) hvr
  · rcases (sigma.cleanedAux Q i Oi).mem_vertexSet.1 hqi with
      ⟨q, hvq⟩
    rcases (sigma.cleanedAux Q j Oj).mem_vertexSet.1 hqj with
      ⟨q', hvq'⟩
    have hqq' : q.1 ≠ q'.1 := by
      intro heq
      have hqBoth :
          q.1 ∈ sigma.pathsInSlice Q i ∩ sigma.pathsInSlice Q j :=
        Finset.mem_inter.2
          ⟨Oi.paths_subset q.2, by simpa [heq] using Oj.paths_subset q'.2⟩
      exact Finset.disjoint_left.mp
        (sigma.pathsInSlice_disjoint Q hintersects hij)
        (Finset.mem_inter.1 hqBoth).1 (Finset.mem_inter.1 hqBoth).2
    exact Finset.disjoint_left.mp (Q.node_disjoint hqq') hvq hvq'

/-! ## Row connectors between selected slices -/

theorem sliceRowPath_target_before_source_of_lt
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (r : R.Index)
    (hne : sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    (R.path r).Before ((sigma.sliceRowPacking i).path r).target
      ((sigma.sliceRowPacking j).path r).source := by
  let closed :=
    (R.path r).segmentOfBefore
      (sigma.cut_monotone r (Fin.castSucc_le_succ i))
  have hclosedNe : closed.source ≠ closed.target := by
    simpa [closed] using hne
  have htargetRight :
      (R.path r).Before closed.penultimate (sigma.cut r i.succ) := by
    apply (R.path r).before_of_mem_segmentOfBefore_right
      (sigma.cut_monotone r (Fin.castSucc_le_succ i))
    exact closed.penultimate_mem_vertexSet hclosedNe
  have hrightLeft :
      (R.path r).Before (sigma.cut r i.succ)
        (sigma.cut r j.castSucc) :=
    sigma.cut_monotone r (by
      apply Fin.mk_le_mk.2
      exact Nat.succ_le_iff.2 hij)
  simpa [sliceRowPacking, sliceRowPath, closed] using
    (R.path r).before_trans htargetRight hrightLeft

/-- The portion of row `r` connecting slice `i` to a later slice `j`. -/
noncomputable def rowGapPath
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (r : R.Index)
    (hne : sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    GraphPath G :=
  (R.path r).segmentOfBefore
    (sigma.sliceRowPath_target_before_source_of_lt hij r hne)

@[simp] theorem rowGapPath_source
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (r : R.Index)
    (hne : sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    (sigma.rowGapPath hij r hne).source =
      ((sigma.sliceRowPacking i).path r).target := rfl

@[simp] theorem rowGapPath_target
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (r : R.Index)
    (hne : sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    (sigma.rowGapPath hij r hne).target =
      ((sigma.sliceRowPacking j).path r).source := rfl

theorem rowGapPath_vertexSet_subset
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (r : R.Index)
    (hne : sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    (sigma.rowGapPath hij r hne).vertexSet ⊆ (R.path r).vertexSet :=
  (R.path r).segmentOfBefore_vertexSet_subset _

theorem sliceRowPath_source_before_of_mem
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) {v : V}
    (hv : v ∈ ((sigma.sliceRowPacking i).path r).vertexSet) :
    (R.path r).Before ((sigma.sliceRowPacking i).path r).source v := by
  apply (R.path r).before_of_mem_segmentOfBefore_left
    (sigma.cut_monotone r (Fin.castSucc_le_succ i))
  exact
    (((R.path r).segmentOfBefore
      (sigma.cut_monotone r (Fin.castSucc_le_succ i)))
      |>.dropLast_vertexSet_subset hv)

set_option maxHeartbeats 800000 in
theorem before_sliceRowPath_target_of_mem
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index)
    (hcut : sigma.cut r i.castSucc ≠ sigma.cut r i.succ)
    {v : V} (hv : v ∈ ((sigma.sliceRowPacking i).path r).vertexSet) :
    (R.path r).Before v ((sigma.sliceRowPacking i).path r).target := by
  classical
  let hclosed :=
    sigma.cut_monotone r (Fin.castSucc_le_succ i)
  let closed := (R.path r).segmentOfBefore hclosed
  have hclosedNe : closed.source ≠ closed.target := by
    simpa [closed, hclosed] using hcut
  have hvClosed : v ∈ closed.vertexSet :=
    closed.dropLast_vertexSet_subset hv
  have hpClosed : closed.penultimate ∈ closed.vertexSet :=
    closed.penultimate_mem_vertexSet hclosedNe
  have hvR : v ∈ (R.path r).vertexSet :=
    (R.path r).segmentOfBefore_vertexSet_subset hclosed hvClosed
  have hpR : closed.penultimate ∈ (R.path r).vertexSet :=
    (R.path r).segmentOfBefore_vertexSet_subset hclosed hpClosed
  have hvr :
      (R.path r).vertexIndex v <
        (R.path r).vertexIndex (sigma.cut r i.succ) := by
    have hvle :=
      ((R.path r).before_iff_vertexIndex_le).1
        ((R.path r).before_of_mem_segmentOfBefore_right hclosed hvClosed) |>.2.2
    have hvne : v ≠ sigma.cut r i.succ := by
      intro hvEq
      exact closed.target_not_mem_dropLast_vertexSet hclosedNe (by
        simpa [closed, hclosed, hvEq] using hv)
    have hidxne :
        (R.path r).vertexIndex v ≠
          (R.path r).vertexIndex (sigma.cut r i.succ) := by
      intro heq
      exact hvne ((R.path r).before_antisymm
        (((R.path r).before_iff_vertexIndex_le).2
          ⟨hvR, sigma.cut_mem r i.succ, by omega⟩)
        (((R.path r).before_iff_vertexIndex_le).2
          ⟨sigma.cut_mem r i.succ, hvR, by omega⟩))
    omega
  have hedgeClosed :
      s(closed.penultimate, sigma.cut r i.succ) ∈ closed.edgeSet := by
    apply List.mem_toFinset.mpr
    simpa [GraphPath.edgeSet, GraphPath.penultimate, closed, hclosed] using
      closed.walk.mk_penultimate_end_mem_edges
        (closed.walk_not_nil_of_source_ne_target hclosedNe)
  have hedgeR :
      s(closed.penultimate, sigma.cut r i.succ) ∈ (R.path r).edgeSet :=
    (R.path r).segmentOfBefore_edgeSet_subset hclosed hedgeClosed
  have hrightLe :
      (R.path r).vertexIndex (sigma.cut r i.succ) ≤
        (R.path r).vertexIndex closed.penultimate + 1 :=
    (R.path r).edge_vertexIndex_le_succ (by
      simpa only [Sym2.eq_swap] using hedgeR)
  have hpBeforeRight :
      (R.path r).vertexIndex closed.penultimate <
        (R.path r).vertexIndex (sigma.cut r i.succ) := by
    have hle :=
      ((R.path r).before_iff_vertexIndex_le).1
        ((R.path r).before_of_mem_segmentOfBefore_right hclosed hpClosed) |>.2.2
    have hpne : closed.penultimate ≠ sigma.cut r i.succ := by
      intro heq
      exact closed.target_not_mem_dropLast_vertexSet hclosedNe (by
        have hpDrop : closed.penultimate ∈ closed.dropLast.vertexSet :=
          GraphPath.target_mem_vertexSet _
        simpa [closed, hclosed, heq] using hpDrop)
    have hidxne :
        (R.path r).vertexIndex closed.penultimate ≠
          (R.path r).vertexIndex (sigma.cut r i.succ) := by
      intro heq
      exact hpne ((R.path r).before_antisymm
        (((R.path r).before_iff_vertexIndex_le).2
          ⟨hpR, sigma.cut_mem r i.succ, by omega⟩)
        (((R.path r).before_iff_vertexIndex_le).2
          ⟨sigma.cut_mem r i.succ, hpR, by omega⟩))
    omega
  apply (R.path r).before_iff_vertexIndex_le.2
  refine ⟨hvR, ?_, ?_⟩
  · simpa [sliceRowPacking, sliceRowPath, closed, hclosed] using hpR
  · change (R.path r).vertexIndex v ≤
      (R.path r).vertexIndex closed.penultimate
    omega

theorem mem_sliceRowPath_of_sliceInterior
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) {v : V}
    (hv : sigma.SliceInterior r i v) :
    v ∈ ((sigma.sliceRowPacking i).path r).vertexSet := by
  let hcut := sigma.cut_monotone r (Fin.castSucc_le_succ i)
  have hcutsNe :
      sigma.cut r i.castSucc ≠ sigma.cut r i.succ := by
    intro heq
    have hback :
        (R.path r).Before v (sigma.cut r i.castSucc) := by
      simpa [heq] using hv.2.2.1
    exact hv.2.2.2.1
      ((R.path r).before_antisymm hback hv.2.1)
  have hvClosed :
      v ∈ ((R.path r).segmentOfBefore hcut).vertexSet :=
    (R.path r).mem_segmentOfBefore_of_before_of_before
      hcut hv.2.1 hv.2.2.1
  rcases
      (((R.path r).segmentOfBefore hcut)
        |>.mem_vertexSet_iff_mem_dropLast_or_eq_target
          (by simpa [hcut] using hcutsNe) v).1 hvClosed with
    hvDrop | hvRight
  · simpa [sliceRowPacking, sliceRowPath, hcut] using hvDrop
  · exact (hv.2.2.2.2 (by simpa [hcut] using hvRight)).elim

/-- A row connector meets the exact support of any selected slice outside its
open interval only at a connector endpoint. -/
theorem rowGapPath_internallyDisjoint_cleanedSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    {i j : Fin M} (hij : i < j) (r : R.Index)
    (hneI : sigma.cut r i.castSucc ≠ sigma.cut r i.succ)
    (k : Fin M) {ell Dhat : ℕ}
    (Ok : sigma.SliceIntersectingSubfamilies Q k (4 * ell) (2 * Dhat))
    (hell : 0 < ell) (hk : k ≤ i ∨ j ≤ k) :
    (sigma.rowGapPath hij r hneI).InternallyDisjointFromSet
      (sigma.cleanedSupportVertexSet Q k Ok) := by
  classical
  intro v hvGap hvSupport
  have hgapLeft :
      (R.path r).Before ((sigma.rowGapPath hij r hneI).source) v :=
    (R.path r).before_of_mem_segmentOfBefore_left
      (sigma.sliceRowPath_target_before_source_of_lt hij r hneI) hvGap
  have hgapRight :
      (R.path r).Before v ((sigma.rowGapPath hij r hneI).target) :=
    (R.path r).before_of_mem_segmentOfBefore_right
      (sigma.sliceRowPath_target_before_source_of_lt hij r hneI) hvGap
  rw [cleanedSupportVertexSet, Finset.mem_union] at hvSupport
  rcases hvSupport with hvRows | hvAux
  · rcases (sigma.cleanedRows Q k Ok).mem_vertexSet.1 hvRows with
      ⟨s, hvs⟩
    by_cases hrs : r = s.1
    · subst r
      have hcutK :=
        sigma.cut_ne_of_mem_cleanedRows Q k Ok hell s.2
      rcases hk with hki | hjk
      · have hvBefore :
            (R.path s.1).Before v
              ((sigma.rowGapPath hij s.1 hneI).source) := by
          rcases lt_or_eq_of_le hki with hki | rfl
          · have htoSource :=
              sigma.sliceRowPath_target_before_source_of_lt hki s.1 hcutK
            have hsourceToTarget :
                (R.path s.1).Before
                  ((sigma.sliceRowPacking i).path s.1).source
                  ((sigma.rowGapPath hij s.1 hneI).source) := by
              simpa using sigma.sliceRowPath_source_before_of_mem i s.1
                (GraphPath.target_mem_vertexSet
                  ((sigma.sliceRowPacking i).path s.1))
            exact (R.path s.1).before_trans
              ((R.path s.1).before_trans
                (sigma.before_sliceRowPath_target_of_mem k s.1 hcutK hvs)
                htoSource)
              hsourceToTarget
          · simpa using
              sigma.before_sliceRowPath_target_of_mem k s.1 hcutK hvs
        exact Or.inl
          ((R.path s.1).before_antisymm hvBefore hgapLeft)
      · have htargetBefore :
            (R.path s.1).Before
              ((sigma.rowGapPath hij s.1 hneI).target) v := by
          have hcuts :
              (R.path s.1).Before (sigma.cut s.1 j.castSucc)
                (sigma.cut s.1 k.castSucc) :=
            sigma.cut_monotone s.1 (by
              apply Fin.mk_le_mk.2
              exact hjk)
          exact (R.path s.1).before_trans hcuts
            (sigma.sliceRowPath_source_before_of_mem k s.1 hvs)
        exact Or.inr
          ((R.path s.1).before_antisymm hgapRight htargetBefore)
    · exact False.elim
        (Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrs)
          (sigma.rowGapPath_vertexSet_subset hij r hneI hvGap)
          (sigma.sliceRowPath_vertexSet_subset k s.1 hvs))
  · rcases (sigma.cleanedAux Q k Ok).mem_vertexSet.1 hvAux with
      ⟨q, hvq⟩
    have hvSlice :
        sigma.SliceInterior r k v :=
      (sigma.mem_pathsInSlice Q k q.1).1 (Ok.paths_subset q.2)
        hvq (sigma.rowGapPath_vertexSet_subset hij r hneI hvGap)
    rcases hk with hki | hjk
    · have hcutK :
          sigma.cut r k.castSucc ≠ sigma.cut r k.succ := by
        intro hcuts
        have hback :
            (R.path r).Before v (sigma.cut r k.castSucc) := by
          simpa [hcuts] using hvSlice.2.2.1
        exact hvSlice.2.2.2.1
          ((R.path r).before_antisymm hback hvSlice.2.1)
      have hvRow :
          v ∈ ((sigma.sliceRowPacking k).path r).vertexSet :=
        sigma.mem_sliceRowPath_of_sliceInterior k r hvSlice
      have hvBefore :
          (R.path r).Before v
            ((sigma.rowGapPath hij r hneI).source) := by
        rcases lt_or_eq_of_le hki with hki | rfl
        · have htoSource :=
            sigma.sliceRowPath_target_before_source_of_lt hki r hcutK
          have hsourceToTarget :
              (R.path r).Before
                ((sigma.sliceRowPacking i).path r).source
                ((sigma.rowGapPath hij r hneI).source) := by
            simpa using sigma.sliceRowPath_source_before_of_mem i r
              (GraphPath.target_mem_vertexSet
                ((sigma.sliceRowPacking i).path r))
          exact (R.path r).before_trans
            ((R.path r).before_trans
              (sigma.before_sliceRowPath_target_of_mem k r hcutK hvRow)
              htoSource)
            hsourceToTarget
        · simpa using
            sigma.before_sliceRowPath_target_of_mem k r hcutK hvRow
      exact Or.inl ((R.path r).before_antisymm hvBefore hgapLeft)
    · have htargetBefore :
          (R.path r).Before
            ((sigma.rowGapPath hij r hneI).target) v := by
        have hcuts :
            (R.path r).Before (sigma.cut r j.castSucc)
              (sigma.cut r k.castSucc) :=
          sigma.cut_monotone r (by
            apply Fin.mk_le_mk.2
            exact hjk)
        exact (R.path r).before_trans hcuts hvSlice.2.1
      exact Or.inr
        ((R.path r).before_antisymm hgapRight htargetBefore)

theorem rowGapPath_disjoint_of_ordered
    (sigma : PathSlicing R M)
    {i j k m : Fin M} (hij : i < j) (hkm : k < m)
    (hjk : j ≤ k) {r s : R.Index}
    (hneI : sigma.cut r i.castSucc ≠ sigma.cut r i.succ)
    (hneK : sigma.cut s k.castSucc ≠ sigma.cut s k.succ)
    (hsliceK :
      ((sigma.sliceRowPacking k).path s).source ≠
        ((sigma.sliceRowPacking k).path s).target) :
    Disjoint (sigma.rowGapPath hij r hneI).vertexSet
      (sigma.rowGapPath hkm s hneK).vertexSet := by
  classical
  by_cases hrs : r = s
  · subst s
    have htargetSource :
        (R.path r).Before
          (sigma.rowGapPath hij r hneI).target
          (sigma.rowGapPath hkm r hneK).source := by
      have hlefts :
          (R.path r).Before (sigma.cut r j.castSucc)
            (sigma.cut r k.castSucc) :=
        sigma.cut_monotone r (by
          apply Fin.mk_le_mk.2
          exact hjk)
      have hinside :
          (R.path r).Before
            ((sigma.sliceRowPacking k).path r).source
            ((sigma.sliceRowPacking k).path r).target :=
        sigma.sliceRowPath_source_before_of_mem k r
          (GraphPath.target_mem_vertexSet _)
      exact (R.path r).before_trans hlefts hinside
    have hstrict :
        (sigma.rowGapPath hij r hneI).target ≠
          (sigma.rowGapPath hkm r hneK).source := by
      intro heq
      have heq' :
          ((sigma.sliceRowPacking j).path r).source =
            ((sigma.sliceRowPacking k).path r).target := by
        simpa using heq
      have hback :
          (R.path r).Before
            ((sigma.sliceRowPacking k).path r).target
            ((sigma.sliceRowPacking k).path r).source := by
        have hlefts :
            (R.path r).Before (sigma.cut r j.castSucc)
              (sigma.cut r k.castSucc) :=
          sigma.cut_monotone r (by
            apply Fin.mk_le_mk.2
            exact hjk)
        have hlefts' :
            (R.path r).Before
              ((sigma.sliceRowPacking j).path r).source
              ((sigma.sliceRowPacking k).path r).source := by
          simpa using hlefts
        rw [heq'] at hlefts'
        exact hlefts'
      exact hsliceK ((R.path r).before_antisymm
        (sigma.sliceRowPath_source_before_of_mem k r
          (GraphPath.target_mem_vertexSet _)) hback)
    exact
      (R.path r).segmentOfBefore_disjoint_of_strict_target_before_source
        (sigma.sliceRowPath_target_before_source_of_lt hij r hneI)
        (sigma.sliceRowPath_target_before_source_of_lt hkm r hneK)
        htargetSource hstrict
  · exact (R.toPathPacking.node_disjoint hrs).mono
      (sigma.rowGapPath_vertexSet_subset hij r hneI)
      (sigma.rowGapPath_vertexSet_subset hkm s hneK)

/-- The row portions joining two selected slices, restricted to a chosen set
of common retained rows. -/
noncomputable def rowGapPacking
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (I : Finset R.Index)
    (hne : ∀ r ∈ I,
      sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    PerfectPathPacking G
      (I.image fun r => ((sigma.sliceRowPacking i).path r).target)
      (I.image fun r => ((sigma.sliceRowPacking j).path r).source) where
  Index := {r : R.Index // r ∈ I}
  path := fun r => sigma.rowGapPath hij r.1 (hne r.1 r.2)
  connects := by
    intro r
    exact Or.inl
      ⟨Finset.mem_image.2 ⟨r.1, r.2, rfl⟩,
        Finset.mem_image.2 ⟨r.1, r.2, rfl⟩⟩
  node_disjoint := by
    intro r s hrs
    apply (R.toPathPacking.node_disjoint (fun h =>
      hrs (Subtype.ext h))).mono
    · exact sigma.rowGapPath_vertexSet_subset hij r.1 (hne r.1 r.2)
    · exact sigma.rowGapPath_vertexSet_subset hij s.1 (hne s.1 s.2)
  source_mem := by
    intro r
    exact Finset.mem_image.2 ⟨r.1, r.2, by simp⟩
  target_mem := by
    intro r
    exact Finset.mem_image.2 ⟨r.1, r.2, by simp⟩
  source_bijective := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      apply sigma.sliceRowPath_target_injective i
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
      refine ⟨⟨r, hr⟩, ?_⟩
      apply Subtype.ext
      simp
  target_bijective := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      apply sigma.sliceRowPath_source_injective j
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
      refine ⟨⟨r, hr⟩, ?_⟩
      apply Subtype.ext
      simp

@[simp] theorem rowGapPacking_card
    (sigma : PathSlicing R M) {i j : Fin M} (hij : i < j)
    (I : Finset R.Index)
    (hne : ∀ r ∈ I,
      sigma.cut r i.castSucc ≠ sigma.cut r i.succ) :
    (sigma.rowGapPacking hij I hne).card = I.card := by
  simp [rowGapPacking, PerfectPathPacking.card]

/-! ## Uniform data over all slices -/

theorem segmentIntersectingLeftIndices_card_eq_metRows
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) {q : Q.Index} (hq : q ∈ sigma.pathsInSlice Q i) :
    (sigma.segmentIntersectingLeftIndices Q i
        (Finset.univ : Finset R.Index) q).card =
      ((Finset.univ : Finset R.Index).filter fun r =>
        ¬ Disjoint (Q.path q).vertexSet (R.path r).vertexSet).card := by
  classical
  congr 1
  ext r
  rw [sigma.mem_segmentIntersectingLeftIndices]
  simp only [Finset.mem_univ, true_and, Finset.mem_filter]
  rw [sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
    Q hq]
  constructor
  · intro h hd
    exact h hd.symm
  · intro h hd
    exact h hd.symm

/-- The cleanup output and one connected happy core in every slice. -/
structure SlicedHappyCores
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (ell Dhat : ℕ) where
  cleaned :
    ∀ i : Fin M,
      sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat)
  core :
    ∀ i : Fin M,
      sigma.SliceHappyCoreData Q i (cleaned i)

/-- Sections 4.3 and 4.4, uniformly over all slices. -/
theorem exists_slicedHappyCores
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    {ell Dhat sliceWidth : ℕ}
    (hell : 0 < ell) (hDhat : 0 < Dhat)
    (hsliceWidth : 0 < sliceWidth)
    (hscale : 8 * ell ≤ Dhat)
    (hwidth : sigma.WidthAtLeast Q sliceWidth)
    (hdense :
      ∀ q : Q.Index,
        4 * Dhat ≤
          ((Finset.univ : Finset R.Index).filter fun r =>
            ¬ Disjoint (Q.path q).vertexSet (R.path r).vertexSet).card)
    (hcleanup :
      2 * (Fintype.card R.Index) * (4 * ell) ≤
        (2 * Dhat) * sliceWidth) :
    Nonempty (sigma.SlicedHappyCores Q ell Dhat) := by
  classical
  let cleaned :
      ∀ i : Fin M,
        sigma.SliceIntersectingSubfamilies Q i (4 * ell) (2 * Dhat) :=
    fun i =>
      sigma.exists_slice_intersecting_subfamilies Q i
        (w := 4 * ell) (D := 2 * Dhat)
        (by positivity)
        (by
          intro q hq
          have hqDense := hdense q
          rw [sigma.segmentIntersectingLeftIndices_card_eq_metRows Q i hq]
          have heq : 2 * (2 * Dhat) = 4 * Dhat := by ring
          rw [heq]
          exact hqDense)
        (by
          calc
            2 * Fintype.card R.Index * (4 * ell)
                ≤ (2 * Dhat) * sliceWidth := hcleanup
            _ ≤ (2 * Dhat) * (sigma.pathsInSlice Q i).card :=
              Nat.mul_le_mul_left (2 * Dhat) (hwidth i))
  let core :
      ∀ i : Fin M,
        sigma.SliceHappyCoreData Q i (cleaned i) :=
    fun i =>
      Classical.choice <| sigma.exists_sliceHappyCoreData Q i (cleaned i)
        hell hDhat hscale (by
          have hhalf := (cleaned i).half_paths
          have hslice := hwidth i
          have hpos : 0 < (sigma.pathsInSlice Q i).card :=
            hsliceWidth.trans_le hslice
          exact Finset.card_pos.mp (by omega))
  exact ⟨{ cleaned := cleaned, core := core }⟩

namespace SlicedHappyCores

variable {ell Dhat : ℕ}
variable {sigma : PathSlicing R M} {Q : PathPacking G S T}

/-- Retained rows reindexed by the paper's common `Fin N`, with
`N = R.card`. -/
noncomputable def sliceRows
    (D : sigma.SlicedHappyCores Q ell Dhat) (i : Fin M) :
    Finset (Fin R.card) :=
  (D.core i).rows.image R.finIndexEquiv.symm

noncomputable def leftEndpoint
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) (r : Fin R.card) : V :=
  ((sigma.sliceRowPacking i).path (R.finIndexEquiv r)).source

noncomputable def rightEndpoint
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) (r : Fin R.card) : V :=
  ((sigma.sliceRowPacking i).path (R.finIndexEquiv r)).target

theorem mem_sliceRows_iff
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) (r : Fin R.card) :
    r ∈ D.sliceRows i ↔ R.finIndexEquiv r ∈ (D.core i).rows := by
  classical
  constructor
  · intro hr
    rcases Finset.mem_image.1 hr with ⟨s, hs, rfl⟩
    simpa using hs
  · intro hr
    exact Finset.mem_image.2
      ⟨R.finIndexEquiv r, hr, R.finIndexEquiv.symm_apply_apply r⟩

@[simp] theorem sliceRows_card
    (D : sigma.SlicedHappyCores Q ell Dhat) (i : Fin M) :
    (D.sliceRows i).card = (D.core i).rows.card := by
  classical
  exact Finset.card_image_of_injective _
    (R.finIndexEquiv.symm).injective

theorem leftEndpoint_injective
    (D : sigma.SlicedHappyCores Q ell Dhat) (i : Fin M) :
    Function.Injective (D.leftEndpoint i) :=
  (sigma.sliceRowPath_source_injective i).comp R.finIndexEquiv.injective

theorem rightEndpoint_injective
    (D : sigma.SlicedHappyCores Q ell Dhat) (i : Fin M) :
    Function.Injective (D.rightEndpoint i) :=
  (sigma.sliceRowPath_target_injective i).comp R.finIndexEquiv.injective

theorem leftEndpoint_mem
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) {r : Fin R.card} (hr : r ∈ D.sliceRows i) :
    D.leftEndpoint i r ∈ (D.core i).cluster :=
  (D.core i).row_path_contained _ ((D.mem_sliceRows_iff i r).1 hr)
    (GraphPath.source_mem_vertexSet _)

theorem rightEndpoint_mem
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) {r : Fin R.card} (hr : r ∈ D.sliceRows i) :
    D.rightEndpoint i r ∈ (D.core i).cluster :=
  (D.core i).row_path_contained _ ((D.mem_sliceRows_iff i r).1 hr)
    (GraphPath.target_mem_vertexSet _)

theorem endpoint_union_weak
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (i : Fin M) (L Rset : Finset (Fin R.card))
    (hL : L ⊆ D.sliceRows i) (hR : Rset ⊆ D.sliceRows i) :
    WeakEdgeWellLinkedIn G (D.core i).cluster
      (L.image (D.leftEndpoint i) ∪
        Rset.image (D.rightEndpoint i)) ell := by
  apply WeakEdgeWellLinkedIn.mono_terminals (D.core i).weak
  intro v hv
  rcases Finset.mem_union.1 hv with hv | hv
  · rw [Finset.mem_union]
    apply Or.inl
    rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.2
      ⟨R.finIndexEquiv r,
        (D.mem_sliceRows_iff i r).1 (hL hr), rfl⟩
  · rw [Finset.mem_union]
    apply Or.inr
    rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.2
      ⟨R.finIndexEquiv r,
        (D.mem_sliceRows_iff i r).1 (hR hr), rfl⟩

theorem cluster_disjoint
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (hintersects : PathPackingIntersectsLinkage R Q)
    (hell : 0 < ell) {i j : Fin M} (hij : i ≠ j) :
    Disjoint (D.core i).cluster (D.core j).cluster :=
  (sigma.cleanedSupportVertexSet_disjoint Q hintersects hij
      (D.cleaned i) (D.cleaned j) hell).mono
    (D.core i).cluster_subset_support
    (D.core j).cluster_subset_support

/-- Sections 4.3--4.5 assembled from the actual sliced pseudo-grid paths. -/
theorem section45Input_of_slicedHappyCores
    (D : sigma.SlicedHappyCores Q ell Dhat)
    (hintersects : PathPackingIntersectsLinkage R Q)
    (hell : 0 < ell) (hscale : 8 * ell ≤ Dhat)
    (hN : 3 * ell ≤ R.card)
    (hDsq : 4 * R.card * ell ≤ Dhat ^ 2)
    (hlarge : 2 * R.card * ell ≤ Dhat * M) :
    Nonempty (Section45.Section45Input G R.card M Dhat ell) := by
  classical
  have hselectedLt :
      ∀ {l : List (Fin M)} (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell))
        {i j : Fin ell}, i < j →
          Section45.selectedIndex l hlen i <
            Section45.selectedIndex l hlen j := by
    intro l hlen hchain i j hij
    have hltChain : l.IsChain (fun a b : Fin M => a < b) :=
      hchain.imp (fun _ _ h => h.1)
    have hp : l.Pairwise (fun a b : Fin M => a < b) :=
      hltChain.pairwise
    exact hp.rel_get_of_lt (by
      change (⟨i.1, by simp [hlen, i.2]⟩ : Fin l.length) <
        ⟨j.1, by simp [hlen, j.2]⟩
      exact hij)
  have hselectedLe :
      ∀ {l : List (Fin M)} (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell))
        {i j : Fin ell}, i ≤ j →
          Section45.selectedIndex l hlen i ≤
            Section45.selectedIndex l hlen j := by
    intro l hlen hchain i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact (hselectedLt hlen hchain hij).le
    · exact le_rfl
  have hrowCard :
      ∀ i : Fin M, Dhat ≤ (D.sliceRows i).card := by
    intro i
    rw [D.sliceRows_card]
    exact (D.core i).row_card
  obtain
      ⟨firstRows, gapRows, hfirstSubset, hfirstCard,
        hgapLeft, hgapRight, hgapCard⟩ :=
    Section45.exists_paperRows D.sliceRows hell (by omega) hrowCard
  let leftRows :=
    fun (l : List (Fin M)) (hlen : l.length = ell)
      (hchain : l.IsChain
        (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell) =>
      Section45.paperLeftRows firstRows gapRows l hlen hchain i
  let rightRows :=
    fun (l : List (Fin M)) (hlen : l.length = ell)
      (hchain : l.IsChain
        (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell) =>
      Section45.paperRightRows firstRows gapRows l hlen hchain i
  have hleftSubset :
      ∀ (l : List (Fin M)) (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell),
        leftRows l hlen hchain i ⊆
          D.sliceRows (Section45.selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · have h0lt : 0 < ell := by simpa [h0] using i.2
      have hi : i = ⟨0, h0lt⟩ := Fin.ext h0
      simpa [leftRows, Section45.paperLeftRows, h0, hi] using
        hfirstSubset l hlen hchain
    · let k : Fin ell := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < ell := by
        dsimp [k]
        omega
      have hnext : (⟨k.1 + 1, hk⟩ : Fin ell) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa [leftRows, Section45.paperLeftRows, h0, k, hk, hnext] using
        hgapRight l hlen hchain k hk
  have hrightSubset :
      ∀ (l : List (Fin M)) (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell),
        rightRows l hlen hchain i ⊆
          D.sliceRows (Section45.selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < ell
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hgapLeft l hlen hchain i hi
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hleftSubset l hlen hchain i
  have hleftCard :
      ∀ (l : List (Fin M)) (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell),
        (leftRows l hlen hchain i).card = ell := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · simpa [leftRows, Section45.paperLeftRows, h0] using
        hfirstCard l hlen hchain
    · let k : Fin ell := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < ell := by
        dsimp [k]
        omega
      simpa [leftRows, Section45.paperLeftRows, h0, k, hk] using
        hgapCard l hlen hchain k hk
  have hrightCard :
      ∀ (l : List (Fin M)) (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell)) (i : Fin ell),
        (rightRows l hlen hchain i).card = ell := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < ell
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hgapCard l hlen hchain i hi
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hleftCard l hlen hchain i
  let connector :
      ∀ (l : List (Fin M)) (hlen : l.length = ell)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel D.sliceRows ell))
        (i : Fin ell) (hi : i.1 + 1 < ell),
        PerfectPathPacking G
          ((rightRows l hlen hchain i).image
            (D.rightEndpoint (Section45.selectedIndex l hlen i)))
          ((leftRows l hlen hchain ⟨i.1 + 1, hi⟩).image
            (D.leftEndpoint
              (Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩))) :=
    fun l hlen hchain i hi =>
      let a := Section45.selectedIndex l hlen i
      let b := Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩
      let hlt : a < b :=
        (Section45.selectedIndex_chain_succ hlen hchain i hi).1
      let IFin := gapRows l hlen hchain i hi
      let IBase : Finset R.Index := IFin.image R.finIndexEquiv
      let hne : ∀ r ∈ IBase,
          sigma.cut r a.castSucc ≠ sigma.cut r a.succ := by
        intro r hr
        rcases Finset.mem_image.1 hr with ⟨rfin, hrfin, rfl⟩
        apply sigma.cut_ne_of_mem_cleanedRows Q a (D.cleaned a) hell
        apply (D.core a).rows_subset
        apply (D.mem_sliceRows_iff a rfin).1
        exact hgapLeft l hlen hchain i hi hrfin
      (sigma.rowGapPacking hlt IBase hne).copyTerminals
        (by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_image.1 hv with ⟨r, hr, hrv⟩
            rcases Finset.mem_image.1 hr with ⟨rfin, hrfin, rfl⟩
            have hrRight : rfin ∈ rightRows l hlen hchain i := by
              simpa [rightRows, Section45.paperRightRows, hi] using hrfin
            exact Finset.mem_image.2
              ⟨rfin, hrRight, by simpa [rightEndpoint] using hrv⟩
          · intro hv
            rcases Finset.mem_image.1 hv with ⟨rfin, hrfin, hrv⟩
            have hrGap : rfin ∈ IFin := by
              simpa [rightRows, Section45.paperRightRows, hi] using hrfin
            exact Finset.mem_image.2
              ⟨R.finIndexEquiv rfin,
                Finset.mem_image.2 ⟨rfin, hrGap, rfl⟩,
                by simpa [rightEndpoint] using hrv⟩)
        (by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_image.1 hv with ⟨r, hr, hrv⟩
            rcases Finset.mem_image.1 hr with ⟨rfin, hrfin, rfl⟩
            have hrLeft :
                rfin ∈ leftRows l hlen hchain ⟨i.1 + 1, hi⟩ := by
              simp only [leftRows, Section45.paperLeftRows]
              simpa using hrfin
            exact Finset.mem_image.2
              ⟨rfin, hrLeft, by simpa [leftEndpoint] using hrv⟩
          · intro hv
            rcases Finset.mem_image.1 hv with ⟨rfin, hrfin, hrv⟩
            have hrGap : rfin ∈ IFin := by
              simp only [leftRows, Section45.paperLeftRows] at hrfin
              simpa using hrfin
            exact Finset.mem_image.2
              ⟨R.finIndexEquiv rfin,
                Finset.mem_image.2 ⟨rfin, hrGap, rfl⟩,
                by simpa [leftEndpoint] using hrv⟩)
  let _ := connector
  exact ⟨by
    refine {
      sliceRows := D.sliceRows
      width_pos := hell
      N_large := hN
      D_square := hDsq
      large := hlarge
      row_card := hrowCard
      cluster := fun l hlen hchain i =>
        (D.core (Section45.selectedIndex l hlen i)).cluster
      cluster_connected := ?_
      cluster_disjoint := ?_
      left := fun l hlen hchain i =>
        (leftRows l hlen hchain i).image
          (D.leftEndpoint (Section45.selectedIndex l hlen i))
      right := fun l hlen hchain i =>
        (rightRows l hlen hchain i).image
          (D.rightEndpoint (Section45.selectedIndex l hlen i))
      left_subset_cluster := ?_
      right_subset_cluster := ?_
      left_right_disjoint := ?_
      left_card := ?_
      right_card := ?_
      connector := connector
      connector_card := ?_
      connector_internally_disjoint_clusters := ?_
      connector_mutually_nodeDisjoint := ?_
      nails_weakWellLinked := ?_
    }
    · intro l hlen hchain i
      exact (D.core (Section45.selectedIndex l hlen i)).cluster_connected
    · intro l hlen hchain i j hij
      apply D.cluster_disjoint hintersects hell
      intro heq
      have hmono :
          Function.Injective (Section45.selectedIndex l hlen) := by
        intro x y hxy
        by_cases hxy' : x = y
        · exact hxy'
        · rcases lt_or_gt_of_ne hxy' with hlt | hgt
          · exact False.elim
              ((ne_of_lt (hselectedLt hlen hchain hlt))
                hxy)
          · exact False.elim
              ((ne_of_lt (hselectedLt hlen hchain hgt))
                hxy.symm)
      exact hij (hmono heq)
    · intro l hlen hchain i v hv
      rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
      exact D.leftEndpoint_mem _ (hleftSubset l hlen hchain i hr)
    · intro l hlen hchain i v hv
      rcases Finset.mem_image.1 hv with ⟨r, hr, rfl⟩
      exact D.rightEndpoint_mem _ (hrightSubset l hlen hchain i hr)
    · intro l hlen hchain i
      rw [Finset.disjoint_left]
      intro v hvL hvR
      rcases Finset.mem_image.1 hvL with ⟨r, hr, hrv⟩
      rcases Finset.mem_image.1 hvR with ⟨s, hs, hsv⟩
      by_cases hrs : r = s
      · subst s
        have hne :=
          sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
            Q (Section45.selectedIndex l hlen i)
            (D.cleaned (Section45.selectedIndex l hlen i)) hell
            ((D.core _).rows_subset
              ((D.mem_sliceRows_iff _ r).1
                (hleftSubset l hlen hchain i hr)))
        exact hne (hrv.trans hsv.symm)
      · have hbaseNe : R.finIndexEquiv r ≠ R.finIndexEquiv s :=
          fun h => hrs (R.finIndexEquiv.injective h)
        have hvSource : v ∈
            ((sigma.sliceRowPacking
              (Section45.selectedIndex l hlen i)).path
              (R.finIndexEquiv r)).vertexSet := by
          change
            ((sigma.sliceRowPacking
              (Section45.selectedIndex l hlen i)).path
              (R.finIndexEquiv r)).source = v at hrv
          rw [← hrv]
          exact GraphPath.source_mem_vertexSet _
        have hvTarget : v ∈
            ((sigma.sliceRowPacking
              (Section45.selectedIndex l hlen i)).path
              (R.finIndexEquiv s)).vertexSet := by
          change
            ((sigma.sliceRowPacking
              (Section45.selectedIndex l hlen i)).path
              (R.finIndexEquiv s)).target = v at hsv
          rw [← hsv]
          exact GraphPath.target_mem_vertexSet _
        exact Finset.disjoint_left.mp
          ((sigma.sliceRowPacking
            (Section45.selectedIndex l hlen i)).node_disjoint hbaseNe)
          hvSource hvTarget
    · intro l hlen hchain i
      rw [Finset.card_image_of_injective]
      · exact hleftCard l hlen hchain i
      · exact D.leftEndpoint_injective _
    · intro l hlen hchain i
      rw [Finset.card_image_of_injective]
      · exact hrightCard l hlen hchain i
      · exact D.rightEndpoint_injective _
    · intro l hlen hchain i hi
      rw [(connector l hlen hchain i hi).card_eq_left_card]
      rw [Finset.card_image_of_injective]
      · exact hrightCard l hlen hchain i
      · exact D.rightEndpoint_injective _
    · intro l hlen hchain i hi j
      intro p v hvp hvC
      -- Each connector path is a row gap, and every selected cluster lies
      -- outside the open interval between consecutive selected indices.
      dsimp [connector] at p hvp
      let a := Section45.selectedIndex l hlen i
      let b := Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩
      let k := Section45.selectedIndex l hlen j
      have hab : a < b :=
        (Section45.selectedIndex_chain_succ hlen hchain i hi).1
      have houtside : k ≤ a ∨ b ≤ k := by
        by_cases hji : j ≤ i
        · exact Or.inl (hselectedLe hlen hchain hji)
        · have hijpos : i.1 + 1 ≤ j.1 := by omega
          exact Or.inr (hselectedLe hlen hchain hijpos)
      rcases Finset.mem_image.1 p.2 with ⟨pfin, hpfin, hpeq⟩
      have hpCoreFin :
          R.finIndexEquiv pfin ∈ (D.core a).rows :=
        (D.mem_sliceRows_iff a pfin).1
          (hgapLeft l hlen hchain i hi hpfin)
      have hpCore : p.1 ∈ (D.core a).rows := by
        rw [← hpeq]
        exact hpCoreFin
      apply
        (sigma.rowGapPath_internallyDisjoint_cleanedSupport
          Q hab p.1
          (by
            apply sigma.cut_ne_of_mem_cleanedRows Q a (D.cleaned a) hell
            exact (D.core a).rows_subset hpCore)
          k (D.cleaned k) hell houtside)
      · simpa [connector, a, b] using hvp
      · exact (D.core k).cluster_subset_support hvC
    · intro l hlen hchain i j hi hj hij
      -- Ordered row gaps on one linkage are disjoint; different linkage rows
      -- are disjoint because the original linkage is a node packing.
      intro p q
      dsimp [connector] at p q
      rcases Finset.mem_image.1 p.2 with ⟨pfin, hpfin, hpeq⟩
      rcases Finset.mem_image.1 q.2 with ⟨qfin, hqfin, hqeq⟩
      have hpCoreFin :
          R.finIndexEquiv pfin ∈
            (D.core (Section45.selectedIndex l hlen i)).rows :=
        (D.mem_sliceRows_iff _ pfin).1
          (hgapLeft l hlen hchain i hi hpfin)
      have hqCoreFin :
          R.finIndexEquiv qfin ∈
            (D.core (Section45.selectedIndex l hlen j)).rows :=
        (D.mem_sliceRows_iff _ qfin).1
          (hgapLeft l hlen hchain j hj hqfin)
      have hpCore :
          p.1 ∈ (D.core (Section45.selectedIndex l hlen i)).rows := by
        rw [← hpeq]
        exact hpCoreFin
      have hqCore :
          q.1 ∈ (D.core (Section45.selectedIndex l hlen j)).rows := by
        rw [← hqeq]
        exact hqCoreFin
      rcases lt_or_gt_of_ne hij with hijlt | hjlt
      · apply sigma.rowGapPath_disjoint_of_ordered
          (Section45.selectedIndex_chain_succ hlen hchain i hi).1
          (Section45.selectedIndex_chain_succ hlen hchain j hj).1
          (hselectedLe hlen hchain
            (Fin.mk_le_mk.2 (Nat.succ_le_iff.2 hijlt)))
          (by
            apply sigma.cut_ne_of_mem_cleanedRows Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hpCore)
          (by
            apply sigma.cut_ne_of_mem_cleanedRows Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hqCore)
          (by
            apply sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
              Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hqCore)
      · exact (sigma.rowGapPath_disjoint_of_ordered
          (Section45.selectedIndex_chain_succ hlen hchain j hj).1
          (Section45.selectedIndex_chain_succ hlen hchain i hi).1
          (hselectedLe hlen hchain
            (Fin.mk_le_mk.2 (Nat.succ_le_iff.2 hjlt)))
          (by
            apply sigma.cut_ne_of_mem_cleanedRows Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hqCore)
          (by
            apply sigma.cut_ne_of_mem_cleanedRows Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hpCore)
          (by
            apply sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
              Q _ (D.cleaned _) hell
            exact (D.core _).rows_subset hpCore)).symm
    · intro l hlen hchain i
      exact D.endpoint_union_weak _ _ _
        (hleftSubset l hlen hchain i)
        (hrightSubset l hlen hchain i)
  ⟩

end SlicedHappyCores

end PathSlicing

namespace Section45

theorem selectedIndex_lt_of_lt
    {N M w : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = w)
    (hchain : l.IsChain (LargeOverlapRel sliceRows w))
    {i j : Fin w} (hij : i < j) :
    selectedIndex l hlen i < selectedIndex l hlen j := by
  have hltChain : l.IsChain (fun a b : Fin M => a < b) :=
    hchain.imp (fun _ _ h => h.1)
  have hp : l.Pairwise (fun a b : Fin M => a < b) :=
    hltChain.pairwise
  exact hp.rel_get_of_lt (by
    change (⟨i.1, by simp [hlen, i.2]⟩ : Fin l.length) <
      ⟨j.1, by simp [hlen, j.2]⟩
    exact hij)

theorem selectedIndex_le_of_le
    {N M w : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = w)
    (hchain : l.IsChain (LargeOverlapRel sliceRows w))
    {i j : Fin w} (hij : i ≤ j) :
    selectedIndex l hlen i ≤ selectedIndex l hlen j := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact (selectedIndex_lt_of_lt hlen hchain hij).le
  · exact le_rfl

end Section45

end SimpleGraph

end Lax17Proofs
