import Lax17Proofs.Source.Exponent8.Observation54Cleanup

namespace Lax17Proofs

/-!
# The cleaned type-two slice of Observation 5.4

This module packages the graph used after additive Lemma 4.8 and strengthened
Claim 5.3.  Starting from one localized slice, it keeps a chosen auxiliary
subfamily, deletes all other auxiliary edges, and then restricts to the exact
support of the retained canonical rows.

All graph ambient types are exact support subtypes.  Consequently
`SpansVertices` has its intended source-faithful meaning and no isolated
ambient vertices are introduced.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : _root_.SimpleGraph W}
variable {Abar Bbar Sbar Tbar : Finset W}
variable {Rbar : PerfectPathPacking H Abar Bbar}
variable {Qbar : PathPacking H Sbar Tbar}
variable {M : ℕ}

namespace PathSlicing

/-- A selected auxiliary subfamily, transferred into the raw graph of one
slice.  Its index type is exactly the selected set of original `Qbar`
indices. -/
noncomputable def selectedSliceAuxInRaw
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hgood : good ⊆ Qset) :
    PathPacking (sliceRawGraph sigma Qbar i Qset)
      Finset.univ Finset.univ where
  Index := {q : Qbar.Index // q ∈ good}
  path := fun q =>
    (((sliceAux Qbar Qset).inSpanningGraph.mapLe le_sup_right).path
      ⟨q.1, hgood q.2⟩)
  connects := by
    intro q
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro q q' hqq'
    exact
      ((sliceAux Qbar Qset).inSpanningGraph.mapLe le_sup_right).node_disjoint
        (by
          intro h
          apply hqq'
          apply Subtype.ext
          exact congrArg
            (fun z : {x : Qbar.Index // x ∈ Qset} => z.1) h)

@[simp] theorem selectedSliceAuxInRaw_card
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hgood : good ⊆ Qset) :
    (selectedSliceAuxInRaw sigma i Qset good hgood).card = good.card := by
  classical
  simp [selectedSliceAuxInRaw, PathPacking.card]

@[simp] theorem selectedSliceAuxInRaw_path_vertexSet
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hgood : good ⊆ Qset)
    (q : (selectedSliceAuxInRaw sigma i Qset good hgood).Index) :
    ((selectedSliceAuxInRaw sigma i Qset good hgood).path q).vertexSet =
      (Qbar.path q.1).vertexSet := by
  change
    (((((sliceAux Qbar Qset).path ⟨q.1, hgood q.2⟩).transfer
      (sliceAux Qbar Qset).spanningGraph _).mapLe _).vertexSet) =
        (Qbar.path q.1).vertexSet
  rw [GraphPath.mapLe_vertexSet, GraphPath.transfer_vertexSet]
  rfl

theorem selectedSliceAuxInRaw_staysIn_support
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (selectedSliceAuxInRaw sigma i Qset good hgood).StaysIn
      (sliceSupportVertexSetFor sigma Qbar i Qset) := by
  intro q v hv
  have hvQ : v ∈ (Qbar.path q.1).vertexSet := by
    simpa using hv
  rcases Rbar.toPathPacking.mem_vertexSet.1 (hspan v) with ⟨r, hvR⟩
  have hqSlice : q.1 ∈ sigma.pathsInSlice Qbar i :=
    hQset (hgood q.2)
  have hvSlice :
      v ∈ (sigma.sliceRowPath i r).vertexSet :=
    mem_sliceRowPath_of_mem_pathsInSlice sigma Qbar hqSlice hvQ hvR
  exact sliceRows_stayIn_support sigma Qbar i Qset r hvSlice

/-- The selected auxiliary paths in the exact slice-support subtype. -/
noncomputable def selectedSliceAuxInSupport
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    PathPacking (sliceSupportGraph sigma Qbar i Qset)
      Finset.univ Finset.univ :=
  PathPacking.induceUniv
    (selectedSliceAuxInRaw sigma i Qset good hgood)
    (sliceSupportVertexSetFor sigma Qbar i Qset)
    (selectedSliceAuxInRaw_staysIn_support
      sigma i Qset good hspan hQset hgood)

@[simp] theorem selectedSliceAuxInSupport_card
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (selectedSliceAuxInSupport
      sigma i Qset good hspan hQset hgood).card = good.card := by
  change
    (PathPacking.induceUniv
      (selectedSliceAuxInRaw sigma i Qset good hgood)
      (sliceSupportVertexSetFor sigma Qbar i Qset)
      (selectedSliceAuxInRaw_staysIn_support
        sigma i Qset good hspan hQset hgood)).card = good.card
  rw [PathPacking.induceUniv_card]
  exact selectedSliceAuxInRaw_card sigma i Qset good hgood

/-- The slice graph after all unwanted auxiliary paths have been deleted.
The vertex subtype is deliberately unchanged at this stage; all of its
vertices are still spanned by the canonical sliced rows. -/
noncomputable def auxiliaryDeletedSliceGraph
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    _root_.SimpleGraph
      (SliceSupportVertex sigma Qbar i Qset) :=
  (sliceRowsInSupport sigma Qbar i Qset).toPathPacking.spanningGraph ⊔
    (selectedSliceAuxInSupport
      sigma i Qset good hspan hQset hgood).spanningGraph

theorem auxiliaryDeletedSliceGraph_le
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    auxiliaryDeletedSliceGraph
        sigma i Qset good hspan hQset hgood ≤
      sliceSupportGraph sigma Qbar i Qset :=
  sup_le
    (sliceRowsInSupport sigma Qbar i Qset).toPathPacking.spanningGraph_le
    (selectedSliceAuxInSupport
      sigma i Qset good hspan hQset hgood).spanningGraph_le

/-- Canonical sliced rows in the auxiliary-deleted graph. -/
noncomputable def auxiliaryDeletedSliceRows
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    PerfectPathPacking
      (auxiliaryDeletedSliceGraph
        sigma i Qset good hspan hQset hgood)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Qbar i Qset)
        (sliceLeftBoundary_subset_support sigma Qbar i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Qbar i Qset)
        (sliceRightBoundary_subset_support sigma Qbar i Qset)) :=
  (sliceRowsInSupport sigma Qbar i Qset).inSpanningGraph.mapLe le_sup_left

/-- Selected auxiliary paths in the auxiliary-deleted graph. -/
noncomputable def auxiliaryDeletedSliceAux
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    PathPacking
      (auxiliaryDeletedSliceGraph
        sigma i Qset good hspan hQset hgood)
      Finset.univ Finset.univ :=
  (selectedSliceAuxInSupport
    sigma i Qset good hspan hQset hgood).inSpanningGraph.mapLe le_sup_right

theorem auxiliaryDeletedSliceRows_isUniqueLinkage
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (auxiliaryDeletedSliceRows
      sigma i Qset good hunique.1 hQset hgood).IsUniqueLinkage := by
  let rows0 := sliceRowsInSupport sigma Qbar i Qset
  let rowsSmall :=
    auxiliaryDeletedSliceRows
      sigma i Qset good hunique.1 hQset hgood
  let hKL :=
    auxiliaryDeletedSliceGraph_le
      sigma i Qset good hunique.1 hQset hgood
  have hrows0Unique :
      rows0.IsUniqueLinkage :=
    sliceSupport_isUniqueLinkage sigma Qbar i Qset hunique hQset
  have hspanSmall : rowsSmall.SpansVertices := by
    intro z
    have hz : z ∈ rows0.toPathPacking.vertexSet :=
      hrows0Unique.1 z
    rcases rows0.toPathPacking.mem_vertexSet.1 hz with ⟨r, hzr⟩
    apply rowsSmall.toPathPacking.mem_vertexSet.2
    refine ⟨r, ?_⟩
    change
      z ∈ ((rows0.inSpanningGraph.path r).mapLe le_sup_left).vertexSet
    rw [GraphPath.mapLe_vertexSet,
      PerfectPathPacking.inSpanningGraph_path_vertexSet]
    exact hzr
  have hcanonical :
      (rowsSmall.mapLe hKL).toPathPacking.edgeSet =
        rows0.toPathPacking.edgeSet := by
    change
      (((rows0.inSpanningGraph.mapLe le_sup_left).mapLe hKL).toPathPacking.edgeSet) =
        rows0.toPathPacking.edgeSet
    rw [PerfectPathPacking.mapLe_edgeSet,
      PerfectPathPacking.mapLe_edgeSet]
    exact inSpanningGraph_edgeSet_eq_local rows0
  have hmappedUnique :
      (rowsSmall.mapLe hKL).IsUniqueLinkage := by
    constructor
    · intro z
      have hz : z ∈ rows0.toPathPacking.vertexSet :=
        hrows0Unique.1 z
      rcases rows0.toPathPacking.mem_vertexSet.1 hz with ⟨r, hzr⟩
      apply
        (rowsSmall.mapLe hKL).toPathPacking.mem_vertexSet.2
      refine ⟨r, ?_⟩
      change
        z ∈
          ((((rows0.inSpanningGraph.path r).mapLe le_sup_left).mapLe hKL).vertexSet)
      rw [GraphPath.mapLe_vertexSet, GraphPath.mapLe_vertexSet,
        PerfectPathPacking.inSpanningGraph_path_vertexSet]
      exact hzr
    · intro L
      calc
        L.toPathPacking.edgeSet = rows0.toPathPacking.edgeSet :=
          hrows0Unique.2 L
        _ = (rowsSmall.mapLe hKL).toPathPacking.edgeSet :=
          hcanonical.symm
  exact uniqueLinkage_preserved_by_auxiliary_deletion
    hKL rowsSmall hspanSmall hmappedUnique

theorem auxiliaryDeletedSliceRows_path_vertexSet
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (r : (auxiliaryDeletedSliceRows
      sigma i Qset good hspan hQset hgood).Index)
    (z : SliceSupportVertex sigma Qbar i Qset) :
    z ∈ ((auxiliaryDeletedSliceRows
      sigma i Qset good hspan hQset hgood).path r).vertexSet ↔
      z.1 ∈ (sigma.sliceRowPath i r).vertexSet := by
  change
    z ∈
        (((sliceRowsInSupport sigma Qbar i Qset).inSpanningGraph.path r).mapLe
          le_sup_left).vertexSet ↔
      z.1 ∈ (sigma.sliceRowPath i r).vertexSet
  rw [GraphPath.mapLe_vertexSet,
    PerfectPathPacking.inSpanningGraph_path_vertexSet]
  change
    z ∈
        (((sliceRowsInRawGraph sigma Qbar i Qset).path r).induce
          (sliceSupportVertexSetFor sigma Qbar i Qset)
          (sliceRowsInRawGraph_stayIn_support
            sigma Qbar i Qset r)).vertexSet ↔
      z.1 ∈ (sigma.sliceRowPath i r).vertexSet
  rw [GraphPath.mem_induce_vertexSet]
  simp [sliceRowsInRawGraph, PerfectPathPacking.mapLe,
    PathPacking.mapLe]

theorem auxiliaryDeletedSliceAux_path_vertexSet
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (q : (auxiliaryDeletedSliceAux
      sigma i Qset good hspan hQset hgood).Index)
    (z : SliceSupportVertex sigma Qbar i Qset) :
    z ∈ ((auxiliaryDeletedSliceAux
      sigma i Qset good hspan hQset hgood).path q).vertexSet ↔
      z.1 ∈ (Qbar.path q.1).vertexSet := by
  change
    z ∈
        (((selectedSliceAuxInSupport
          sigma i Qset good hspan hQset hgood).inSpanningGraph.path q).mapLe
          le_sup_right).vertexSet ↔
      z.1 ∈ (Qbar.path q.1).vertexSet
  rw [GraphPath.mapLe_vertexSet,
    PathPacking.inSpanningGraph_path_vertexSet]
  change
    z ∈
        (((selectedSliceAuxInRaw sigma i Qset good hgood).path q).induce
          (sliceSupportVertexSetFor sigma Qbar i Qset)
          (selectedSliceAuxInRaw_staysIn_support
            sigma i Qset good hspan hQset hgood q)).vertexSet ↔
      z.1 ∈ (Qbar.path q.1).vertexSet
  rw [GraphPath.mem_induce_vertexSet]
  rw [selectedSliceAuxInRaw_path_vertexSet sigma i Qset good hgood q]

/-- If every selected auxiliary path avoids every discarded sliced row, then
the auxiliary packing in the deleted graph stays in the exact union of the
retained row paths. -/
theorem auxiliaryDeletedSliceAux_staysIn_selectedRows
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (havoid :
      ∀ q ∈ good, ∀ r : Rbar.Index, r ∉ retained →
        Disjoint (Qbar.path q).vertexSet
          (sigma.sliceRowPath i r).vertexSet) :
    (auxiliaryDeletedSliceAux
      sigma i Qset good hunique.1 hQset hgood).StaysIn
        (selectedRowVertexSet
          (auxiliaryDeletedSliceRows
            sigma i Qset good hunique.1 hQset hgood)
          retained) := by
  let rowsSmall :=
    auxiliaryDeletedSliceRows
      sigma i Qset good hunique.1 hQset hgood
  let auxSmall :=
    auxiliaryDeletedSliceAux
      sigma i Qset good hunique.1 hQset hgood
  have hrowsUnique :
      rowsSmall.IsUniqueLinkage :=
    auxiliaryDeletedSliceRows_isUniqueLinkage
      sigma i Qset good hunique hQset hgood
  intro q z hzq
  have hzRows : z ∈ rowsSmall.toPathPacking.vertexSet :=
    hrowsUnique.1 z
  rcases rowsSmall.toPathPacking.mem_vertexSet.1 hzRows with
    ⟨r, hzr⟩
  have hr : r ∈ retained := by
    by_contra hrnot
    have hzQbar : z.1 ∈ (Qbar.path q.1).vertexSet :=
      (auxiliaryDeletedSliceAux_path_vertexSet
        sigma i Qset good hunique.1 hQset hgood q z).1
        (by simpa [auxSmall] using hzq)
    have hzRow :
        z.1 ∈ (sigma.sliceRowPath i r).vertexSet :=
      (auxiliaryDeletedSliceRows_path_vertexSet
        sigma i Qset good hunique.1 hQset hgood r z).1
        (by simpa [rowsSmall] using hzr)
    exact Finset.disjoint_left.mp
      (havoid q.1 q.2 r hrnot) hzQbar hzRow
  apply
    (rowsSmall.restrictIndexSet retained).toPathPacking.mem_vertexSet.2
  exact ⟨⟨r, hr⟩, by simpa using hzr⟩

/-- Retained canonical rows after deleting discarded components. -/
noncomputable def retainedSliceRows
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :=
  selectedRowsInSupport
    (auxiliaryDeletedSliceRows
      sigma i Qset good hspan hQset hgood)
    retained

/-- Surviving auxiliary paths after inducing onto the exact retained-row
support. -/
noncomputable def retainedSliceAux
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (havoid :
      ∀ q ∈ good, ∀ r : Rbar.Index, r ∉ retained →
        Disjoint (Qbar.path q).vertexSet
          (sigma.sliceRowPath i r).vertexSet) :
    PathPacking
      (auxiliaryDeletedSliceGraph
          sigma i Qset good hunique.1 hQset hgood |>.induce
        {z |
          z ∈ selectedRowVertexSet
            (auxiliaryDeletedSliceRows
              sigma i Qset good hunique.1 hQset hgood)
            retained})
      Finset.univ Finset.univ :=
  PathPacking.induceUniv
    (auxiliaryDeletedSliceAux
      sigma i Qset good hunique.1 hQset hgood)
    (selectedRowVertexSet
      (auxiliaryDeletedSliceRows
        sigma i Qset good hunique.1 hQset hgood)
      retained)
    (auxiliaryDeletedSliceAux_staysIn_selectedRows
      sigma i Qset good retained hunique hQset hgood havoid)

theorem retainedSliceRows_isUniqueLinkage
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (retainedSliceRows
      sigma i Qset good retained hunique.1 hQset hgood).IsUniqueLinkage :=
  restrict_separated_rows_isUniqueLinkage
    (auxiliaryDeletedSliceRows
      sigma i Qset good hunique.1 hQset hgood)
    (auxiliaryDeletedSliceRows_isUniqueLinkage
      sigma i Qset good hunique hQset hgood)
    retained

@[simp] theorem auxiliaryDeletedSliceAux_card
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (auxiliaryDeletedSliceAux
      sigma i Qset good hspan hQset hgood).card = good.card := by
  change
    (((selectedSliceAuxInSupport
      sigma i Qset good hspan hQset hgood).inSpanningGraph.mapLe
        le_sup_right).card) = good.card
  rw [PathPacking.mapLe_card, PathPacking.inSpanningGraph_card]
  exact
    selectedSliceAuxInSupport_card
      sigma i Qset good hspan hQset hgood

@[simp] theorem retainedSliceAux_card
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (havoid :
      ∀ q ∈ good, ∀ r : Rbar.Index, r ∉ retained →
        Disjoint (Qbar.path q).vertexSet
          (sigma.sliceRowPath i r).vertexSet) :
    (retainedSliceAux
      sigma i Qset good retained hunique hQset hgood havoid).card =
        good.card := by
  change
    (PathPacking.induceUniv
      (auxiliaryDeletedSliceAux
        sigma i Qset good hunique.1 hQset hgood)
      (selectedRowVertexSet
        (auxiliaryDeletedSliceRows
          sigma i Qset good hunique.1 hQset hgood) retained)
      _).card = good.card
  rw [PathPacking.induceUniv_card]
  exact auxiliaryDeletedSliceAux_card
    sigma i Qset good hunique.1 hQset hgood

@[simp] theorem retainedSliceRows_card
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hspan : Rbar.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset) :
    (retainedSliceRows
      sigma i Qset good retained hspan hQset hgood).card =
        retained.card := by
  change
    (selectedRowsInSupport
      (auxiliaryDeletedSliceRows
        sigma i Qset good hspan hQset hgood)
      retained).card = retained.card
  unfold selectedRowsInSupport
  rw [PerfectPathPacking.induce_card,
    PerfectPathPacking.restrictIndexSet_card]
  rfl

theorem retainedSliceAux_intersectsRows
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (havoid :
      ∀ q ∈ good, ∀ r : Rbar.Index, r ∉ retained →
        Disjoint (Qbar.path q).vertexSet
          (sigma.sliceRowPath i r).vertexSet)
    (hmeet :
      ∀ q ∈ good, ∃ r ∈ retained,
        sigma.SliceSegmentIntersectsPath Qbar i r q) :
    PathSlicing.PathPackingIntersectsLinkage
      (retainedSliceRows
        sigma i Qset good retained hunique.1 hQset hgood)
      (retainedSliceAux
        sigma i Qset good retained hunique hQset hgood havoid) := by
  let rowsSmall :=
    auxiliaryDeletedSliceRows
      sigma i Qset good hunique.1 hQset hgood
  let auxSmall :=
    auxiliaryDeletedSliceAux
      sigma i Qset good hunique.1 hQset hgood
  let Ukeep : Finset (SliceSupportVertex sigma Qbar i Qset) :=
    selectedRowVertexSet rowsSmall retained
  intro q
  rcases hmeet q.1 q.2 with ⟨r, hr, v, hvQ, hvSlice⟩
  have hvRow : v ∈ (sigma.sliceRowPath i r).vertexSet :=
    sigma.mem_sliceRowPath_of_sliceInterior i r hvSlice
  let z0 : SliceSupportVertex sigma Qbar i Qset :=
    ⟨v, sliceRows_stayIn_support sigma Qbar i Qset r hvRow⟩
  have hz0Row : z0 ∈ (rowsSmall.path r).vertexSet :=
    (auxiliaryDeletedSliceRows_path_vertexSet
      sigma i Qset good hunique.1 hQset hgood r z0).2 hvRow
  have hzKeep : z0 ∈ Ukeep := by
    apply
      (rowsSmall.restrictIndexSet retained).toPathPacking.mem_vertexSet.2
    exact ⟨⟨r, hr⟩, hz0Row⟩
  let z : {x // x ∈ Ukeep} := ⟨z0, hzKeep⟩
  refine ⟨⟨r, hr⟩, Finset.not_disjoint_iff.2 ⟨z, ?_, ?_⟩⟩
  · change
      z ∈
        ((auxSmall.path q).induce Ukeep
          (auxiliaryDeletedSliceAux_staysIn_selectedRows
            sigma i Qset good retained hunique hQset hgood havoid q)).vertexSet
    apply
      (GraphPath.mem_induce_vertexSet
        (auxSmall.path q) Ukeep
        (auxiliaryDeletedSliceAux_staysIn_selectedRows
          sigma i Qset good retained hunique hQset hgood havoid q) z).2
    exact
      (auxiliaryDeletedSliceAux_path_vertexSet
        sigma i Qset good hunique.1 hQset hgood q z0).2 hvQ
  · change
      z ∈
        (((rowsSmall.restrictIndexSet retained).path ⟨r, hr⟩).induce
          Ukeep
          ((rowsSmall.restrictIndexSet retained).toPathPacking
            |>.path_vertexSet_subset_vertexSet ⟨r, hr⟩)).vertexSet
    apply
      (GraphPath.mem_induce_vertexSet
        ((rowsSmall.restrictIndexSet retained).path ⟨r, hr⟩)
        Ukeep
        ((rowsSmall.restrictIndexSet retained).toPathPacking
          |>.path_vertexSet_subset_vertexSet ⟨r, hr⟩) z).2
    exact hz0Row

/-- Observation 5.4, in its graph-theoretic type-two form.  The output graph
has exactly the retained sliced rows as its ambient support; those rows form
a perfect unique linkage, and every surviving auxiliary path meets one of
them.  The exact cardinalities are retained for the recursive arithmetic. -/
theorem observation54_type2_cleaned_slice
    (sigma : PathSlicing Rbar M) (i : Fin M)
    (Qset good : Finset Qbar.Index)
    (retained : Finset Rbar.Index)
    (hunique : Rbar.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Qbar i)
    (hgood : good ⊆ Qset)
    (havoid :
      ∀ q ∈ good, ∀ r : Rbar.Index, r ∉ retained →
        Disjoint (Qbar.path q).vertexSet
          (sigma.sliceRowPath i r).vertexSet)
    (hmeet :
      ∀ q ∈ good, ∃ r ∈ retained,
        sigma.SliceSegmentIntersectsPath Qbar i r q) :
    (retainedSliceRows
        sigma i Qset good retained hunique.1 hQset hgood).IsUniqueLinkage ∧
      (retainedSliceRows
        sigma i Qset good retained hunique.1 hQset hgood).card =
          retained.card ∧
      (retainedSliceAux
        sigma i Qset good retained hunique hQset hgood havoid).card =
          good.card ∧
      PathSlicing.PathPackingIntersectsLinkage
        (retainedSliceRows
          sigma i Qset good retained hunique.1 hQset hgood)
        (retainedSliceAux
          sigma i Qset good retained hunique hQset hgood havoid) := by
  exact
    ⟨retainedSliceRows_isUniqueLinkage
        sigma i Qset good retained hunique hQset hgood,
      retainedSliceRows_card
        sigma i Qset good retained hunique.1 hQset hgood,
      retainedSliceAux_card
        sigma i Qset good retained hunique hQset hgood havoid,
      retainedSliceAux_intersectsRows
        sigma i Qset good retained hunique hQset hgood havoid hmeet⟩

end PathSlicing
end Exponent8
end SimpleGraph

end Lax17Proofs
