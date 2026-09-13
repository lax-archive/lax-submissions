import Lax17Proofs.Source.Exponent8.Observation54Composition
import Lax17Proofs.Source.Theorem46

namespace Lax17Proofs

/-!
# Local Theorem 4.6 refinements after Observation 5.4

This module invokes Chuzhoy--Tan Theorem 4.6 on the exact-support graph
produced by Observation 5.4, transports the local cut system back to the
original row paths, and extends it trivially across every discarded row.

The output is an `ExtendedParentRefinement`, ready for the nonconsecutive
composition theorem in `Observation54Composition`.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset

namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width wHat Dhat : ℕ}

/-- Membership in a retained Observation 5.4 row is exactly membership in
the corresponding original half-open parent row segment. -/
theorem observation54Rows_path_vertexSet_iff
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (r : (L.observation54Rows i).Index)
    (z : _) :
    z ∈ ((L.observation54Rows i).path r).vertexSet ↔
      z.1.1 ∈ (L.sigma.sliceRowPath i r.1).vertexSet := by
  let rowsSmall :=
    PathSlicing.auxiliaryDeletedSliceRows
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      L.unique_linkage.1 (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i)
  let Ukeep :=
    selectedRowVertexSet rowsSmall (L.cleanup i).rows
  have hrow :
      (rowsSmall.path r.1).vertexSet ⊆ Ukeep :=
    (rowsSmall.restrictIndexSet (L.cleanup i).rows).toPathPacking
      |>.path_vertexSet_subset_vertexSet r
  change
    z ∈ ((rowsSmall.path r.1).induce Ukeep hrow).vertexSet ↔
      z.1.1 ∈ (L.sigma.sliceRowPath i r.1).vertexSet
  calc
    z ∈ ((rowsSmall.path r.1).induce Ukeep hrow).vertexSet ↔
        z.1 ∈ (rowsSmall.path r.1).vertexSet :=
      GraphPath.mem_induce_vertexSet
        (rowsSmall.path r.1) Ukeep hrow z
    _ ↔ z.1.1 ∈ (L.sigma.sliceRowPath i r.1).vertexSet :=
      PathSlicing.auxiliaryDeletedSliceRows_path_vertexSet
        L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
        L.unique_linkage.1 (L.cleanup i).paths_subset
        (L.observation54GoodQ_subset i) r.1 z.1

/-- Membership in a retained Observation 5.4 auxiliary path is exactly
membership in its original `Qbar` path. -/
theorem observation54Aux_path_vertexSet_iff
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (q : (L.observation54Aux i).Index)
    (z : _) :
    z ∈ ((L.observation54Aux i).path q).vertexSet ↔
      z.1.1 ∈ (Qbar.path q.1).vertexSet := by
  let rowsSmall :=
    PathSlicing.auxiliaryDeletedSliceRows
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      L.unique_linkage.1 (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i)
  let auxSmall :=
    PathSlicing.auxiliaryDeletedSliceAux
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      L.unique_linkage.1 (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i)
  let Ukeep :=
    selectedRowVertexSet rowsSmall (L.cleanup i).rows
  have haux :
      (auxSmall.path q).vertexSet ⊆ Ukeep :=
    PathSlicing.auxiliaryDeletedSliceAux_staysIn_selectedRows
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      (L.cleanup i).rows L.unique_linkage
      (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)
      (L.observation54GoodQ_avoids_discarded i) q
  change
    z ∈ ((auxSmall.path q).induce Ukeep haux).vertexSet ↔
      z.1.1 ∈ (Qbar.path q.1).vertexSet
  calc
    z ∈ ((auxSmall.path q).induce Ukeep haux).vertexSet ↔
        z.1 ∈ (auxSmall.path q).vertexSet :=
      GraphPath.mem_induce_vertexSet
        (auxSmall.path q) Ukeep haux z
    _ ↔ z.1.1 ∈ (Qbar.path q.1).vertexSet :=
      PathSlicing.auxiliaryDeletedSliceAux_path_vertexSet
        L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
        L.unique_linkage.1 (L.cleanup i).paths_subset
        (L.observation54GoodQ_subset i) q z.1

/-- Local order on an exact-support retained row projects to the order on the
original half-open parent row segment. -/
theorem observation54Rows_before_val
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (r : (L.observation54Rows i).Index)
    {x y : _}
    (hxy : ((L.observation54Rows i).path r).Before x y) :
    (L.sigma.sliceRowPath i r.1).Before x.1.1 y.1.1 := by
  let rowsSmall :=
    PathSlicing.auxiliaryDeletedSliceRows
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      L.unique_linkage.1 (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i)
  let Ukeep :=
    selectedRowVertexSet rowsSmall (L.cleanup i).rows
  have hrow :
      (rowsSmall.path r.1).vertexSet ⊆ Ukeep :=
    (rowsSmall.restrictIndexSet (L.cleanup i).rows).toPathPacking
      |>.path_vertexSet_subset_vertexSet r
  have hsmall :
      (rowsSmall.path r.1).Before x.1 y.1 :=
    induce_before_val (rowsSmall.path r.1) Ukeep hrow hxy
  let supportRows :=
    PathSlicing.sliceRowsInSupport
      L.sigma Qbar i (L.cleanup i).paths
  change
    (((supportRows.inSpanningGraph.path r.1).mapLe le_sup_left).Before
      x.1 y.1) at hsmall
  have hinSupport :
      (supportRows.inSpanningGraph.path r.1).Before x.1 y.1 :=
    (mapLe_before_iff_local
      (supportRows.inSpanningGraph.path r.1) le_sup_left).1 hsmall
  have hsupport :
      (supportRows.path r.1).Before x.1 y.1 :=
    (pathPacking_inSpanningGraph_before_iff_local
      supportRows.toPathPacking r.1).1 hinSupport
  let rawRows :=
    PathSlicing.sliceRowsInRawGraph
      L.sigma Qbar i (L.cleanup i).paths
  have hraw :
      (rawRows.path r.1).Before x.1.1 y.1.1 :=
    induce_before_val
      (rawRows.path r.1)
      (PathSlicing.sliceSupportVertexSetFor
        L.sigma Qbar i (L.cleanup i).paths)
      (PathSlicing.sliceRowsInRawGraph_stayIn_support
        L.sigma Qbar i (L.cleanup i).paths r.1)
      hsupport
  let canonical := PathSlicing.sliceRowPerfectPacking L.sigma i
  change
    (((canonical.inSpanningGraph.path r.1).mapLe le_sup_left).Before
      x.1.1 y.1.1) at hraw
  have hinCanonical :
      (canonical.inSpanningGraph.path r.1).Before x.1.1 y.1.1 :=
    (mapLe_before_iff_local
      (canonical.inSpanningGraph.path r.1) le_sup_left).1 hraw
  have hcanonical :
      (canonical.path r.1).Before x.1.1 y.1.1 :=
    (pathPacking_inSpanningGraph_before_iff_local
      canonical.toPathPacking r.1).1 hinCanonical
  exact hcanonical

@[simp] theorem observation54Rows_source_val
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (r : (L.observation54Rows i).Index) :
    ((L.observation54Rows i).path r).source.1.1 =
      (L.sigma.sliceRowPath i r.1).source := by
  rfl

@[simp] theorem observation54Rows_target_val
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (r : (L.observation54Rows i).Index) :
    ((L.observation54Rows i).path r).target.1.1 =
      (L.sigma.sliceRowPath i r.1).target := by
  rfl

/-- Order on a half-open sliced row is inherited from the original full row.
This isolates the only walk-subpath calculation needed when local Theorem 4.6
cuts are transported back to the fixed global linkage. -/
theorem sliceRowPath_before_main
    (sigma : PathSlicing Rbar m) (i : Fin m) (r : Rbar.Index)
    {x y : W}
    (hxy : (sigma.sliceRowPath i r).Before x y) :
    (Rbar.path r).Before x y := by
  have hsub :
      (sigma.sliceRowPath i r).walk.IsSubwalk
        (Rbar.path r).walk := by
    unfold PathSlicing.sliceRowPath
    apply _root_.SimpleGraph.Walk.IsSubwalk.trans
      ((_root_.SimpleGraph.Walk.isSubwalk_rfl _).dropLast)
    unfold GraphPath.segmentOfBefore GraphPath.between
    apply _root_.SimpleGraph.Walk.IsSubwalk.trans
      (_root_.SimpleGraph.Walk.isSubwalk_takeUntil _ _)
    exact _root_.SimpleGraph.Walk.isSubwalk_dropUntil _ _
  exact
    before_of_walk_isSubwalk
      (Rbar.path r) (sigma.sliceRowPath i r) hsub hxy

/-- Local Theorem 4.6 cuts projected to the original vertex type and extended
trivially over discarded rows. -/
noncomputable def observation54ExtendedCut
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (r : Rbar.Index) (t : Fin (f + 1)) : W :=
  if hr : r ∈ (L.cleanup i).rows then
    (tau.cut ⟨r, hr⟩ t).1.1
  else if t = 0 then
    (L.sigma.sliceRowPath i r).source
  else
    (L.sigma.sliceRowPath i r).target

/-- The original `Qbar` indices captured by one local Theorem 4.6 cell. -/
noncomputable def observation54CellPaths
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (j : Fin f) : Finset Qbar.Index :=
  (tau.pathsInSlice (L.observation54Aux i) j).image
    (fun q => q.1)

theorem observation54ExtendedCut_mem_main
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (r : Rbar.Index) (t : Fin (f + 1)) :
    L.observation54ExtendedCut i tau r t ∈
      (Rbar.path r).vertexSet := by
  classical
  by_cases hr : r ∈ (L.cleanup i).rows
  · have hlocal :
        tau.cut ⟨r, hr⟩ t ∈
          ((L.observation54Rows i).path ⟨r, hr⟩).vertexSet :=
      tau.cut_mem ⟨r, hr⟩ t
    have hslice :
        (tau.cut ⟨r, hr⟩ t).1.1 ∈
          (L.sigma.sliceRowPath i r).vertexSet :=
      (L.observation54Rows_path_vertexSet_iff
        i ⟨r, hr⟩ (tau.cut ⟨r, hr⟩ t)).1 hlocal
    simpa [observation54ExtendedCut, hr] using
      L.sigma.sliceRowPath_vertexSet_subset i r hslice
  · by_cases ht : t = 0
    · simp only [observation54ExtendedCut, dif_neg hr, if_pos ht]
      exact
        L.sigma.sliceRowPath_vertexSet_subset i r
          (GraphPath.source_mem_vertexSet _)
    · simp only [observation54ExtendedCut, dif_neg hr, if_neg ht]
      exact
        L.sigma.sliceRowPath_vertexSet_subset i r
          (GraphPath.target_mem_vertexSet _)

@[simp] theorem observation54ExtendedCut_zero
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (r : Rbar.Index) :
    L.observation54ExtendedCut i tau r 0 =
      (L.sigma.sliceRowPath i r).source := by
  classical
  by_cases hr : r ∈ (L.cleanup i).rows
  · have hcut :=
      congrArg (fun z => z.1.1) (tau.cut_zero ⟨r, hr⟩)
    simpa [observation54ExtendedCut, hr] using hcut
  · simp [observation54ExtendedCut, hr]

@[simp] theorem observation54ExtendedCut_last
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ} (hf : 0 < f)
    (tau : PathSlicing (L.observation54Rows i) f)
    (r : Rbar.Index) :
    L.observation54ExtendedCut i tau r (Fin.last f) =
      (L.sigma.sliceRowPath i r).target := by
  classical
  have hlast_ne_zero :
      (Fin.last f) ≠ (0 : Fin (f + 1)) := by
    intro h
    have : f = 0 := by
      simpa using congrArg Fin.val h
    omega
  by_cases hr : r ∈ (L.cleanup i).rows
  · have hcut :=
      congrArg (fun z => z.1.1) (tau.cut_last ⟨r, hr⟩)
    simpa [observation54ExtendedCut, hr] using hcut
  · simp [observation54ExtendedCut, hr, hlast_ne_zero]

theorem observation54ExtendedCut_monotone
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (r : Rbar.Index) {s t : Fin (f + 1)} (hst : s ≤ t) :
    (Rbar.path r).Before
      (L.observation54ExtendedCut i tau r s)
      (L.observation54ExtendedCut i tau r t) := by
  classical
  by_cases hr : r ∈ (L.cleanup i).rows
  · have hlocal :=
      tau.cut_monotone ⟨r, hr⟩ hst
    have hslice :=
      L.observation54Rows_before_val i ⟨r, hr⟩ hlocal
    simpa [observation54ExtendedCut, hr] using
      sliceRowPath_before_main L.sigma i r hslice
  · by_cases hs : s = 0
    · subst s
      by_cases ht : t = 0
      · subst t
        simp only [observation54ExtendedCut, dif_neg hr, if_pos rfl]
        exact
          (Rbar.path r).before_refl
            (L.sigma.sliceRowPath_vertexSet_subset i r
              (GraphPath.source_mem_vertexSet _))
      · simp only [observation54ExtendedCut, dif_neg hr, if_pos rfl,
          if_neg ht]
        exact
          L.sigma.sliceRowPath_source_before_of_mem i r
            (GraphPath.target_mem_vertexSet _)
    · have ht : t ≠ 0 := by
        intro ht
        subst t
        have hsle : s ≤ (0 : Fin (f + 1)) := by
          simpa using hst
        exact hs (le_antisymm hsle (Fin.zero_le s))
      simp only [observation54ExtendedCut, dif_neg hr, if_neg hs,
        if_neg ht]
      exact
        (Rbar.path r).before_refl
          (L.sigma.sliceRowPath_vertexSet_subset i r
            (GraphPath.target_mem_vertexSet _))

@[simp] theorem observation54CellPaths_card
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (j : Fin f) :
    (L.observation54CellPaths i tau j).card =
      (tau.pathsInSlice (L.observation54Aux i) j).card := by
  classical
  unfold observation54CellPaths
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem observation54CellPaths_parent_localized
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (j : Fin f) :
    L.observation54CellPaths i tau j ⊆
      L.sigma.pathsInSlice Qbar i := by
  classical
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨q0, _hq0, rfl⟩
  exact
    (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i q0.2)

/-- Strict local Theorem 4.6 localization survives both exact-support
subtypes and the trivial extension over discarded rows. -/
theorem observation54CellPaths_strict_localized
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f : ℕ}
    (tau : PathSlicing (L.observation54Rows i) f)
    (j : Fin f) (q : Qbar.Index)
    (hq : q ∈ L.observation54CellPaths i tau j) :
    ∀ r v,
      v ∈ (Qbar.path q).vertexSet →
      v ∈ (Rbar.path r).vertexSet →
      (Rbar.path r).Before
          (L.observation54ExtendedCut i tau r j.castSucc) v ∧
        (Rbar.path r).Before v
          (L.observation54ExtendedCut i tau r j.succ) ∧
        v ≠ L.observation54ExtendedCut i tau r j.castSucc ∧
        v ≠ L.observation54ExtendedCut i tau r j.succ := by
  classical
  rcases Finset.mem_image.mp hq with ⟨q0, hq0, hqval⟩
  subst q
  intro r v hvQ hvR
  have hqParent :
      q0.1 ∈ L.sigma.pathsInSlice Qbar i :=
    (L.cleanup i).paths_subset
      (L.observation54GoodQ_subset i q0.2)
  have hvSlice :
      v ∈ (L.sigma.sliceRowPath i r).vertexSet :=
    PathSlicing.mem_sliceRowPath_of_mem_pathsInSlice
      L.sigma Qbar hqParent hvQ hvR
  by_cases hr : r ∈ (L.cleanup i).rows
  · let rowsSmall :=
      PathSlicing.auxiliaryDeletedSliceRows
        L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
        L.unique_linkage.1 (L.cleanup i).paths_subset
        (L.observation54GoodQ_subset i)
    let Ukeep :=
      selectedRowVertexSet rowsSmall (L.cleanup i).rows
    let z0 :
        PathSlicing.SliceSupportVertex
          L.sigma Qbar i (L.cleanup i).paths :=
      ⟨v, PathSlicing.sliceRows_stayIn_support
        L.sigma Qbar i (L.cleanup i).paths r hvSlice⟩
    have hz0Row :
        z0 ∈ (rowsSmall.path r).vertexSet := by
      exact
        (PathSlicing.auxiliaryDeletedSliceRows_path_vertexSet
          L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
          L.unique_linkage.1 (L.cleanup i).paths_subset
          (L.observation54GoodQ_subset i) r z0).2 hvSlice
    have hzKeep : z0 ∈ Ukeep := by
      apply
        (rowsSmall.restrictIndexSet
          (L.cleanup i).rows).toPathPacking.mem_vertexSet.2
      exact ⟨⟨r, hr⟩, hz0Row⟩
    let z : {x // x ∈ Ukeep} := ⟨z0, hzKeep⟩
    have hzAux :
        z ∈ ((L.observation54Aux i).path q0).vertexSet :=
      (L.observation54Aux_path_vertexSet_iff i q0 z).2 hvQ
    have hzRow :
        z ∈ ((L.observation54Rows i).path ⟨r, hr⟩).vertexSet :=
      (L.observation54Rows_path_vertexSet_iff i ⟨r, hr⟩ z).2
        hvSlice
    have hlocal :
        tau.SliceInterior ⟨r, hr⟩ j z :=
      (tau.mem_pathsInSlice (L.observation54Aux i) j q0).1
        hq0 hzAux hzRow
    have hleftSlice :
        (L.sigma.sliceRowPath i r).Before
          (tau.cut ⟨r, hr⟩ j.castSucc).1.1 v :=
      L.observation54Rows_before_val i ⟨r, hr⟩ hlocal.2.1
    have hrightSlice :
        (L.sigma.sliceRowPath i r).Before
          v (tau.cut ⟨r, hr⟩ j.succ).1.1 :=
      L.observation54Rows_before_val i ⟨r, hr⟩ hlocal.2.2.1
    refine
      ⟨?_, ?_, ?_, ?_⟩
    · simpa [observation54ExtendedCut, hr] using
        sliceRowPath_before_main L.sigma i r hleftSlice
    · simpa [observation54ExtendedCut, hr] using
        sliceRowPath_before_main L.sigma i r hrightSlice
    · simp only [observation54ExtendedCut, dif_pos hr]
      intro hv
      apply hlocal.2.2.2.1
      apply Subtype.ext
      apply Subtype.ext
      exact hv
    · simp only [observation54ExtendedCut, dif_pos hr]
      intro hv
      apply hlocal.2.2.2.2
      apply Subtype.ext
      apply Subtype.ext
      exact hv
  · have hdisj :=
      L.observation54GoodQ_avoids_discarded
        i q0.1 q0.2 r hr
    exact
      (Finset.disjoint_left.mp hdisj hvQ hvSlice).elim

/-- Package one local Theorem 4.6 slicing as a refinement of the original
parent slice. -/
noncomputable def observation54ExtendedParentRefinement
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f wNext : ℕ} (hf : 0 < f)
    (tau : PathSlicing (L.observation54Rows i) f)
    (hwidth :
      tau.WidthAtLeast (L.observation54Aux i) wNext) :
    PathSlicing.ExtendedParentRefinement
      L.sigma Qbar i f wNext where
  cut := L.observation54ExtendedCut i tau
  cut_mem_main := L.observation54ExtendedCut_mem_main i tau
  cut_zero := L.observation54ExtendedCut_zero i tau
  cut_last := L.observation54ExtendedCut_last i hf tau
  cut_monotone := L.observation54ExtendedCut_monotone i tau
  cellPaths := L.observation54CellPaths i tau
  cell_card := by
    intro j
    rw [L.observation54CellPaths_card i tau j]
    exact hwidth j
  cell_parent_localized :=
    L.observation54CellPaths_parent_localized i tau
  cell_strict_localized :=
    L.observation54CellPaths_strict_localized i tau

/-- Observation 5.4 followed by Chuzhoy--Tan Theorem 4.6, with all cuts
transported back to the fixed global row linkage. -/
theorem exists_observation54ExtendedParentRefinement
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) {f wNext : ℕ}
    (hDhat : 0 < Dhat) (hf : 0 < f) (hw : 0 < wNext)
    (hbudget :
      f * wNext + (f + 1) * (L.cleanup i).rows.card ≤
        (L.observation54GoodQ i).card) :
    Nonempty
      (PathSlicing.ExtendedParentRefinement
        L.sigma Qbar i f wNext) := by
  have hobs := L.observation54_type2_cleaned_slice i hDhat
  have hcard :
      f * wNext + (f + 1) * (L.observation54Rows i).card ≤
        (L.observation54Aux i).card := by
    rw [hobs.2.1, hobs.2.2.1]
    exact hbudget
  rcases
      PathSlicing.theorem46
        (L.observation54Rows i) (L.observation54Aux i)
        f wNext hf hw hobs.1 hobs.2.2.2 hcard with
    ⟨tau, htau⟩
  exact
    ⟨L.observation54ExtendedParentRefinement
      i hf tau htau⟩

end RecursiveSliceLayer
end Exponent8
end SimpleGraph

end Lax17Proofs
