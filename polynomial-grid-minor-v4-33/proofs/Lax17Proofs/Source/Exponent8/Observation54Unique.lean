import Lax17Proofs.Source.Exponent8.Observation54Support
import Lax17Proofs.Source.PseudoGridReduction

namespace Lax17Proofs

/-!
# Hereditary uniqueness for one localized slice

This module formalizes the unique-linkage part of Chuzhoy--Tan Observation 5.4.
The sliced rows live in the exact support subtype constructed in
`Observation54Support`.  An arbitrary perfect linkage in that subtype is
lifted to the original graph and glued between the canonical row prefixes and
suffixes.  The construction permits arbitrary pairings between the two slice
boundaries.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

namespace PathSlicing

/-- The canonical row prefixes ending at the left boundary of slice `i`. -/
noncomputable def slicePrefixPacking
    (sigma : PathSlicing R M) (i : Fin M) :
    PerfectPathPacking G A (sliceLeftBoundary sigma i) where
  toPathPacking := {
    Index := R.Index
    path := fun r =>
      (R.path r).takeUntil (by
        simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
          sigma.cut_mem r i.castSucc)
    connects := by
      intro r
      exact Or.inl
        ⟨R.source_mem r,
          Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by
            simp [SimpleGraph.PathSlicing.sliceRowPath_source]⟩⟩
    node_disjoint := by
      intro r s hrs
      exact Finset.disjoint_of_subset_left
        ((R.path r).takeUntil_vertexSet_subset _)
        (Finset.disjoint_of_subset_right
          ((R.path s).takeUntil_vertexSet_subset _)
          (R.toPathPacking.node_disjoint hrs))
  }
  source_mem := fun r => R.source_mem r
  target_mem := by
    intro r
    exact Finset.mem_image.mpr
      ⟨r, Finset.mem_univ _, by
        simp [SimpleGraph.PathSlicing.sliceRowPath_source]⟩
  source_bijective := by
    simpa using R.source_bijective
  target_bijective := by
    constructor
    · intro r s hrs
      apply sigma.sliceRowPath_source_injective i
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
      exact ⟨r, by simp [SimpleGraph.PathSlicing.sliceRowPath_source]⟩

@[simp] theorem slicePrefixPacking_path_source
    (sigma : PathSlicing R M) (i : Fin M)
    (r : (slicePrefixPacking sigma i).Index) :
    ((slicePrefixPacking sigma i).path r).source = (R.path r).source := rfl

@[simp] theorem slicePrefixPacking_path_target
    (sigma : PathSlicing R M) (i : Fin M)
    (r : (slicePrefixPacking sigma i).Index) :
    ((slicePrefixPacking sigma i).path r).target =
      (sigma.sliceRowPath i r).source := by
  simp [slicePrefixPacking, SimpleGraph.PathSlicing.sliceRowPath_source]

/-- The actual target of the half-open slice path lies on its original row. -/
theorem sliceRowPath_target_mem_main
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) :
    (sigma.sliceRowPath i r).target ∈ (R.path r).vertexSet :=
  sigma.sliceRowPath_vertexSet_subset i r
    (GraphPath.target_mem_vertexSet _)

/-- The canonical row suffixes beginning at the actual target of the
half-open sliced row.  This suffix contains the edge leading to the deleted
right cut. -/
noncomputable def sliceSuffixPacking
    (sigma : PathSlicing R M) (i : Fin M) :
    PerfectPathPacking G (sliceRightBoundary sigma i) B where
  toPathPacking := {
    Index := R.Index
    path := fun r =>
      (R.path r).dropUntil (sliceRowPath_target_mem_main sigma i r)
    connects := by
      intro r
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by simp⟩,
          R.target_mem r⟩
    node_disjoint := by
      intro r s hrs
      exact Finset.disjoint_of_subset_left
        ((R.path r).dropUntil_vertexSet_subset _)
        (Finset.disjoint_of_subset_right
          ((R.path s).dropUntil_vertexSet_subset _)
          (R.toPathPacking.node_disjoint hrs))
  }
  source_mem := by
    intro r
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by simp⟩
  target_mem := fun r => R.target_mem r
  source_bijective := by
    constructor
    · intro r s hrs
      apply sigma.sliceRowPath_target_injective i
      exact congrArg Subtype.val hrs
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨r, _hr, rfl⟩
      exact ⟨r, rfl⟩
  target_bijective := by
    simpa using R.target_bijective

@[simp] theorem sliceSuffixPacking_path_source
    (sigma : PathSlicing R M) (i : Fin M)
    (r : (sliceSuffixPacking sigma i).Index) :
    ((sliceSuffixPacking sigma i).path r).source =
      (sigma.sliceRowPath i r).target := rfl

@[simp] theorem sliceSuffixPacking_path_target
    (sigma : PathSlicing R M) (i : Fin M)
    (r : (sliceSuffixPacking sigma i).Index) :
    ((sliceSuffixPacking sigma i).path r).target = (R.path r).target := rfl

/-- Lift an arbitrary perfect linkage in an exact slice support back to the
original graph.  No endpoint pairing is changed or prescribed. -/
noncomputable def liftSliceLinkage
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    PerfectPathPacking G (sliceLeftBoundary sigma i)
      (sliceRightBoundary sigma i) :=
  (SimpleGraph.Exponent8.liftInducedPerfect
      (sliceLeftBoundary_subset_support sigma Q i Qset)
      (sliceRightBoundary_subset_support sigma Q i Qset) L).mapLe
    (sliceRawGraph_le sigma Q i Qset)

@[simp] theorem liftSliceLinkage_path_vertexSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset)))
    (p : L.Index) :
    ((liftSliceLinkage sigma Q i Qset L).path p).vertexSet =
      (SimpleGraph.Exponent8.liftInducedPath (L.path p)).vertexSet := by
  simp [liftSliceLinkage, PerfectPathPacking.mapLe, PathPacking.mapLe]

/-- Every vertex of a localized exact support lies on a canonical sliced row. -/
theorem exists_sliceRowPath_of_mem_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    {v : V} (hv : v ∈ sliceSupportVertexSetFor sigma Q i Qset) :
    ∃ r : R.Index, v ∈ (sigma.sliceRowPath i r).vertexSet := by
  let z : SliceSupportVertex sigma Q i Qset := ⟨v, hv⟩
  have hz :=
    sliceSupport_spansVertices sigma Q i Qset hspan hQset z
  rcases
      (sliceRowsInSupport sigma Q i Qset).toPathPacking.mem_vertexSet.1 hz with
    ⟨r, hzr⟩
  refine ⟨r, ?_⟩
  have hraw :
      v ∈ ((sliceRowsInRawGraph sigma Q i Qset).path r).vertexSet :=
    (GraphPath.mem_induce_vertexSet
      ((sliceRowsInRawGraph sigma Q i Qset).path r)
      (sliceSupportVertexSetFor sigma Q i Qset)
      (sliceRowsInRawGraph_stayIn_support sigma Q i Qset r) z).1 hzr
  simpa [sliceRowsInRawGraph, PerfectPathPacking.mapLe,
    PathPacking.mapLe] using hraw

theorem liftSliceLinkage_staysIn_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    (liftSliceLinkage sigma Q i Qset L).toPathPacking.StaysIn
      (sliceSupportVertexSetFor sigma Q i Qset) := by
  intro p
  rw [liftSliceLinkage_path_vertexSet]
  exact
    SimpleGraph.Exponent8.liftInducedPath_vertexSet_subset (L.path p)

/-- A canonical prefix can enter the localized support only at its target. -/
theorem eq_slicePrefix_target_of_mem_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (r : R.Index) {v : V}
    (hvPrefix : v ∈ ((slicePrefixPacking sigma i).path r).vertexSet)
    (hvSupport : v ∈ sliceSupportVertexSetFor sigma Q i Qset) :
    v = ((slicePrefixPacking sigma i).path r).target := by
  rcases
      exists_sliceRowPath_of_mem_support sigma Q i Qset
        hspan hQset hvSupport with
    ⟨s, hvSlice⟩
  by_cases hrs : r = s
  · subst s
    have hvBefore :
        (R.path r).Before v (sigma.sliceRowPath i r).source := by
      simpa [slicePrefixPacking,
        SimpleGraph.PathSlicing.sliceRowPath_source] using
        (R.path r).before_of_mem_takeUntil
          (by
            simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
              sigma.cut_mem r i.castSucc)
          hvPrefix
    have hBeforeV :
        (R.path r).Before (sigma.sliceRowPath i r).source v :=
      sigma.sliceRowPath_source_before_of_mem i r hvSlice
    have hvEq :=
      (R.path r).before_antisymm hvBefore hBeforeV
    simpa [slicePrefixPacking,
      SimpleGraph.PathSlicing.sliceRowPath_source] using hvEq
  · exact False.elim
      (Finset.disjoint_left.mp
        (R.toPathPacking.node_disjoint hrs)
        ((R.path r).takeUntil_vertexSet_subset
          (by
            simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
              sigma.cut_mem r i.castSucc) hvPrefix)
        (sigma.sliceRowPath_vertexSet_subset i s hvSlice))

/-- A canonical suffix can enter the localized support only at its source. -/
theorem eq_sliceSuffix_source_of_mem_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (r : R.Index) {v : V}
    (hvSuffix : v ∈ ((sliceSuffixPacking sigma i).path r).vertexSet)
    (hvSupport : v ∈ sliceSupportVertexSetFor sigma Q i Qset) :
    v = ((sliceSuffixPacking sigma i).path r).source := by
  rcases
      exists_sliceRowPath_of_mem_support sigma Q i Qset
        hspan hQset hvSupport with
    ⟨s, hvSlice⟩
  by_cases hrs : r = s
  · subst s
    by_cases hcut :
        sigma.cut r i.castSucc = sigma.cut r i.succ
    · let hclosed :=
        sigma.cut_monotone r (Fin.castSucc_le_succ i)
      let closed := (R.path r).segmentOfBefore hclosed
      have hvClosed : v ∈ closed.vertexSet :=
        closed.dropLast_vertexSet_subset hvSlice
      have hvBeforeLeft :
          (R.path r).Before v (sigma.sliceRowPath i r).source := by
        have hvRight :=
          (R.path r).before_of_mem_segmentOfBefore_right hclosed hvClosed
        simpa [closed, hclosed, hcut,
          SimpleGraph.PathSlicing.sliceRowPath_source] using hvRight
      have hLeftBeforeV :
          (R.path r).Before (sigma.sliceRowPath i r).source v :=
        sigma.sliceRowPath_source_before_of_mem i r hvSlice
      have hvLeft :=
        (R.path r).before_antisymm hvBeforeLeft hLeftBeforeV
      have htSlice :
          (sigma.sliceRowPath i r).target ∈
            (sigma.sliceRowPath i r).vertexSet :=
        GraphPath.target_mem_vertexSet _
      have htClosed :
          (sigma.sliceRowPath i r).target ∈ closed.vertexSet :=
        closed.dropLast_vertexSet_subset htSlice
      have htBeforeLeft :
          (R.path r).Before (sigma.sliceRowPath i r).target
            (sigma.sliceRowPath i r).source := by
        have htRight :=
          (R.path r).before_of_mem_segmentOfBefore_right hclosed htClosed
        simpa [closed, hclosed, hcut,
          SimpleGraph.PathSlicing.sliceRowPath_source] using htRight
      have hLeftBeforeT :
          (R.path r).Before (sigma.sliceRowPath i r).source
            (sigma.sliceRowPath i r).target :=
        sigma.sliceRowPath_source_before_of_mem i r htSlice
      have htLeft :=
        (R.path r).before_antisymm htBeforeLeft hLeftBeforeT
      simpa [sliceSuffixPacking] using hvLeft.trans htLeft.symm
    · have hvBefore :
          (R.path r).Before v (sigma.sliceRowPath i r).target :=
        sigma.before_sliceRowPath_target_of_mem i r hcut hvSlice
      have hBeforeV :
          (R.path r).Before (sigma.sliceRowPath i r).target v := by
        exact ⟨sliceRowPath_target_mem_main sigma i r,
          by simpa [sliceSuffixPacking] using hvSuffix⟩
      have hvEq :=
        (R.path r).before_antisymm hvBefore hBeforeV
      simpa [sliceSuffixPacking] using hvEq
  · exact False.elim
      (Finset.disjoint_left.mp
        (R.toPathPacking.node_disjoint hrs)
        ((R.path r).dropUntil_vertexSet_subset
          (sliceRowPath_target_mem_main sigma i r) hvSuffix)
        (sigma.sliceRowPath_vertexSet_subset i s hvSlice))

theorem slicePrefix_internallyDisjoint_support
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    (slicePrefixPacking sigma i).toPathPacking.InternallyDisjointFromSet
      (sliceSupportVertexSetFor sigma Q i Qset) := by
  intro r v hvPrefix hvSupport
  exact Or.inr
    (eq_slicePrefix_target_of_mem_support
      sigma Q i Qset hspan hQset r hvPrefix hvSupport)

theorem slicePrefix_sourceOnlyAtTarget
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    ∀ r : (slicePrefixPacking sigma i).Index,
      ∀ p : (liftSliceLinkage sigma Q i Qset L).Index,
        ((slicePrefixPacking sigma i).path r).source ∈
            ((liftSliceLinkage sigma Q i Qset L).path p).vertexSet →
          ((slicePrefixPacking sigma i).path r).source =
            ((slicePrefixPacking sigma i).path r).target := by
  intro r p hv
  exact eq_slicePrefix_target_of_mem_support
    sigma Q i Qset hspan hQset r
    (GraphPath.source_mem_vertexSet _)
    (liftSliceLinkage_staysIn_support sigma Q i Qset L p hv)

/-- Glue an arbitrary local linkage after the canonical prefixes. -/
noncomputable def prefixLocalLinkage
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    PerfectPathPacking G A (sliceRightBoundary sigma i) :=
  (slicePrefixPacking sigma i)
    |>.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      (liftSliceLinkage sigma Q i Qset L)
      (slicePrefix_internallyDisjoint_support
        sigma Q i Qset hspan hQset)
      (liftSliceLinkage_staysIn_support sigma Q i Qset L)
      (slicePrefix_sourceOnlyAtTarget
        sigma Q i Qset hspan hQset L)

theorem prefixLocalLinkage_staysIn
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    (prefixLocalLinkage sigma Q i Qset hspan hQset L).toPathPacking.StaysIn
      ((slicePrefixPacking sigma i).toPathPacking.vertexSet ∪
        sliceSupportVertexSetFor sigma Q i Qset) := by
  exact
    SimpleGraph.PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_staysIn_union
        (slicePrefixPacking sigma i)
        (liftSliceLinkage sigma Q i Qset L)
        (slicePrefix_internallyDisjoint_support
          sigma Q i Qset hspan hQset)
        (liftSliceLinkage_staysIn_support sigma Q i Qset L)
        (slicePrefix_sourceOnlyAtTarget
          sigma Q i Qset hspan hQset L)
        (by
          intro r
          exact
            (slicePrefixPacking sigma i).toPathPacking
              |>.path_vertexSet_subset_vertexSet r)

/-- A suffix meets the union of all prefixes only at the suffix source. -/
theorem eq_sliceSuffix_source_of_mem_prefixVertexSet
    (sigma : PathSlicing R M) (i : Fin M)
    (r : R.Index) {v : V}
    (hvSuffix : v ∈ ((sliceSuffixPacking sigma i).path r).vertexSet)
    (hvPrefixes :
      v ∈ (slicePrefixPacking sigma i).toPathPacking.vertexSet) :
    v = ((sliceSuffixPacking sigma i).path r).source := by
  rcases
      (slicePrefixPacking sigma i).toPathPacking.mem_vertexSet.1 hvPrefixes with
    ⟨s, hvPrefix⟩
  by_cases hrs : r = s
  · subst s
    have hvBeforeLeft :
        (R.path r).Before v (sigma.sliceRowPath i r).source := by
      simpa [slicePrefixPacking,
        SimpleGraph.PathSlicing.sliceRowPath_source] using
        (R.path r).before_of_mem_takeUntil
          (by
            simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
              sigma.cut_mem r i.castSucc)
          hvPrefix
    have hLeftBeforeTarget :
        (R.path r).Before (sigma.sliceRowPath i r).source
          (sigma.sliceRowPath i r).target :=
      sigma.sliceRowPath_source_before_of_mem i r
        (GraphPath.target_mem_vertexSet _)
    have hvBeforeTarget :
        (R.path r).Before v (sigma.sliceRowPath i r).target :=
      (R.path r).before_trans hvBeforeLeft hLeftBeforeTarget
    have hTargetBeforeV :
        (R.path r).Before (sigma.sliceRowPath i r).target v :=
      ⟨sliceRowPath_target_mem_main sigma i r,
        by simpa [sliceSuffixPacking] using hvSuffix⟩
    have hvEq :=
      (R.path r).before_antisymm hvBeforeTarget hTargetBeforeV
    simpa [sliceSuffixPacking] using hvEq
  · exact False.elim
      (Finset.disjoint_left.mp
        (R.toPathPacking.node_disjoint hrs)
        ((R.path r).dropUntil_vertexSet_subset
          (sliceRowPath_target_mem_main sigma i r) hvSuffix)
        ((R.path s).takeUntil_vertexSet_subset
          (by
            simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
              sigma.cut_mem s i.castSucc) hvPrefix))

theorem sliceSuffix_internallyDisjoint_preSupport
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    (sliceSuffixPacking sigma i).toPathPacking.InternallyDisjointFromSet
      ((slicePrefixPacking sigma i).toPathPacking.vertexSet ∪
        sliceSupportVertexSetFor sigma Q i Qset) := by
  intro r v hvSuffix hv
  rcases Finset.mem_union.mp hv with hvPrefix | hvSupport
  · exact Or.inl
      (eq_sliceSuffix_source_of_mem_prefixVertexSet
        sigma i r hvSuffix hvPrefix)
  · exact Or.inl
      (eq_sliceSuffix_source_of_mem_support
        sigma Q i Qset hspan hQset r hvSuffix hvSupport)

theorem sliceSuffix_targetOnlyAtSource
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    ∀ p : (prefixLocalLinkage sigma Q i Qset hspan hQset L).Index,
      ∀ r : (sliceSuffixPacking sigma i).Index,
        ((sliceSuffixPacking sigma i).path r).target ∈
            ((prefixLocalLinkage sigma Q i Qset hspan hQset L).path p).vertexSet →
          ((sliceSuffixPacking sigma i).path r).target =
            ((sliceSuffixPacking sigma i).path r).source := by
  intro p r hv
  have hvRegion :
      ((sliceSuffixPacking sigma i).path r).target ∈
        ((slicePrefixPacking sigma i).toPathPacking.vertexSet ∪
          sliceSupportVertexSetFor sigma Q i Qset) :=
    prefixLocalLinkage_staysIn
      sigma Q i Qset hspan hQset L p hv
  rcases Finset.mem_union.mp hvRegion with hvPrefix | hvSupport
  · exact eq_sliceSuffix_source_of_mem_prefixVertexSet
      sigma i r (GraphPath.target_mem_vertexSet _) hvPrefix
  · exact eq_sliceSuffix_source_of_mem_support
      sigma Q i Qset hspan hQset r
        (GraphPath.target_mem_vertexSet _) hvSupport

/-- Extend an arbitrary perfect linkage in one exact slice support to a
perfect `A`--`B` linkage in the original graph.  The local linkage may use any
bijection between its left and right boundary terminals. -/
noncomputable def alternate_slice_linkage_extends_to_global
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    PerfectPathPacking G A B :=
  (prefixLocalLinkage sigma Q i Qset hspan hQset L)
    |>.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      (sliceSuffixPacking sigma i)
      (prefixLocalLinkage_staysIn
        sigma Q i Qset hspan hQset L)
      (sliceSuffix_internallyDisjoint_preSupport
        sigma Q i Qset hspan hQset)
      (sliceSuffix_targetOnlyAtSource
        sigma Q i Qset hspan hQset L)

/-! ## Exact edge traces through perfect-packing concatenation -/

theorem appendWithEq_edgeSet_eq
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hpath :
      (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).edgeSet = P.edgeSet ∪ Q.edgeSet := by
  classical
  ext e
  simp [GraphPath.appendWithEq, GraphPath.edgeSet,
    _root_.SimpleGraph.Walk.edges_append]

theorem concat_edgeSet_eq
    {C : Finset V}
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G B C)
    (hpath :
      ∀ p : P.Index,
        ((P.path p).walk.append
          ((Q.path (P.indexOfSourceTarget Q p)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget P Q p) rfl)).IsPath)
    (hnode :
      Pairwise fun p q =>
        GraphPath.NodeDisjoint
          ((P.path p).appendWithEq
            (Q.path (P.indexOfSourceTarget Q p))
            (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
            (hpath p))
          ((P.path q).appendWithEq
            (Q.path (P.indexOfSourceTarget Q q))
            (PerfectPathPacking.source_indexOfSourceTarget P Q q).symm
            (hpath q))) :
    (P.concat Q hpath hnode).toPathPacking.edgeSet =
      P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    rcases
        ((P.concat Q hpath hnode).toPathPacking.mem_edgeSet).1 he with
      ⟨p, hep⟩
    have hsplit :
        e ∈ (P.path p).edgeSet ∪
          (Q.path (P.indexOfSourceTarget Q p)).edgeSet := by
      rw [← appendWithEq_edgeSet_eq
        (P.path p) (Q.path (P.indexOfSourceTarget Q p))
        (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
        (hpath p)]
      exact hep
    rcases Finset.mem_union.mp hsplit with heP | heQ
    · exact Finset.mem_union_left _
        (P.toPathPacking.mem_edgeSet.2 ⟨p, heP⟩)
    · exact Finset.mem_union_right _
        (Q.toPathPacking.mem_edgeSet.2
          ⟨P.indexOfSourceTarget Q p, heQ⟩)
  · intro e he
    rcases Finset.mem_union.mp he with heP | heQ
    · rcases P.toPathPacking.mem_edgeSet.1 heP with ⟨p, hep⟩
      apply (P.concat Q hpath hnode).toPathPacking.mem_edgeSet.2
      refine ⟨p, ?_⟩
      change
        e ∈
          ((P.path p).appendWithEq
            (Q.path (P.indexOfSourceTarget Q p))
            (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
            (hpath p)).edgeSet
      rw [appendWithEq_edgeSet_eq
        (P.path p) (Q.path (P.indexOfSourceTarget Q p))
        (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
        (hpath p)]
      exact Finset.mem_union_left _ hep
    · rcases Q.toPathPacking.mem_edgeSet.1 heQ with ⟨q, heq⟩
      let p : P.Index :=
        P.indexOfTarget ⟨(Q.path q).source, Q.source_mem q⟩
      have hpTarget :
          (P.path p).target = (Q.path q).source := by
        exact congrArg Subtype.val
          (P.target_indexOfTarget ⟨(Q.path q).source, Q.source_mem q⟩)
      have hpq : P.indexOfSourceTarget Q p = q := by
        apply Q.source_bijective.1
        apply Subtype.ext
        calc
          (Q.path (P.indexOfSourceTarget Q p)).source =
              (P.path p).target :=
            PerfectPathPacking.source_indexOfSourceTarget P Q p
          _ = (Q.path q).source := hpTarget
      apply (P.concat Q hpath hnode).toPathPacking.mem_edgeSet.2
      refine ⟨p, ?_⟩
      change
        e ∈
          ((P.path p).appendWithEq
            (Q.path (P.indexOfSourceTarget Q p))
            (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
            (hpath p)).edgeSet
      rw [appendWithEq_edgeSet_eq
        (P.path p) (Q.path (P.indexOfSourceTarget Q p))
        (PerfectPathPacking.source_indexOfSourceTarget P Q p).symm
        (hpath p)]
      exact Finset.mem_union_right _ (by simpa [hpq] using heq)

/-- Keep only edges whose two endpoints lie in `U`. -/
noncomputable def edgesInside
    (U : Finset V) (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => e.toFinset ⊆ U

theorem mem_edgesInside {U : Finset V} {E : Finset (Sym2 V)}
    {e : Sym2 V} :
    e ∈ edgesInside U E ↔ e ∈ E ∧ e.toFinset ⊆ U := by
  classical
  simp [edgesInside]

theorem edgesInside_union
    (U : Finset V) (E F : Finset (Sym2 V)) :
    edgesInside U (E ∪ F) = edgesInside U E ∪ edgesInside U F := by
  classical
  ext e
  simp only [mem_edgesInside, Finset.mem_union]
  tauto

/-- Filtering does nothing to the edge set of a packing wholly supported
inside `U`. -/
theorem edgesInside_edgeSet_eq_of_staysIn
    (P : PathPacking G S T) (U : Finset V)
    (hP : P.StaysIn U) :
    edgesInside U P.edgeSet = P.edgeSet := by
  classical
  apply Finset.filter_eq_self.2
  intro e he
  rcases P.mem_edgeSet.1 he with ⟨p, hep⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy :=
        GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path p) hep
      rw [Sym2.toFinset_mk_eq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hP p hxy.1
      · exact hP p hxy.2

/-- No edge of a canonical prefix has both endpoints in the exact localized
slice support. -/
theorem edgesInside_slicePrefixPacking_edgeSet_eq_empty
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    edgesInside (sliceSupportVertexSetFor sigma Q i Qset)
        (slicePrefixPacking sigma i).toPathPacking.edgeSet = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro e he
  rcases mem_edgesInside.1 he with ⟨hePrefix, heSupport⟩
  rcases
      (slicePrefixPacking sigma i).toPathPacking.mem_edgeSet.1 hePrefix with
    ⟨r, her⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxyPrefix :=
        GraphPath.endpoints_mem_vertexSet_of_edgeSet
          ((slicePrefixPacking sigma i).path r) her
      have hxSupport :
          x ∈ sliceSupportVertexSetFor sigma Q i Qset := by
        exact heSupport (by simp [Sym2.toFinset_mk_eq])
      have hySupport :
          y ∈ sliceSupportVertexSetFor sigma Q i Qset := by
        exact heSupport (by simp [Sym2.toFinset_mk_eq])
      have hx :=
        eq_slicePrefix_target_of_mem_support
          sigma Q i Qset hspan hQset r hxyPrefix.1 hxSupport
      have hy :=
        eq_slicePrefix_target_of_mem_support
          sigma Q i Qset hspan hQset r hxyPrefix.2 hySupport
      have hxyNe : x ≠ y :=
        G.not_isDiag_of_mem_edgeSet
          (GraphPath.edgeSet_subset_edgeSet
            ((slicePrefixPacking sigma i).path r) her)
      exact hxyNe (hx.trans hy.symm)

/-- No edge of a canonical suffix has both endpoints in the exact localized
slice support. -/
theorem edgesInside_sliceSuffixPacking_edgeSet_eq_empty
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    edgesInside (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceSuffixPacking sigma i).toPathPacking.edgeSet = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro e he
  rcases mem_edgesInside.1 he with ⟨heSuffix, heSupport⟩
  rcases
      (sliceSuffixPacking sigma i).toPathPacking.mem_edgeSet.1 heSuffix with
    ⟨r, her⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxySuffix :=
        GraphPath.endpoints_mem_vertexSet_of_edgeSet
          ((sliceSuffixPacking sigma i).path r) her
      have hxSupport :
          x ∈ sliceSupportVertexSetFor sigma Q i Qset := by
        exact heSupport (by simp [Sym2.toFinset_mk_eq])
      have hySupport :
          y ∈ sliceSupportVertexSetFor sigma Q i Qset := by
        exact heSupport (by simp [Sym2.toFinset_mk_eq])
      have hx :=
        eq_sliceSuffix_source_of_mem_support
          sigma Q i Qset hspan hQset r hxySuffix.1 hxSupport
      have hy :=
        eq_sliceSuffix_source_of_mem_support
          sigma Q i Qset hspan hQset r hxySuffix.2 hySupport
      have hxyNe : x ≠ y :=
        G.not_isDiag_of_mem_edgeSet
          (GraphPath.edgeSet_subset_edgeSet
            ((sliceSuffixPacking sigma i).path r) her)
      exact hxyNe (hx.trans hy.symm)

theorem prefixLocalLinkage_edgeSet_eq
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    (prefixLocalLinkage sigma Q i Qset hspan hQset L).toPathPacking.edgeSet =
      (slicePrefixPacking sigma i).toPathPacking.edgeSet ∪
        (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet := by
  unfold prefixLocalLinkage
  unfold
    SimpleGraph.PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
  apply concat_edgeSet_eq

theorem alternate_slice_linkage_extends_to_global_edgeSet_eq
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    (alternate_slice_linkage_extends_to_global
        sigma Q i Qset hspan hQset L).toPathPacking.edgeSet =
      (slicePrefixPacking sigma i).toPathPacking.edgeSet ∪
        (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet ∪
          (sliceSuffixPacking sigma i).toPathPacking.edgeSet := by
  rw [show
      (alternate_slice_linkage_extends_to_global
          sigma Q i Qset hspan hQset L).toPathPacking.edgeSet =
        (prefixLocalLinkage
            sigma Q i Qset hspan hQset L).toPathPacking.edgeSet ∪
          (sliceSuffixPacking sigma i).toPathPacking.edgeSet by
    unfold alternate_slice_linkage_extends_to_global
    unfold
      SimpleGraph.PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
    apply concat_edgeSet_eq]
  rw [prefixLocalLinkage_edgeSet_eq]

/-- Filtering an extended local linkage back to the exact support recovers
exactly the lifted local linkage edge set. -/
theorem edgesInside_alternate_slice_linkage_extends_to_global
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    edgesInside (sliceSupportVertexSetFor sigma Q i Qset)
        (alternate_slice_linkage_extends_to_global
          sigma Q i Qset hspan hQset L).toPathPacking.edgeSet =
      (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet := by
  rw [alternate_slice_linkage_extends_to_global_edgeSet_eq,
    edgesInside_union, edgesInside_union,
    edgesInside_slicePrefixPacking_edgeSet_eq_empty
      sigma Q i Qset hspan hQset,
    edgesInside_sliceSuffixPacking_edgeSet_eq_empty
      sigma Q i Qset hspan hQset,
    edgesInside_edgeSet_eq_of_staysIn
      (liftSliceLinkage sigma Q i Qset L).toPathPacking
      (sliceSupportVertexSetFor sigma Q i Qset)
      (liftSliceLinkage_staysIn_support sigma Q i Qset L)]
  simp

/-- Removing the last edge of a path cannot introduce a new edge. -/
theorem dropLast_edgeSet_subset_local (P : GraphPath G) :
    P.dropLast.edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have heWalk : e ∈ P.walk.dropLast.edges := by
    simpa [GraphPath.dropLast, GraphPath.edgeSet] using he
  have hsub :
      P.walk.dropLast.edges ⊆ P.walk.edges :=
    ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.walk).dropLast).edges_subset
  exact by
    simpa [GraphPath.edgeSet] using hsub heWalk

theorem sliceRowPath_edgeSet_subset
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) :
    (sigma.sliceRowPath i r).edgeSet ⊆ (R.path r).edgeSet := by
  intro e he
  exact
    (R.path r).segmentOfBefore_edgeSet_subset
      (sigma.cut_monotone r (Fin.castSucc_le_succ i))
      (dropLast_edgeSet_subset_local
        ((R.path r).segmentOfBefore
          (sigma.cut_monotone r (Fin.castSucc_le_succ i))) he)

/-- The edges of the original row linkage whose two endpoints lie in the
localized support are exactly the sliced-row edges. -/
theorem edgesInside_originalRows_eq_sliceRows
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hspan : R.SpansVertices)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    edgesInside (sliceSupportVertexSetFor sigma Q i Qset)
        R.toPathPacking.edgeSet =
      (sliceRowPerfectPacking sigma i).toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    rcases mem_edgesInside.1 he with ⟨heRows, heSupport⟩
    rcases R.toPathPacking.mem_edgeSet.1 heRows with ⟨r, her⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxyRow :=
          GraphPath.endpoints_mem_vertexSet_of_edgeSet (R.path r) her
        have hxSupport :
            x ∈ sliceSupportVertexSetFor sigma Q i Qset :=
          heSupport (by simp [Sym2.toFinset_mk_eq])
        have hySupport :
            y ∈ sliceSupportVertexSetFor sigma Q i Qset :=
          heSupport (by simp [Sym2.toFinset_mk_eq])
        rcases
            exists_sliceRowPath_of_mem_support
              sigma Q i Qset hspan hQset hxSupport with
          ⟨rx, hxSlice⟩
        rcases
            exists_sliceRowPath_of_mem_support
              sigma Q i Qset hspan hQset hySupport with
          ⟨ry, hySlice⟩
        have hrx : r = rx := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (R.toPathPacking.node_disjoint hne)
            hxyRow.1
            (sigma.sliceRowPath_vertexSet_subset i rx hxSlice)
        have hry : r = ry := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (R.toPathPacking.node_disjoint hne)
            hxyRow.2
            (sigma.sliceRowPath_vertexSet_subset i ry hySlice)
        subst rx
        subst ry
        apply
          (sliceRowPerfectPacking sigma i).toPathPacking.mem_edgeSet.2
        refine ⟨r, ?_⟩
        exact
          Section4Reduction.GraphPath.edge_mem_of_edge_subset_of_endpoints_mem
            (R.path r) (sigma.sliceRowPath i r)
            (sliceRowPath_edgeSet_subset sigma i r)
            hxSlice hySlice her
  · intro he
    rcases
        (sliceRowPerfectPacking sigma i).toPathPacking.mem_edgeSet.1 he with
      ⟨r, her⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxySlice :=
          GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (sigma.sliceRowPath i r) her
        apply mem_edgesInside.2
        constructor
        · exact R.toPathPacking.mem_edgeSet.2
            ⟨r, sliceRowPath_edgeSet_subset sigma i r her⟩
        · rw [Sym2.toFinset_mk_eq]
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact sliceRows_stayIn_support sigma Q i Qset r hxySlice.1
          · exact sliceRows_stayIn_support sigma Q i Qset r hxySlice.2

/-- Lifting a path out of an induced graph maps precisely its edge set under
the subtype inclusion. -/
theorem liftInducedPath_edgeSet_eq_image
    {K : _root_.SimpleGraph V} {U : Finset V}
    (P : GraphPath (K.induce {v : V | v ∈ U})) :
    (SimpleGraph.Exponent8.liftInducedPath P).edgeSet =
      P.edgeSet.image (Sym2.map Subtype.val) := by
  classical
  ext e
  change
    e ∈
        (P.walk.map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges.toFinset ↔
      e ∈ P.walk.edges.toFinset.image (Sym2.map Subtype.val)
  rw [_root_.SimpleGraph.Walk.edges_map]
  simp

/-- Edge-image notation for a graph on a finite vertex subtype. -/
noncomputable def ambientEdgeImage
    (U : Finset V) (E : Finset (Sym2 {v : V // v ∈ U})) :
    Finset (Sym2 V) :=
  E.image (Sym2.map Subtype.val)

theorem liftInducedPerfect_edgeSet_eq_ambientEdgeImage
    {K : _root_.SimpleGraph V} {U A₀ B₀ : Finset V}
    (hA : A₀ ⊆ U) (hB : B₀ ⊆ U)
    (P : PerfectPathPacking (K.induce {v : V | v ∈ U})
      (PathPacking.subtypeFinset A₀ U hA)
      (PathPacking.subtypeFinset B₀ U hB)) :
    (SimpleGraph.Exponent8.liftInducedPerfect hA hB P).toPathPacking.edgeSet =
      ambientEdgeImage U P.toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    rcases
        (SimpleGraph.Exponent8.liftInducedPerfect hA hB P).toPathPacking
          |>.mem_edgeSet.1 he with
      ⟨p, hep⟩
    change
      e ∈ (SimpleGraph.Exponent8.liftInducedPath (P.path p)).edgeSet at hep
    rw [liftInducedPath_edgeSet_eq_image] at hep
    rcases Finset.mem_image.mp hep with ⟨e₀, he₀, rfl⟩
    exact Finset.mem_image.mpr
      ⟨e₀, P.toPathPacking.mem_edgeSet.2 ⟨p, he₀⟩, rfl⟩
  · intro he
    rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
    rcases P.toPathPacking.mem_edgeSet.1 he₀ with ⟨p, hep⟩
    apply
      (SimpleGraph.Exponent8.liftInducedPerfect hA hB P).toPathPacking
        |>.mem_edgeSet.2
    refine ⟨p, ?_⟩
    change
      Sym2.map Subtype.val e₀ ∈
        (SimpleGraph.Exponent8.liftInducedPath (P.path p)).edgeSet
    rw [liftInducedPath_edgeSet_eq_image]
    exact Finset.mem_image.mpr ⟨e₀, hep, rfl⟩

/-- Inducing a perfect packing onto a vertex set that contains all of its
paths, then mapping the subtype edges back, recovers its original edge set. -/
theorem ambientEdgeImage_induce_edgeSet_eq
    {K : _root_.SimpleGraph V} {U A₀ B₀ : Finset V}
    (P : PerfectPathPacking K A₀ B₀)
    (hP : P.toPathPacking.StaysIn U)
    (hA : A₀ ⊆ U) (hB : B₀ ⊆ U) :
    ambientEdgeImage U
        (P.induce U hP hA hB).toPathPacking.edgeSet =
      P.toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
    rcases
        (P.induce U hP hA hB).toPathPacking.mem_edgeSet.1 he₀ with
      ⟨p, hep⟩
    apply P.toPathPacking.mem_edgeSet.2
    refine ⟨p, ?_⟩
    change
      e₀ ∈ ((P.path p).induce U (hP p)).edgeSet at hep
    exact
      (GraphPath.mem_induce_edgeSet
        (P.path p) U (hP p) e₀).1 hep
  · intro he
    rcases P.toPathPacking.mem_edgeSet.1 he with ⟨p, hep⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy :=
          GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path p) hep
        let xU : {v : V // v ∈ U} := ⟨x, hP p hxy.1⟩
        let yU : {v : V // v ∈ U} := ⟨y, hP p hxy.2⟩
        let e₀ : Sym2 {v : V // v ∈ U} := s(xU, yU)
        apply Finset.mem_image.mpr
        refine ⟨e₀, ?_, ?_⟩
        · apply
            (P.induce U hP hA hB).toPathPacking.mem_edgeSet.2
          refine ⟨p, ?_⟩
          change e₀ ∈ ((P.path p).induce U (hP p)).edgeSet
          apply
            (GraphPath.mem_induce_edgeSet
              (P.path p) U (hP p) e₀).2
          simpa [e₀, xU, yU, Sym2.map_mk] using hep
        · simp [e₀, xU, yU, Sym2.map_mk]

theorem liftSliceLinkage_edgeSet_eq_ambientEdgeImage
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (L : PerfectPathPacking (sliceSupportGraph sigma Q i Qset)
      (PathPacking.subtypeFinset
        (sliceLeftBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceLeftBoundary_subset_support sigma Q i Qset))
      (PathPacking.subtypeFinset
        (sliceRightBoundary sigma i)
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRightBoundary_subset_support sigma Q i Qset))) :
    (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet =
      ambientEdgeImage
        (sliceSupportVertexSetFor sigma Q i Qset)
        L.toPathPacking.edgeSet := by
  unfold liftSliceLinkage
  rw [PerfectPathPacking.mapLe_edgeSet]
  exact
    liftInducedPerfect_edgeSet_eq_ambientEdgeImage
      (sliceLeftBoundary_subset_support sigma Q i Qset)
      (sliceRightBoundary_subset_support sigma Q i Qset) L

theorem inSpanningGraph_edgeSet_eq_local
    (P : PerfectPathPacking G A B) :
    P.inSpanningGraph.toPathPacking.edgeSet =
      P.toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    rcases P.inSpanningGraph.toPathPacking.mem_edgeSet.1 he with
      ⟨p, hep⟩
    apply P.toPathPacking.mem_edgeSet.2
    refine ⟨p, ?_⟩
    simpa [PerfectPathPacking.inSpanningGraph,
      PathPacking.inSpanningGraph, PathPacking.transfer,
      GraphPath.transfer_edgeSet] using hep
  · intro he
    rcases P.toPathPacking.mem_edgeSet.1 he with ⟨p, hep⟩
    apply P.inSpanningGraph.toPathPacking.mem_edgeSet.2
    refine ⟨p, ?_⟩
    simpa [PerfectPathPacking.inSpanningGraph,
      PathPacking.inSpanningGraph, PathPacking.transfer,
      GraphPath.transfer_edgeSet] using hep

theorem ambientEdgeImage_sliceRowsInSupport_edgeSet
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index) :
    ambientEdgeImage
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRowsInSupport sigma Q i Qset).toPathPacking.edgeSet =
      (sliceRowPerfectPacking sigma i).toPathPacking.edgeSet := by
  rw [show
      ambientEdgeImage
          (sliceSupportVertexSetFor sigma Q i Qset)
          (sliceRowsInSupport sigma Q i Qset).toPathPacking.edgeSet =
        (sliceRowsInRawGraph sigma Q i Qset).toPathPacking.edgeSet by
    exact ambientEdgeImage_induce_edgeSet_eq
      (sliceRowsInRawGraph sigma Q i Qset)
      (sliceRowsInRawGraph_stayIn_support sigma Q i Qset)
      (sliceLeftBoundary_subset_support sigma Q i Qset)
      (sliceRightBoundary_subset_support sigma Q i Qset)]
  change
    (((sliceRowPerfectPacking sigma i).inSpanningGraph.mapLe
      le_sup_left).toPathPacking.edgeSet) =
        (sliceRowPerfectPacking sigma i).toPathPacking.edgeSet
  rw [PerfectPathPacking.mapLe_edgeSet]
  exact inSpanningGraph_edgeSet_eq_local (sliceRowPerfectPacking sigma i)

theorem ambientEdgeImage_injective (U : Finset V) :
    Function.Injective (ambientEdgeImage U) := by
  exact Finset.image_injective
    (Sym2.map.injective Subtype.val_injective)

/-- Observation 5.4, unique-linkage part.  A slice of a perfect unique
linkage, together with any auxiliary paths localized to that slice, is again a
perfect unique linkage on its exact support subtype. -/
theorem sliceSupport_isUniqueLinkage
    (sigma : PathSlicing R M) (Q : PathPacking G S T)
    (i : Fin M) (Qset : Finset Q.Index)
    (hunique : R.IsUniqueLinkage)
    (hQset : Qset ⊆ sigma.pathsInSlice Q i) :
    (sliceRowsInSupport sigma Q i Qset).IsUniqueLinkage := by
  refine ⟨sliceSupport_spansVertices
    sigma Q i Qset hunique.1 hQset, ?_⟩
  intro L
  let Lglobal :=
    alternate_slice_linkage_extends_to_global
      sigma Q i Qset hunique.1 hQset L
  have hGlobal :
      Lglobal.toPathPacking.edgeSet =
        R.toPathPacking.edgeSet :=
    hunique.2 Lglobal
  have hFiltered :=
    congrArg
      (edgesInside (sliceSupportVertexSetFor sigma Q i Qset))
      hGlobal
  have hLifted :
      (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet =
        (sliceRowPerfectPacking sigma i).toPathPacking.edgeSet := by
    simpa [Lglobal,
      edgesInside_alternate_slice_linkage_extends_to_global
        sigma Q i Qset hunique.1 hQset L,
      edgesInside_originalRows_eq_sliceRows
        sigma Q i Qset hunique.1 hQset] using hFiltered
  apply ambientEdgeImage_injective
    (sliceSupportVertexSetFor sigma Q i Qset)
  calc
    ambientEdgeImage
        (sliceSupportVertexSetFor sigma Q i Qset)
        L.toPathPacking.edgeSet =
      (liftSliceLinkage sigma Q i Qset L).toPathPacking.edgeSet := by
        symm
        exact liftSliceLinkage_edgeSet_eq_ambientEdgeImage
          sigma Q i Qset L
    _ = (sliceRowPerfectPacking sigma i).toPathPacking.edgeSet :=
      hLifted
    _ = ambientEdgeImage
        (sliceSupportVertexSetFor sigma Q i Qset)
        (sliceRowsInSupport sigma Q i Qset).toPathPacking.edgeSet := by
          symm
          exact ambientEdgeImage_sliceRowsInSupport_edgeSet
            sigma Q i Qset

end PathSlicing
end Exponent8
end SimpleGraph

end Lax17Proofs
