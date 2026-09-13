import Lax17Proofs.Source.Exponent8.Observation54Type2

namespace Lax17Proofs

/-!
# Observation 5.4 for one recursive-slicing layer

The graph-theoretic Observation 5.4 theorem is applied to the additive cleanup
and localization data in `RecursiveSliceLayer`.

For one parent slice, the bad rows are the rows discarded by Lemma 4.8 and
the good auxiliary paths are the paths surviving the strengthened Claim 5.3
filter. Membership in that filter proves that every good path avoids every
discarded row segment. The positive `Dhat` lower bound supplies a retained row
met by each good path.

The resulting row and auxiliary packings lie in the retained-row support
subtype and establish the type-two part of Chuzhoy--Tan Observation 5.4.
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

/-- Rows discarded by additive Lemma 4.8 in one recursive slice. -/
noncomputable def observation54BadRows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) : Finset Rbar.Index :=
  (Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows

/-- Auxiliary paths surviving deletion of every path meeting a discarded
row segment. -/
noncomputable def observation54GoodQ
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) : Finset Qbar.Index :=
  (L.localization i).goodQ
    (L.observation54BadRows i) (L.cleanup i).paths

theorem observation54GoodQ_subset
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :
    L.observation54GoodQ i ⊆ (L.cleanup i).paths :=
  (L.localization i).goodQ_subset
    (L.observation54BadRows i) (L.cleanup i).paths

/-- A good path cannot meet a row discarded by the cleanup.  Otherwise the
slice-local intersection would put that path in `badHitQ`, contradicting the
definition as a finite-set difference. -/
theorem observation54GoodQ_avoids_discarded
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :
    ∀ q ∈ L.observation54GoodQ i,
      ∀ r : Rbar.Index, r ∉ (L.cleanup i).rows →
        Disjoint (Qbar.path q).vertexSet
          (L.sigma.sliceRowPath i r).vertexSet := by
  classical
  intro q hq r hr
  rw [Finset.disjoint_left]
  intro z hzQ hzRow
  have hqCleanup : q ∈ (L.cleanup i).paths :=
    L.observation54GoodQ_subset i hq
  have hqSlice : q ∈ L.sigma.pathsInSlice Qbar i :=
    (L.cleanup i).paths_subset hqCleanup
  have hqLocalized : q ∈ (L.localization i).localizedQ := by
    rw [L.localized_eq i]
    exact hqCleanup
  have hsegment :
      L.sigma.SliceSegmentIntersectsPath Qbar i r q := by
    apply
      (L.sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
        Qbar hqSlice).2
    rw [PathPacking.PathsIntersect, Finset.not_disjoint_iff]
    exact ⟨z, hzRow, hzQ⟩
  have hrBad : r ∈ L.observation54BadRows i := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr⟩
  have hbad :
      q ∈ (L.localization i).badHitQ
        (L.observation54BadRows i) (L.cleanup i).paths := by
    apply
      ((L.localization i).mem_badHitQ
        (L.observation54BadRows i) (L.cleanup i).paths q).2
    exact ⟨hqCleanup, hqLocalized, ⟨r, hrBad, hsegment⟩⟩
  exact
    (Finset.mem_sdiff.mp
      (show
        q ∈ (L.cleanup i).paths \
          (L.localization i).badHitQ
            (L.observation54BadRows i) (L.cleanup i).paths
        from hq)).2 hbad

/-- Every good auxiliary path still meets a retained row.  This uses only
the positive `Dhat` side of the additive cleanup's intersecting certificate;
no cardinality is discarded in this conversion. -/
theorem observation54GoodQ_meets_retained
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (hDhat : 0 < Dhat) :
    ∀ q ∈ L.observation54GoodQ i,
      ∃ r ∈ (L.cleanup i).rows,
        L.sigma.SliceSegmentIntersectsPath Qbar i r q := by
  classical
  intro q hq
  have hqCleanup : q ∈ (L.cleanup i).paths :=
    L.observation54GoodQ_subset i hq
  have hdense :=
    (L.cleanup i).intersecting.2 q hqCleanup
  have hpositive :
      0 <
        (L.sigma.segmentIntersectingLeftIndices
          Qbar i (L.cleanup i).rows q).card :=
    lt_of_lt_of_le hDhat hdense
  rcases Finset.card_pos.mp hpositive with ⟨r, hr⟩
  rw [L.sigma.mem_segmentIntersectingLeftIndices] at hr
  exact ⟨r, hr.1, hr.2⟩

/-- A row retained by the recursive cleanup has a nontrivial parent-slice
interval.

Theorem 4.5 permits two consecutive cuts to coincide. Such a zero-edge
interval cannot enter a recursive child: every retained row meets at least
`wHat` localized auxiliary paths, and the recursive specialization has
positive `wHat = 4 * g^2`. This theorem records that support restriction
explicitly, before the row is transported to the Observation 5.4 subtype. -/
theorem cleanup_sliceRowPath_source_ne_target
    (g : ℕ)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width (4 * g ^ 2) Dhat)
    (i : Fin m) (hg : 0 < g)
    {r : Rbar.Index} (hr : r ∈ (L.cleanup i).rows) :
    (L.sigma.sliceRowPath i r).source ≠
      (L.sigma.sliceRowPath i r).target := by
  classical
  have hpos :
      0 <
        (L.sigma.segmentIntersectingRightIndices
          Qbar i (L.cleanup i).paths r).card := by
    have h := (L.cleanup i).intersecting.1 r hr
    have hw : 0 < 4 * g ^ 2 := by positivity
    exact hw.trans_le h
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  have hqCleanup : q ∈ (L.cleanup i).paths :=
    ((L.sigma.mem_segmentIntersectingRightIndices
      Qbar i (L.cleanup i).paths r q).1 hq).1
  have hmeet :
      PathPacking.PathsIntersect
        (L.sigma.sliceRowPath i r) (Qbar.path q) :=
    (L.sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
      Qbar ((L.cleanup i).paths_subset hqCleanup)).1
      ((L.sigma.mem_segmentIntersectingRightIndices
        Qbar i (L.cleanup i).paths r q).1 hq).2
  rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvRow, hvQ⟩
  have hvSlice : L.sigma.SliceInterior r i v :=
    (L.sigma.mem_pathsInSlice Qbar i q).1
      ((L.cleanup i).paths_subset hqCleanup)
      hvQ (L.sigma.sliceRowPath_vertexSet_subset i r hvRow)
  intro hendpoints
  have hvEq :=
    GraphPath.eq_source_of_source_eq_target_of_mem_vertexSet
      (L.sigma.sliceRowPath i r) hendpoints hvRow
  exact hvSlice.2.2.2.1 (by
    simpa [L.sigma.sliceRowPath_source] using hvEq)

/-- The exact-support retained-row packing produced from one recursive
slice. -/
noncomputable def observation54Rows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :=
  PathSlicing.retainedSliceRows
    L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
    (L.cleanup i).rows L.unique_linkage.1
    (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)

/-- The good auxiliary packing, induced onto the exact retained-row
support. -/
noncomputable def observation54Aux
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :=
  PathSlicing.retainedSliceAux
    L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
    (L.cleanup i).rows L.unique_linkage
    (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)
    (L.observation54GoodQ_avoids_discarded i)

/-- Chuzhoy--Tan Observation 5.4, type-two branch, specialized to one
recursive layer.  This is the theorem consumed by the local Theorem 4.6
refinement: the rows are a perfect unique linkage, the auxiliary family
meets it, and neither family loses indices during the support transports. -/
theorem observation54_type2_cleaned_slice
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (hDhat : 0 < Dhat) :
    (L.observation54Rows i).IsUniqueLinkage ∧
      (L.observation54Rows i).card = (L.cleanup i).rows.card ∧
      (L.observation54Aux i).card =
        (L.observation54GoodQ i).card ∧
      PathSlicing.PathPackingIntersectsLinkage
        (L.observation54Rows i) (L.observation54Aux i) := by
  simpa only [observation54Rows, observation54Aux] using
    (PathSlicing.observation54_type2_cleaned_slice
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      (L.cleanup i).rows L.unique_linkage
      (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)
      (L.observation54GoodQ_avoids_discarded i)
      (L.observation54GoodQ_meets_retained i hDhat))

end RecursiveSliceLayer
end Exponent8
end SimpleGraph

end Lax17Proofs
