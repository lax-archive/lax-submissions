import Lax17Proofs.Source.Exponent8.RecursiveSlicing
import Lax17Proofs.Source.Section45PseudoGrid

namespace Lax17Proofs

/-!
# All happy clusters in a large recursive slice

This module is the all-cluster version of
`PathSlicing.exists_sliceHappyCoreData`.  Chuzhoy--Tan Section 5.1 does not
select one happy cluster from a large slice: it retains the complete
Theorem 4.11 output and later groups all resulting cluster occurrences
geometrically.

The additive Lemma 4.8 certificate is first viewed through the ordinary
Section 4.3 interface.  Theorem 4.11 is then applied once, and every happy
cluster is replaced by the connected core supplied by
`exists_connected_happy_core`.  The final `quarter_mass` inequality counts
original row indices with the parent slice still implicit; aggregation across
slices will tag these occurrences by their parent.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset
open Section44
open Section44.PathPacking

namespace AdditiveSliceCleanup

/-- Forget only the additive-loss certificate and retain the exact ordinary
Lemma 4.8 output consumed by Theorem 4.11. -/
noncomputable def toOrdinary
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m wHat Dhat : ℕ}
    {sigma : PathSlicing Rbar m} {i : Fin m}
    (O : AdditiveSliceCleanup (Qbar := Qbar) sigma i wHat Dhat) :
    sigma.SliceIntersectingSubfamilies Qbar i wHat Dhat where
  rows := O.rows
  paths := O.paths
  rows_subset := O.rows_subset
  paths_subset := O.paths_subset
  intersecting := O.intersecting
  half_paths := O.half_paths
  discarded_rows_sparse := O.discarded_rows_sparse

@[simp] theorem toOrdinary_rows
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m wHat Dhat : ℕ}
    {sigma : PathSlicing Rbar m} {i : Fin m}
    (O : AdditiveSliceCleanup (Qbar := Qbar) sigma i wHat Dhat) :
    O.toOrdinary.rows = O.rows := rfl

@[simp] theorem toOrdinary_paths
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m wHat Dhat : ℕ}
    {sigma : PathSlicing Rbar m} {i : Fin m}
    (O : AdditiveSliceCleanup (Qbar := Qbar) sigma i wHat Dhat) :
    O.toOrdinary.paths = O.paths := rfl

end AdditiveSliceCleanup

/-- Every connected happy cluster produced in one large slice, expressed back
on the original row-index type. -/
structure AllHappyClustersData
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    {m : ℕ} (sigma : PathSlicing Rbar m) (i : Fin m)
    {wHappy DHappy : ℕ}
    (O : AdditiveSliceCleanup (Qbar := Qbar) sigma i
      (4 * wHappy) (2 * DHappy)) where
  ClusterIndex : Type v
  [clusterFintype : Fintype ClusterIndex]
  [clusterDecidableEq : DecidableEq ClusterIndex]
  cluster : ClusterIndex → Finset W
  rows : ClusterIndex → Finset Rbar.Index
  cluster_connected : ∀ c, IsCluster H (cluster c)
  cluster_subset_support :
    ∀ c,
      cluster c ⊆
        sigma.cleanedSupportVertexSet Qbar i O.toOrdinary
  cluster_disjoint :
    Pairwise fun c d => Disjoint (cluster c) (cluster d)
  rows_pairwise_disjoint :
    Pairwise fun c d => Disjoint (rows c) (rows d)
  rows_subset_cleanup : ∀ c, rows c ⊆ O.rows
  row_card : ∀ c, DHappy ≤ (rows c).card
  row_path_contained :
    ∀ c r, r ∈ rows c →
      ((sigma.sliceRowPacking i).path r).vertexSet ⊆ cluster c
  weak :
    ∀ c,
      WeakEdgeWellLinkedIn H (cluster c)
        ((rows c).image
            (fun r => ((sigma.sliceRowPacking i).path r).source) ∪
          (rows c).image
            (fun r => ((sigma.sliceRowPacking i).path r).target))
        wHappy
  quarter_mass :
    O.rows.card ≤ 4 * ∑ c : ClusterIndex, (rows c).card

attribute [instance] AllHappyClustersData.clusterFintype
attribute [instance] AllHappyClustersData.clusterDecidableEq

namespace PathSlicing

variable
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m wHappy DHappy : ℕ}
    {sigma : PathSlicing Rbar m} {i : Fin m}

/-- Theorem 4.11 applied to one additive cleanup, retaining connected cores
for every happy cluster and the full quarter-retention mass. -/
noncomputable def allHappyClusters_of_additiveCleanup
    (O : AdditiveSliceCleanup (Qbar := Qbar) sigma i
      (4 * wHappy) (2 * DHappy))
    (hw : 0 < wHappy)
    (hD : 0 < DHappy)
    (hscale : 8 * wHappy ≤ DHappy) :
    AllHappyClustersData Rbar Qbar sigma i O := by
  classical
  let O₀ := O.toOrdinary
  let Pclean := sigma.cleanedRowsInSupport Qbar i O₀
  let Qclean := sigma.cleanedAuxInSupport Qbar i O₀
  have hinter :
      Pclean.IntersectingPathSetPair Qclean
        Finset.univ Finset.univ (4 * wHappy) (2 * DHappy) := by
    simpa [Pclean, Qclean, O₀] using
      sigma.cleaned_intersecting Qbar i O₀
  let Output :=
    Classical.choice
      (Section44.PathPacking.theorem411
        Pclean Qclean Finset.univ Finset.univ
        hw hD hinter hscale)
  let coreExists :
      ∀ c : Output.ClusterIndex,
        ∃ Ccore : Finset W,
          IsCluster (sigma.cleanedSupportGraph Qbar i O₀) Ccore ∧
            Ccore ⊆ Output.cluster c ∧
              containedInCluster Pclean Finset.univ Ccore =
                containedInCluster Pclean Finset.univ (Output.cluster c) ∧
              WeakEdgeWellLinkedIn
                (sigma.cleanedSupportGraph Qbar i O₀) Ccore
                (endpointSetInCluster Pclean Finset.univ Ccore)
                wHappy :=
    fun c =>
      Section44.exists_connected_happy_core
        Pclean Finset.univ (Output.cluster c)
        hw hD (Output.happy c)
  let Ccore : Output.ClusterIndex → Finset W :=
    fun c => Classical.choose (coreExists c)
  have hcoreSpec :
      ∀ c : Output.ClusterIndex,
        IsCluster (sigma.cleanedSupportGraph Qbar i O₀) (Ccore c) ∧
          Ccore c ⊆ Output.cluster c ∧
            containedInCluster Pclean Finset.univ (Ccore c) =
              containedInCluster Pclean Finset.univ (Output.cluster c) ∧
            WeakEdgeWellLinkedIn
              (sigma.cleanedSupportGraph Qbar i O₀) (Ccore c)
              (endpointSetInCluster Pclean Finset.univ (Ccore c))
              wHappy :=
    fun c => Classical.choose_spec (coreExists c)
  let localRows : Output.ClusterIndex → Finset Pclean.Index :=
    fun c => containedInCluster Pclean Finset.univ (Ccore c)
  let rows : Output.ClusterIndex → Finset Rbar.Index :=
    fun c => (localRows c).image fun r => r.1
  have hvalInjective :
      Function.Injective (fun r : Pclean.Index => r.1) := by
    intro a b hab
    exact Subtype.ext hab
  have hrowsCard :
      ∀ c : Output.ClusterIndex,
        (rows c).card = (localRows c).card := by
    intro c
    exact Finset.card_image_of_injective _ hvalInjective
  have hrowCard :
      ∀ c : Output.ClusterIndex, DHappy ≤ (rows c).card := by
    intro c
    rw [hrowsCard c]
    change DHappy ≤
      (containedInCluster Pclean Finset.univ (Ccore c)).card
    rw [(hcoreSpec c).2.2.1]
    exact (Output.happy c).2
  have hrowsSubset :
      ∀ c : Output.ClusterIndex, rows c ⊆ O.rows := by
    intro c r hr
    rcases Finset.mem_image.mp hr with ⟨r', _hr', rfl⟩
    exact r'.2
  have hrowContained :
      ∀ c : Output.ClusterIndex, ∀ r ∈ rows c,
        ((sigma.sliceRowPacking i).path r).vertexSet ⊆ Ccore c := by
    intro c r hr
    rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
    have hr'data :=
      (mem_containedInCluster Pclean Finset.univ (Ccore c) r').1 hr'J
    intro x hx
    exact hr'data.2 (by simpa [Pclean] using hx)
  have hterminalSubset :
      ∀ c : Output.ClusterIndex,
        ((rows c).image
            (fun r => ((sigma.sliceRowPacking i).path r).source) ∪
          (rows c).image
            (fun r => ((sigma.sliceRowPacking i).path r).target)) ⊆
          endpointSetInCluster Pclean Finset.univ (Ccore c) := by
    intro c x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
      apply (mem_endpointSetInCluster Pclean Finset.univ (Ccore c) _).2
      exact Or.inl ⟨r', hr'J, by simp [Pclean]⟩
    · rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      rcases Finset.mem_image.mp hr with ⟨r', hr'J, rfl⟩
      apply (mem_endpointSetInCluster Pclean Finset.univ (Ccore c) _).2
      exact Or.inr ⟨r', hr'J, by simp [Pclean]⟩
  have hcoreSupport :
      ∀ c : Output.ClusterIndex,
        Ccore c ⊆ sigma.cleanedSupportVertexSet Qbar i O₀ := by
    intro c
    have hlocalPos : 0 < (localRows c).card := by
      rw [← hrowsCard c]
      exact hD.trans_le (hrowCard c)
    obtain ⟨r₀, hr₀⟩ := Finset.card_pos.mp hlocalPos
    have htCore :
        (Pclean.path r₀).source ∈ Ccore c :=
      ((mem_containedInCluster Pclean Finset.univ (Ccore c) r₀).1 hr₀).2
        (GraphPath.source_mem_vertexSet _)
    have htSupport :
        (Pclean.path r₀).source ∈
          sigma.cleanedSupportVertexSet Qbar i O₀ := by
      rw [SimpleGraph.PathSlicing.cleanedSupportVertexSet,
        Finset.mem_union]
      left
      apply (sigma.cleanedRows Qbar i O₀).mem_vertexSet.2
      refine ⟨r₀, ?_⟩
      change ((sigma.cleanedRows Qbar i O₀).path r₀).source ∈
        ((sigma.cleanedRows Qbar i O₀).path r₀).vertexSet
      exact GraphPath.source_mem_vertexSet _
    intro x hx
    by_cases hxt : x = (Pclean.path r₀).source
    · simpa [hxt] using htSupport
    · have hreachInduced :
          ((sigma.cleanedSupportGraph Qbar i O₀).induce
              {z : W | z ∈ Ccore c}).Reachable
            ⟨x, hx⟩ ⟨(Pclean.path r₀).source, htCore⟩ :=
        (hcoreSpec c).1.preconnected _ _
      have hreach :
          (sigma.cleanedSupportGraph Qbar i O₀).Reachable
            x (Pclean.path r₀).source :=
        hreachInduced.map
          (_root_.SimpleGraph.Embedding.induce
            {z : W | z ∈ Ccore c}).toHom
      exact
        sigma.cleanedSupportGraph_support_subset_sliceSupport Qbar i O₀
          (_root_.SimpleGraph.mem_support_of_reachable hxt hreach)
  have hclusterDisjoint :
      Pairwise fun c d : Output.ClusterIndex =>
        Disjoint (Ccore c) (Ccore d) := by
    intro c d hcd
    exact (Output.cluster_disjoint hcd).mono
      (hcoreSpec c).2.1 (hcoreSpec d).2.1
  have hrowsDisjoint :
      Pairwise fun c d : Output.ClusterIndex =>
        Disjoint (rows c) (rows d) := by
    intro c d hcd
    rw [Finset.disjoint_left]
    intro r hrc hrd
    have hsC :
        ((sigma.sliceRowPacking i).path r).source ∈ Ccore c :=
      hrowContained c r hrc (GraphPath.source_mem_vertexSet _)
    have hsD :
        ((sigma.sliceRowPacking i).path r).source ∈ Ccore d :=
      hrowContained d r hrd (GraphPath.source_mem_vertexSet _)
    exact Finset.disjoint_left.mp (hclusterDisjoint hcd) hsC hsD
  have hretainedSubset :
      Output.retained ⊆
        (Finset.univ : Finset Output.ClusterIndex).biUnion localRows := by
    intro r hr
    rcases Output.retained_contained r hr with ⟨c, hrc⟩
    apply Finset.mem_biUnion.2
    refine ⟨c, Finset.mem_univ _, ?_⟩
    change r ∈ containedInCluster Pclean Finset.univ (Ccore c)
    rw [(hcoreSpec c).2.2.1]
    exact hrc
  have hquarterOutput :
      O.rows.card ≤ 4 * Output.retained.card := by
    calc
      O.rows.card = Pclean.card := by
        simpa [Pclean, O₀, AdditiveSliceCleanup.toOrdinary] using
          (sigma.cleanedRowsInSupport_card Qbar i O₀).symm
      _ = (Finset.univ : Finset Pclean.Index).card := by
        simp [PathPacking.card]
      _ ≤ 4 * Output.retained.card := Output.quarter_retained
  have hquarter :
      O.rows.card ≤
        4 * ∑ c : Output.ClusterIndex, (rows c).card := by
    calc
      O.rows.card ≤ 4 * Output.retained.card := hquarterOutput
      _ ≤
          4 *
            ((Finset.univ : Finset Output.ClusterIndex).biUnion
              localRows).card :=
        Nat.mul_le_mul_left 4 (Finset.card_le_card hretainedSubset)
      _ ≤
          4 *
            ∑ c ∈ (Finset.univ : Finset Output.ClusterIndex),
              (localRows c).card :=
        Nat.mul_le_mul_left 4 Finset.card_biUnion_le
      _ = 4 * ∑ c : Output.ClusterIndex, (rows c).card := by
        congr 1
        simpa only using
          Finset.sum_congr rfl
            (fun c _hc => (hrowsCard c).symm)
  refine
    { ClusterIndex := Output.ClusterIndex
      cluster := Ccore
      rows := rows
      cluster_connected := fun c =>
        IsCluster.mono_graph (hcoreSpec c).1
          (sigma.cleanedSupportGraph_le Qbar i O₀)
      cluster_subset_support := hcoreSupport
      cluster_disjoint := hclusterDisjoint
      rows_pairwise_disjoint := hrowsDisjoint
      rows_subset_cleanup := hrowsSubset
      row_card := hrowCard
      row_path_contained := hrowContained
      weak := fun c =>
        WeakEdgeWellLinkedIn.mono_graph
          (WeakEdgeWellLinkedIn.mono_terminals
            (hcoreSpec c).2.2.2 (hterminalSubset c))
          (sigma.cleanedSupportGraph_le Qbar i O₀)
      quarter_mass := hquarter }

end PathSlicing

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
    {m width wHat Dhat rowCap mass : ℕ}

/-- A majority-large output and the corresponding parameter mass inequality
give the required sum of retained-row occurrences.  The sum is over slices,
so the same original row index is intentionally counted once per parent
slice in which its segment survives. -/
theorem assemblyMass_le_sum_rows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (Large : LargeSliceLayer L rowCap)
    (hmass : 2 * mass ≤ m * rowCap) :
    mass ≤
      ∑ i ∈ Large.large, (L.cleanup i).rows.card := by
  have hrows :
      Large.large.card * rowCap ≤
        ∑ i ∈ Large.large, (L.cleanup i).rows.card := by
    calc
      Large.large.card * rowCap =
          ∑ i ∈ Large.large, rowCap := by
        simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ Large.large, (L.cleanup i).rows.card := by
        exact Finset.sum_le_sum fun i hi => Large.rows_large i hi
  have hmajority :
      m * rowCap ≤ 2 * (Large.large.card * rowCap) := by
    calc
      m * rowCap ≤ (2 * Large.large.card) * rowCap :=
        Nat.mul_le_mul_right rowCap Large.majority
      _ = 2 * (Large.large.card * rowCap) := by ring
  have hdouble :
      2 * mass ≤
        2 * (∑ i ∈ Large.large, (L.cleanup i).rows.card) :=
    hmass.trans
      (hmajority.trans (Nat.mul_le_mul_left 2 hrows))
  omega

end RecursiveSliceLayer
end Exponent8
end SimpleGraph

end Lax17Proofs
