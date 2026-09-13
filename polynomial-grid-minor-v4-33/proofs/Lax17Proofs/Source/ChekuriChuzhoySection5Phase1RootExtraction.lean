import Lax17Proofs.Source.ChekuriChuzhoyRootedTreeGrouping
import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthBridge
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Restoration
import Lax17Proofs.Source.ScaledLinkedSubsets
import Lax17Proofs.Source.Theorem214Nonconstructive

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1: extraction inside the root router

This module specializes preprint Corollary 2.12 to the family of root-side
endpoint sets produced by Claim 5.15.  Its proof composes:

* preprint Corollary 2.8 (journal Corollary 2.11), including the rooted-tree
  grouping of Observation 2.12;
* preprint Theorem 2.11 (journal Theorem 2.14), extracting a node-well-linked
  subset from every grouped block; and
* preprint Theorem 4.20 (journal Theorem 4.21), linking every two final blocks.

Only the semantic existential conclusion used in Phase 1 is retained.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1RootExtraction


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The root-router conclusion needed after Claim 5.15. -/
structure RootExtraction
    (G : _root_.SimpleGraph V) (root : Finset V)
    {m : Nat} (block : Fin m -> Finset V) (width : Nat) where
  endpoint : Fin m -> Finset V
  endpoint_subset : forall i, endpoint i ⊆ block i
  endpoint_card : forall i, (endpoint i).card = width
  endpoint_nodeWellLinked :
    forall i, NodeWellLinkedIn G root (endpoint i)
  endpoint_pair_nodeLinked :
    forall {i j : Fin m}, i ≠ j ->
      NodeLinkedIn G root (endpoint i) (endpoint j)

/-- Choose an exact-size subset from every member of a finite family. -/
noncomputable def exactSubset
    {I : Type*} (block : I -> Finset V) {width : Nat}
    (hwidth : forall i, width ≤ (block i).card) (i : I) : Finset V :=
  (Finset.exists_subset_card_eq (hwidth i)).choose

theorem exactSubset_subset
    {I : Type*} (block : I -> Finset V) {width : Nat}
    (hwidth : forall i, width ≤ (block i).card) (i : I) :
    exactSubset block hwidth i ⊆ block i :=
  (Finset.exists_subset_card_eq (hwidth i)).choose_spec.1

theorem exactSubset_card
    {I : Type*} (block : I -> Finset V) {width : Nat}
    (hwidth : forall i, width ≤ (block i).card) (i : I) :
    (exactSubset block hwidth i).card = width :=
  (Finset.exists_subset_card_eq (hwidth i)).choose_spec.2

/-- Source-faithful specialization of preprint Corollary 2.12.

The input blocks are equal-size subsets of the root-router interface.  The
truncated bandwidth hypothesis makes their union scaled edge-well-linked.
Corollary 2.8 groups each block simultaneously, Theorem 2.11 extracts
node-well-linked carriers, and Theorem 4.20 links every pair of final sets.
-/
theorem exists_rootExtraction_of_truncatedBandwidth
    {root : Finset V} {m cap alphaNum alphaDen Delta inWidth
      groupSize groupedWidth carrierWidth outWidth : Nat}
    (block : Fin m -> Finset V)
    (hroot : IsCluster G root)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hblockRoot : forall i, block i ⊆ root)
    (hblockInterface : forall i,
      block i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G root)
    (hblockCard : forall i, (block i).card = inWidth)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G root cap alphaNum alphaDen)
    (hunionCap : m * inWidth ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ inWidth)
    (hscale : alphaDen ≤ alphaNum * groupSize)
    (hgroupedWidth : groupedWidth ≤ inWidth / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty (RootExtraction G root block outWidth) := by
  classical
  let terminals : Finset V := Finset.univ.biUnion block
  by_cases hm : Nonempty (Fin m)
  · let i0 : Fin m := Classical.choice hm
    have hgroupSizeTerminals : groupSize ≤ terminals.card := by
      have hsub : block i0 ⊆ terminals := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, hx⟩
      exact hgroupSizeWidth.trans <| by
        rw [← hblockCard i0]
        exact Finset.card_le_card hsub
    have hterminalsRoot : terminals ⊆ root := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
      exact hblockRoot i hxi
    have hterminalsInterface :
        terminals ⊆
          ChekuriChuzhoySection5Clustering.interfaceVertices G root := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
      exact hblockInterface i hxi
    have hterminalsCap : terminals.card ≤ cap := by
      calc
        terminals.card ≤ ∑ i : Fin m, (block i).card := by
          exact Finset.card_biUnion_le
        _ = m * inWidth := by
          simp [hblockCard, Nat.mul_comm]
        _ ≤ cap := hunionCap
    have hterminalsWell :
        Section46.ScaledEdgeWellLinkedIn G root terminals
          alphaNum alphaDen :=
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth.scaledEdgeWellLinkedIn_of_subset_interface
        (G := G) hband hterminalsInterface hterminalsCap
    rcases ChekuriChuzhoyRootedTreeGrouping.exists_treeGrouping_of_connected
        (G := G) (C := root) (U := terminals) hgroupSize
        hroot hterminalsRoot hgroupSizeTerminals with
      ⟨K, hKFintype, hKDecidableEq, ⟨R⟩⟩
    letI : Fintype K := hKFintype
    letI : DecidableEq K := hKDecidableEq
    let J := ULift.{u} (Fin m)
    let liftedBlock : J -> Finset V := fun i => block i.down
    have hliftedBlockDisjoint :
        Set.PairwiseDisjoint Set.univ liftedBlock := by
      intro i _hi j _hj hij
      apply hblockDisjoint (by simp) (by simp)
      intro hdown
      apply hij
      cases i with
      | up i =>
        cases j with
        | up j =>
          cases hdown
          rfl
    have hliftedBlockCover :
        Finset.univ.biUnion liftedBlock = terminals := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
        exact Finset.mem_biUnion.mpr
          ⟨i.down, Finset.mem_univ _, by simpa [liftedBlock] using hxi⟩
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
        exact Finset.mem_biUnion.mpr
          ⟨ULift.up i, Finset.mem_univ _, by simpa [liftedBlock] using hxi⟩
    rcases ChekuriChuzhoyCorollary28.TreeGrouping.blockGroupingConclusion
        R liftedBlock hliftedBlockDisjoint hliftedBlockCover hgroupSize
        hterminalsWell hscale with
      ⟨D⟩
    have hselectedSize :
        forall i : J, groupedWidth ≤ (D.selectedBlock i).card := by
      intro i
      exact hgroupedWidth.trans <| by
        rw [← hblockCard i.down]
        exact D.selectedBlock_card i
    let selected : J -> Finset V :=
      exactSubset D.selectedBlock hselectedSize
    have hselectedSubset :
        forall i, selected i ⊆ D.selectedBlock i :=
      exactSubset_subset D.selectedBlock hselectedSize
    have hselectedCard :
        forall i, (selected i).card = groupedWidth :=
      exactSubset_card D.selectedBlock hselectedSize
    have hselectedUnionSubset :
        Finset.univ.biUnion selected ⊆
          Finset.univ.biUnion D.selectedBlock := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, hselectedSubset i hxi⟩
    have hselectedWell :
        Section46.ScaledEdgeWellLinkedIn G root
          (Finset.univ.biUnion selected) 1 2 :=
      Section46.ScaledEdgeWellLinkedIn.mono_terminals
        D.union_scaledEdgeWellLinked hselectedUnionSubset
    have hselectedBlockSubset :
        forall i, selected i ⊆ Finset.univ.biUnion selected := by
      intro i x hx
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
    have hselectedBlockWell :
        forall i,
          Section46.ScaledEdgeWellLinkedIn G root (selected i) 1 2 :=
      fun i =>
        Section46.ScaledEdgeWellLinkedIn.mono_terminals hselectedWell
          (hselectedBlockSubset i)
    choose carrierBig hcarrierBigSubset hcarrierBigCard hcarrierBigNode
      using fun i =>
        ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
          (G := G) (C := root) (T := selected i)
          (alphaNum := 1) (alphaDen := 2) (Δ := Delta)
          (κ := groupedWidth)
          hroot hdegree hDelta (by omega) (by omega)
          (hselectedCard i) (hselectedBlockWell i)
    have hcarrierBigEnough :
        forall i, carrierWidth ≤ (carrierBig i).card := by
      intro i
      exact hcarrierWidth.trans <| by
        simpa using hcarrierBigCard i
    choose carrier hcarrierSubset hcarrierCard using fun i =>
      Finset.exists_subset_card_eq (hcarrierBigEnough i)
    have hcarrierNode :
        forall i, NodeWellLinkedIn G root (carrier i) :=
      fun i =>
        (hcarrierBigNode i).mono_terminals (hcarrierSubset i)
    have hendpointExists :
        forall i, ∃ endpoint ⊆ carrier i, endpoint.card = outWidth := by
      intro i
      exact Finset.exists_subset_card_eq
        (by simpa [hcarrierCard i] using houtCarrier)
    choose endpoint hendpointSubset hendpointCard using hendpointExists
    refine ⟨{
      endpoint := fun i => endpoint (ULift.up i)
      endpoint_subset := ?_
      endpoint_card := fun i => hendpointCard (ULift.up i)
      endpoint_nodeWellLinked := ?_
      endpoint_pair_nodeLinked := ?_ }⟩
    · intro i
      exact (hendpointSubset (ULift.up i)).trans
        (hcarrierSubset (ULift.up i)) |>.trans
        (hcarrierBigSubset (ULift.up i)) |>.trans
        (hselectedSubset (ULift.up i)) |>.trans
        (D.selectedBlock_subset (ULift.up i))
    · intro i
      exact (hcarrierNode (ULift.up i)).mono_terminals
        (hendpointSubset (ULift.up i))
    · intro i j hij
      have hijLift : (ULift.up i : J) ≠ ULift.up j := by
        intro h
        exact hij (congrArg ULift.down h)
      have hcarrierDisjoint :
          Disjoint (carrier (ULift.up i)) (carrier (ULift.up j)) := by
        apply (hliftedBlockDisjoint (by simp) (by simp) hijLift).mono
        · exact (hcarrierSubset (ULift.up i)).trans
            (hcarrierBigSubset (ULift.up i)) |>.trans
            (hselectedSubset (ULift.up i)) |>.trans
            (D.selectedBlock_subset (ULift.up i))
        · exact (hcarrierSubset (ULift.up j)).trans
            (hcarrierBigSubset (ULift.up j)) |>.trans
            (hselectedSubset (ULift.up j)) |>.trans
            (D.selectedBlock_subset (ULift.up j))
      have hcarrierUnionWell :
          Section46.ScaledEdgeWellLinkedIn G root
            (carrier (ULift.up i) ∪ carrier (ULift.up j)) 1 2 := by
        apply Section46.ScaledEdgeWellLinkedIn.mono_terminals hselectedWell
        exact Finset.union_subset
          ((hcarrierSubset (ULift.up i)).trans
            (hcarrierBigSubset (ULift.up i)) |>.trans
            (hselectedBlockSubset (ULift.up i)))
          ((hcarrierSubset (ULift.up j)).trans
            (hcarrierBigSubset (ULift.up j)) |>.trans
            (hselectedBlockSubset (ULift.up j)))
      apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
        hdegree (by omega) (by omega) hcarrierDisjoint
        (kappa := carrierWidth) (by rw [hcarrierCard (ULift.up i)])
        (by rw [hcarrierCard (ULift.up j)])
        hcarrierUnionWell (hcarrierNode (ULift.up i))
        (hcarrierNode (ULift.up j))
        (hendpointSubset (ULift.up i)) (hendpointSubset (ULift.up j))
      rw [hendpointCard (ULift.up i)]
      calc
        2 * Delta * 2 * outWidth = 4 * Delta * outWidth := by ring
        _ ≤ carrierWidth := hlink
        _ = 1 * carrierWidth := by simp
  · have hempty : IsEmpty (Fin m) := ⟨fun i => hm ⟨i⟩⟩
    letI : IsEmpty (Fin m) := hempty
    exact ⟨{
      endpoint := isEmptyElim
      endpoint_subset := fun i => isEmptyElim i
      endpoint_card := fun i => isEmptyElim i
      endpoint_nodeWellLinked := fun i => isEmptyElim i
      endpoint_pair_nodeLinked := fun {i} => isEmptyElim i }⟩

/-! ## Adapter from the restored Claim 5.15 family -/

open ChekuriChuzhoySection5Phase1Restoration

/-- Apply the specialized Corollary 2.12 extraction to the root-side endpoint
sets of a restored Claim 5.15 family.

Distinct endpoint blocks are disjoint because the restored path packings are
mutually node-disjoint. -/
theorem exists_rootExtraction_of_restoredLeafPackingFamily
    {root targetCarrier : Finset V}
    {m q cap alphaNum alphaDen Delta groupSize
      groupedWidth carrierWidth outWidth : Nat}
    {leafRouter : Fin m -> Finset V}
    (R : RestoredLeafPackingFamily G leafRouter targetCarrier q)
    (hroot : IsCluster G root)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (htargetRoot : targetCarrier ⊆ root)
    (htargetInterface : forall i,
      R.targetSet i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G root)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G root cap alphaNum alphaDen)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : alphaDen ≤ alphaNum * groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty (RootExtraction G root R.targetSet outWidth) := by
  classical
  have htargetVertexSet :
      forall i, R.targetSet i ⊆ (R.packing i).vertexSet := by
    intro i v hv
    have hvUsed : v ∈ (R.packing i).targetSet := by
      simpa [R.exact_targetSet i] using hv
    rcases (R.packing i).exists_orient_target_eq_of_mem_targetSet hvUsed with
      ⟨k, hk⟩
    exact (R.packing i).mem_vertexSet.mpr
      ⟨k, by
        rw [← (R.packing i).orient_path_vertexSet]
        simpa [hk] using
          Lax17Proofs.SimpleGraph.GraphPath.target_mem_vertexSet
            ((R.packing i).orient.path k)⟩
  have htargetDisjoint :
      Set.PairwiseDisjoint Set.univ R.targetSet := by
    intro i _hi j _hj hij
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (R.mutuallyNodeDisjoint hij)).mono
          (htargetVertexSet i) (htargetVertexSet j)
  exact exists_rootExtraction_of_truncatedBandwidth
    R.targetSet hroot hdegree hDelta
    (fun i => (R.targetSet_subset_root i).trans htargetRoot)
    htargetInterface R.targetSet_card htargetDisjoint hband hunionCap
    hgroupSize hgroupSizeWidth hscale hgroupedWidth hcarrierWidth
    houtCarrier hlink

/-! ## Complete support-tree to root-extraction package -/

open ChekuriChuzhoySection5Phase1Bundle
open ChekuriChuzhoySection5RouterSkeleton

/-- The combined output of Claims 5.14/5.15, host restoration, and the
specialized root-router Corollary 2.12 extraction. -/
structure RestoredRootExtractionPackage
    (G : _root_.SimpleGraph V)
    {n m : Nat} (router : Fin n -> Finset V)
    (leafRouter : Fin m -> Fin n) (rootRouter : Fin n)
    (q outWidth : Nat) where
  restored :
    RestoredLeafPackingFamily G
      (fun i => router (leafRouter i))
      (ChekuriChuzhoySection5Clustering.interfaceVertices
        G (router rootRouter))
      q
  extraction :
    RootExtraction G (router rootRouter) restored.targetSet outWidth

/-- Produce the complete post-Claim-5.15 root extraction directly from the
support tree.  Every quantitative loss from Corollary 2.8, Theorem 2.11, and
Theorem 4.20 is an explicit natural-number premise. -/
theorem exists_restoredRootExtractionPackage_of_supportTree_leafFamily
    {n m : Nat} {router : Fin n -> Finset V}
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen eta replicas q groupSize
      groupedWidth carrierWidth outWidth : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (B : S.SupportBundleTransversal T (8 * Delta ^ 2 * width))
    (leafRouter : Fin m -> Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : forall i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n)
    (hrootLeaf : forall i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint :
      forall {i j : Fin n}, i ≠ j -> Disjoint (router i) (router j))
    (hrouterCluster : forall i, IsCluster G (router i))
    (hband :
      forall i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      forall i,
        1 + (T.dist rootRouter (leafRouter i) - 1) *
            (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : routerDen ≤ groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty
      (RestoredRootExtractionPackage G router leafRouter rootRouter
        q outWidth) := by
  rcases
      exists_restoredLeafPackingFamily_of_supportTree_leafFamily_interfaceRoot
        S T hT hload hdegree (by omega) B leafRouter hleafInjective hleaf
        rootRouter hrootLeaf (fun {_ _} h => hrouterDisjoint h)
        hband hcap heta hc
        hreplicasPos hreplicaValue hcapacity hthin with
    ⟨R⟩
  rcases exists_rootExtraction_of_restoredLeafPackingFamily
      R (hrouterCluster rootRouter) hdegree hDelta
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G (router rootRouter))
      R.targetSet_subset_root (hband rootRouter) hunionCap hgroupSize
      hgroupSizeWidth (by simpa using hscale) hgroupedWidth hcarrierWidth
      houtCarrier hlink with
    ⟨E⟩
  exact ⟨⟨R, E⟩⟩

end ChekuriChuzhoySection5Phase1RootExtraction
end SimpleGraph

end Lax17Proofs
