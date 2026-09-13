import Lax17Proofs.Source.ChekuriChuzhoyRootedTreeGrouping
import Lax17Proofs.Source.TreeOfSetsStrongification

namespace Lax17Proofs

universe u v w

/-!
# Source-sharp strongification of a bandwidth tree-of-sets system

This module implements the grouped, per-meta-vertex restriction from
Chekuri--Chuzhoy Lemma 4.5.  All interfaces incident with one cluster are
grouped simultaneously.  The grouping boost makes their selected union
`1/2` edge-well-linked before node-well-linked carriers are extracted, so a
pass loses one power of the input bandwidth rather than the extra power paid
by an edge-local argument.
-/

namespace SimpleGraph


open scoped Classical

namespace BandwidthTreeOfSetsSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {m w alphaNum alphaDen Delta q inWidth groupedWidth carrierWidth outWidth : ℕ}

/-- Neighbors of one meta-vertex, used as the finite block index for grouping. -/
abbrev IncidentNeighbor
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) (i : Fin m) :=
  {j : Fin m // T.metaTree.Adj i j}

/-- The result of one grouped restriction at one meta-vertex.  The input
interfaces may already have been restricted by the opposite endpoint. -/
structure MetaVertexGroupedRestriction
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (I : T.toTreeOfSetsSystem.CanonicalIndexSets) (i : Fin m)
    (outWidth : ℕ) where
  endpoint : IncidentNeighbor T i → Finset V
  endpoint_subset : ∀ j,
    endpoint j ⊆ T.toTreeOfSetsSystem.restrictedInterface I i j.1 j.2
  endpoint_card : ∀ j, (endpoint j).card = outWidth
  endpoint_nodeWellLinked : ∀ j,
    NodeWellLinkedIn G (T.cluster i) (endpoint j)
  endpoint_pair_nodeLinked : ∀ j k, j.1 ≠ k.1 →
    NodeLinkedIn G (T.cluster i) (endpoint j) (endpoint k)

/-- Exact subblocks selected from a block-grouping conclusion. -/
noncomputable def exactGroupedBlock
    {J : Type u} [Fintype J]
    {C : Finset V} {block : J → Finset V} {q s : ℕ}
    (D : ChekuriChuzhoyCorollary28.BlockGroupingConclusion G C block q)
    (hs : ∀ j, s ≤ (D.selectedBlock j).card) (j : J) : Finset V :=
  (Finset.exists_subset_card_eq (hs j)).choose

theorem exactGroupedBlock_subset
    {J : Type u} [Fintype J]
    {C : Finset V} {block : J → Finset V} {q s : ℕ}
    (D : ChekuriChuzhoyCorollary28.BlockGroupingConclusion G C block q)
    (hs : ∀ j, s ≤ (D.selectedBlock j).card) (j : J) :
    exactGroupedBlock D hs j ⊆ D.selectedBlock j :=
  (Finset.exists_subset_card_eq (hs j)).choose_spec.1

theorem exactGroupedBlock_card
    {J : Type u} [Fintype J]
    {C : Finset V} {block : J → Finset V} {q s : ℕ}
    (D : ChekuriChuzhoyCorollary28.BlockGroupingConclusion G C block q)
    (hs : ∀ j, s ≤ (D.selectedBlock j).card) (j : J) :
  (exactGroupedBlock D hs j).card = s :=
  (Finset.exists_subset_card_eq (hs j)).choose_spec.2

/-- Canonical connector restrictions are monotone at both oriented endpoints. -/
theorem restrictedInterface_mono_of_indexSets
    (T : TreeOfSetsSystem G m w) (I J : T.CanonicalIndexSets)
    (hIJ : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j) (hij_lt : i < j),
      I i j hij hij_lt ⊆ J i j hij hij_lt)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    T.restrictedInterface I i j hij ⊆ T.restrictedInterface J i j hij := by
  classical
  by_cases hij_lt : i < j
  · simpa [TreeOfSetsSystem.restrictedInterface, hij_lt] using
      (T.connector i j hij).sourceSet_mono (hIJ i j hij hij_lt)
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt hij_lt) hij.ne.symm
    simpa [TreeOfSetsSystem.restrictedInterface, hij_lt, hji] using
      (T.connector j i (T.metaTree.symm hij)).targetSet_mono
        (hIJ j i (T.metaTree.symm hij) hji)

private theorem finTwo_eq_zero_of_ne_one (x : Fin 2) (hx : x ≠ 1) : x = 0 := by
  apply Fin.ext
  omega

private theorem color_one_of_adj_color_zero
    {M : Type*} {H : _root_.SimpleGraph M} (color : H.Coloring (Fin 2))
    {i j : M} (hij : H.Adj i j) (hi : color i = 0) : color j = 1 := by
  apply Fin.eq_one_of_ne_zero
  intro hj
  exact color.valid hij (by simpa [hi, hj])

private theorem color_zero_of_adj_color_one
    {M : Type*} {H : _root_.SimpleGraph M} (color : H.Coloring (Fin 2))
    {i j : M} (hij : H.Adj i j) (hi : color i = 1) : color j = 0 := by
  apply finTwo_eq_zero_of_ne_one
  intro hj
  exact color.valid hij (by simpa [hi, hj])

/-- One simultaneous grouped restriction at a cluster.  The first inequality
is Corollary 2.11's per-block quota, the second is Theorem 2.14's
node-well-linked extraction, and the last two equalize the interfaces and
supply Theorem 4.21's pairwise linking bound. -/
theorem exists_metaVertexGroupedRestriction
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (I : T.toTreeOfSetsSystem.CanonicalIndexSets) (i : Fin m)
    (hcurrent : ∀ j : IncidentNeighbor T i,
      (T.toTreeOfSetsSystem.restrictedInterface I i j.1 j.2).card = inWidth)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (hq : 0 < q) (hqWidth : q ≤ inWidth)
    (hscale : alphaDen ≤ alphaNum * q)
    (hgroupWidth : groupedWidth ≤ inWidth / (3 * q))
    (hextract : carrierWidth ≤ (3 * groupedWidth) / (20 * Delta))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty (MetaVertexGroupedRestriction T I i outWidth) := by
  classical
  let J := ULift.{u} (IncidentNeighbor T i)
  let block : J → Finset V := fun j =>
    T.toTreeOfSetsSystem.restrictedInterface I i j.down.1 j.down.2
  let terminals : Finset V := Finset.univ.biUnion block
  by_cases hJ : Nonempty J
  · let j0 : J := Classical.choice hJ
    have hqTerminals : q ≤ terminals.card := by
      have hsub : block j0 ⊆ terminals := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨j0, Finset.mem_univ _, hx⟩
      exact hqWidth.trans <| by
        rw [← hcurrent j0.down]
        exact Finset.card_le_card hsub
    have hterminalsCluster : terminals ⊆ T.cluster i := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
      exact T.toTreeOfSetsSystem.restrictedInterface_subset_cluster
        I i j.down.1 j.down.2 hxj
    have hterminalsWell :
        Section46.ScaledEdgeWellLinkedIn G (T.cluster i) terminals
          alphaNum alphaDen := by
      apply Section46.ScaledEdgeWellLinkedIn.mono_terminals
        (T.boundaryReserve_scaledEdgeWellLinked i)
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
      exact T.interface_subset_boundaryReserve i j.down.1 j.down.2 <|
        T.toTreeOfSetsSystem.restrictedInterface_subset_interface
          I i j.down.1 j.down.2 hxj
    have hblockDisjoint : Set.PairwiseDisjoint Set.univ block := by
      intro j _hj k _hk hjk
      apply T.toTreeOfSetsSystem.restrictedInterface_disjoint I j.down.2 k.down.2
      intro h
      apply hjk
      cases j with
      | up j =>
        cases k with
        | up k =>
          exact congrArg ULift.up (Subtype.ext h)
    rcases ChekuriChuzhoyRootedTreeGrouping.exists_treeGrouping_of_connected
        (G := G) (C := T.cluster i) (U := terminals) hq
        (T.cluster_connected i) hterminalsCluster hqTerminals with
      ⟨K, hKFintype, hKDecidableEq, ⟨R⟩⟩
    letI : Fintype K := hKFintype
    letI : DecidableEq K := hKDecidableEq
    rcases ChekuriChuzhoyCorollary28.TreeGrouping.blockGroupingConclusion
        R block hblockDisjoint (by rfl) hq hterminalsWell hscale with ⟨D⟩
    have hselected : ∀ j, groupedWidth ≤ (D.selectedBlock j).card := by
      intro j
      exact hgroupWidth.trans <| by
        rw [← hcurrent j.down]
        exact D.selectedBlock_card j
    let selected : J → Finset V := fun j =>
      exactGroupedBlock (s := groupedWidth) D hselected j
    have hselectedSub : ∀ j, selected j ⊆ D.selectedBlock j :=
      fun j => exactGroupedBlock_subset D hselected j
    have hselectedCard : ∀ j, (selected j).card = groupedWidth :=
      fun j => exactGroupedBlock_card (s := groupedWidth) D hselected j
    have hselectedUnionSub :
        Finset.univ.biUnion selected ⊆ Finset.univ.biUnion D.selectedBlock := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, hselectedSub j hxj⟩
    have hselectedWell :
        Section46.ScaledEdgeWellLinkedIn G (T.cluster i)
          (Finset.univ.biUnion selected) 1 2 :=
      Section46.ScaledEdgeWellLinkedIn.mono_terminals
        D.union_scaledEdgeWellLinked hselectedUnionSub
    have hselectedBlockSub : ∀ j, selected j ⊆ Finset.univ.biUnion selected := by
      intro j x hx
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩
    have hselectedBlockWell : ∀ j,
        Section46.ScaledEdgeWellLinkedIn G (T.cluster i) (selected j) 1 2 :=
      fun j => Section46.ScaledEdgeWellLinkedIn.mono_terminals hselectedWell
        (hselectedBlockSub j)
    choose carrierBig hcarrierBigSub hcarrierLarge hcarrierBigNode using fun j =>
      ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
        (G := G) (C := T.cluster i) (T := selected j)
        (alphaNum := 1) (alphaDen := 2) (Δ := Delta) (κ := groupedWidth)
        (T.cluster_connected i) hdegree hDelta (by omega) (by omega)
        (hselectedCard j) (hselectedBlockWell j)
    have hcarrierWidth : ∀ j, carrierWidth ≤ (carrierBig j).card := by
      intro j
      calc
        carrierWidth ≤ (3 * groupedWidth) / (20 * Delta) := hextract
        _ = (3 * 1 * groupedWidth) / (10 * Delta * 2) := by
          congr 1 <;> ring
        _ ≤ (carrierBig j).card := hcarrierLarge j
    choose carrier hcarrierSub hcarrierCard using fun j =>
      Finset.exists_subset_card_eq (hcarrierWidth j)
    have hcarrierNode : ∀ j,
        NodeWellLinkedIn G (T.cluster i) (carrier j) :=
      fun j => (hcarrierBigNode j).mono_terminals (hcarrierSub j)
    have hendpointExists : ∀ j, ∃ endpoint ⊆ carrier j,
        endpoint.card = outWidth := by
      intro j
      exact Finset.exists_subset_card_eq (by simpa [hcarrierCard j] using houtCarrier)
    choose endpoint hendpointSub hendpointCard using hendpointExists
    refine ⟨{
      endpoint := fun j => endpoint (ULift.up j)
      endpoint_subset := ?_
      endpoint_card := fun j => hendpointCard (ULift.up j)
      endpoint_nodeWellLinked := ?_
      endpoint_pair_nodeLinked := ?_ }⟩
    · intro j
      exact (hendpointSub (ULift.up j)).trans (hcarrierSub (ULift.up j)) |>.trans
        (hcarrierBigSub (ULift.up j)) |>.trans
        (hselectedSub (ULift.up j)) |>.trans (D.selectedBlock_subset (ULift.up j))
    · intro j
      exact (hcarrierNode (ULift.up j)).mono_terminals (hendpointSub (ULift.up j))
    · intro j k hjk
      have hcarrierDisjoint :
          Disjoint (carrier (ULift.up j)) (carrier (ULift.up k)) := by
        apply (T.toTreeOfSetsSystem.restrictedInterface_disjoint I j.2 k.2 hjk).mono
        · exact (hcarrierSub (ULift.up j)).trans
            (hcarrierBigSub (ULift.up j)) |>.trans
            (hselectedSub (ULift.up j)) |>.trans
            (D.selectedBlock_subset (ULift.up j))
        · exact (hcarrierSub (ULift.up k)).trans
            (hcarrierBigSub (ULift.up k)) |>.trans
            (hselectedSub (ULift.up k)) |>.trans
            (D.selectedBlock_subset (ULift.up k))
      have hcarrierUnionWell :
          Section46.ScaledEdgeWellLinkedIn G (T.cluster i)
            (carrier (ULift.up j) ∪ carrier (ULift.up k)) 1 2 := by
        apply Section46.ScaledEdgeWellLinkedIn.mono_terminals hselectedWell
        exact Finset.union_subset
          ((hcarrierSub (ULift.up j)).trans (hcarrierBigSub (ULift.up j)) |>.trans
            (hselectedBlockSub (ULift.up j)))
          ((hcarrierSub (ULift.up k)).trans (hcarrierBigSub (ULift.up k)) |>.trans
            (hselectedBlockSub (ULift.up k)))
      apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
        hdegree (by omega) (by omega) hcarrierDisjoint
        (kappa := carrierWidth) (by rw [hcarrierCard (ULift.up j)])
        (by rw [hcarrierCard (ULift.up k)])
        hcarrierUnionWell (hcarrierNode (ULift.up j)) (hcarrierNode (ULift.up k))
        (hendpointSub (ULift.up j)) (hendpointSub (ULift.up k))
      rw [hendpointCard (ULift.up j)]
      calc
        2 * Delta * 2 * outWidth = 4 * Delta * outWidth := by ring
        _ ≤ carrierWidth := hlink
        _ = 1 * carrierWidth := by simp
  · have hJempty : IsEmpty J := ⟨fun j => hJ ⟨j⟩⟩
    letI : IsEmpty J := hJempty
    letI : IsEmpty (IncidentNeighbor T i) :=
      ⟨fun j => hJ ⟨ULift.up j⟩⟩
    exact ⟨{
      endpoint := isEmptyElim
      endpoint_subset := fun j => isEmptyElim j
      endpoint_card := fun j => isEmptyElim j
      endpoint_nodeWellLinked := fun j => isEmptyElim j
      endpoint_pair_nodeLinked := fun j => isEmptyElim j }⟩

/-- Source-sharp two-pass strongification of a bandwidth tree-of-sets system.

The meta-tree is two-colored.  The first pass processes every color-zero
cluster and restricts each connector at that endpoint.  The second pass does
the same at every color-one cluster.  Each meta-edge is therefore restricted
once at each endpoint, while the second canonical index set is a subset of
the first, preserving the color-zero linkedness certificates. -/
theorem exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp_with_same_clusters
    {q0 groupedWidth0 carrierWidth0 passWidth
      q1 groupedWidth1 carrierWidth1 W : ℕ}
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (hq0 : 0 < q0) (hq0Width : q0 ≤ w)
    (hscale0 : alphaDen ≤ alphaNum * q0)
    (hgroupWidth0 : groupedWidth0 ≤ w / (3 * q0))
    (hextract0 : carrierWidth0 ≤ (3 * groupedWidth0) / (20 * Delta))
    (hpassCarrier : passWidth ≤ carrierWidth0)
    (hlink0 : 4 * Delta * passWidth ≤ carrierWidth0)
    (hq1 : 0 < q1) (hq1Width : q1 ≤ passWidth)
    (hscale1 : alphaDen ≤ alphaNum * q1)
    (hgroupWidth1 : groupedWidth1 ≤ passWidth / (3 * q1))
    (hextract1 : carrierWidth1 ≤ (3 * groupedWidth1) / (20 * Delta))
    (hWCarrier : W ≤ carrierWidth1)
    (hlink1 : 4 * Delta * W ≤ carrierWidth1)
    (hWpos : 0 < W) :
    ∃ S : StrongTreeOfSetsSystem G m W,
      ∀ i : Fin m, S.cluster i = T.cluster i := by
  classical
  let I0 : T.toTreeOfSetsSystem.CanonicalIndexSets :=
    fun _ _ _ _ => Finset.univ
  have hcurrent0 : ∀ i : Fin m, ∀ j : IncidentNeighbor T i,
      (T.toTreeOfSetsSystem.restrictedInterface I0 i j.1 j.2).card = w := by
    intro i j
    rw [T.toTreeOfSetsSystem.restrictedInterface_card]
    by_cases hij_lt : i < j.1
    · simp only [dif_pos hij_lt, I0, Finset.card_univ]
      change (T.connector i j.1 j.2).card = w
      exact T.connector_card i j.1 j.2
    · have hji : j.1 < i :=
        lt_of_le_of_ne (le_of_not_gt hij_lt) j.2.ne.symm
      simp only [dif_neg hij_lt, I0, Finset.card_univ]
      change (T.connector j.1 i (T.metaTree.symm j.2)).card = w
      exact T.connector_card j.1 i (T.metaTree.symm j.2)
  let first : ∀ i : Fin m,
      MetaVertexGroupedRestriction T I0 i passWidth :=
    fun i => Classical.choice <|
      T.exists_metaVertexGroupedRestriction I0 i (hcurrent0 i)
        hdegree hDelta hq0 hq0Width hscale0 hgroupWidth0 hextract0
        hpassCarrier hlink0
  have hfirst_subset : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j),
      (first i).endpoint ⟨j, hij⟩ ⊆ T.interface i j hij := by
    intro i j hij
    exact (first i).endpoint_subset ⟨j, hij⟩ |>.trans
      (T.toTreeOfSetsSystem.restrictedInterface_subset_interface I0 i j hij)
  let color : T.metaTree.Coloring (Fin 2) := T.meta_isTree.coloringTwo
  let I1 : T.toTreeOfSetsSystem.CanonicalIndexSets := fun i j hij _ =>
    if hi : color i = 0 then
      (T.connector i j hij).sourceIndexSetOfSubset
        ((first i).endpoint ⟨j, hij⟩)
    else
      (T.connector i j hij).targetIndexSetOfSubset
        ((first j).endpoint ⟨i, T.metaTree.symm hij⟩)
  have hI1card : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j) (hij_lt : i < j),
      (I1 i j hij hij_lt).card = passWidth := by
    intro i j hij hij_lt
    by_cases hi : color i = 0
    · simpa [I1, hi, (first i).endpoint_card ⟨j, hij⟩] using
        (T.connector i j hij).sourceIndexSetOfSubset_card (hfirst_subset i j hij)
    · simpa [I1, hi, (first j).endpoint_card ⟨i, T.metaTree.symm hij⟩] using
        (T.connector i j hij).targetIndexSetOfSubset_card
          (hfirst_subset j i (T.metaTree.symm hij))
  have hI1_endpoint : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j)
      (hi : color i = 0),
      T.toTreeOfSetsSystem.restrictedInterface I1 i j hij =
        (first i).endpoint ⟨j, hij⟩ := by
    intro i j hij hi
    by_cases hij_lt : i < j
    · simpa [TreeOfSetsSystem.restrictedInterface, I1, hij_lt, hi] using
        (T.connector i j hij).sourceSet_sourceIndexSetOfSubset
          (hfirst_subset i j hij)
    · have hji : j < i :=
        lt_of_le_of_ne (le_of_not_gt hij_lt) hij.ne.symm
      have hj : color j = 1 :=
        color_one_of_adj_color_zero color hij hi
      have hj0 : color j ≠ 0 := by omega
      simpa [TreeOfSetsSystem.restrictedInterface, I1, hij_lt, hji, hj0] using
        (T.connector j i (T.metaTree.symm hij)).targetSet_targetIndexSetOfSubset
          (hfirst_subset i j hij)
  have hcurrent1 : ∀ i : Fin m, ∀ j : IncidentNeighbor T i,
      (T.toTreeOfSetsSystem.restrictedInterface I1 i j.1 j.2).card = passWidth := by
    intro i j
    rw [T.toTreeOfSetsSystem.restrictedInterface_card]
    by_cases hij_lt : i < j.1
    · simpa [hij_lt] using hI1card i j.1 j.2 hij_lt
    · have hji : j.1 < i :=
        lt_of_le_of_ne (le_of_not_gt hij_lt) j.2.ne.symm
      simpa [hij_lt, hji] using hI1card j.1 i (T.metaTree.symm j.2) hji
  let second : ∀ i : Fin m,
      MetaVertexGroupedRestriction T I1 i W :=
    fun i => Classical.choice <|
      T.exists_metaVertexGroupedRestriction I1 i (hcurrent1 i)
        hdegree hDelta hq1 hq1Width hscale1 hgroupWidth1 hextract1
        hWCarrier hlink1
  have hsecond_subset : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j),
      (second i).endpoint ⟨j, hij⟩ ⊆
        T.toTreeOfSetsSystem.restrictedInterface I1 i j hij := by
    intro i j hij
    exact (second i).endpoint_subset ⟨j, hij⟩
  let I2 : T.toTreeOfSetsSystem.CanonicalIndexSets := fun i j hij _ =>
    if hi : color i = 1 then
      (T.connector i j hij).sourceIndexSetOfSubset
        ((second i).endpoint ⟨j, hij⟩)
    else
      (T.connector i j hij).targetIndexSetOfSubset
        ((second j).endpoint ⟨i, T.metaTree.symm hij⟩)
  have hsecond_subset_interface : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j),
      (second i).endpoint ⟨j, hij⟩ ⊆ T.interface i j hij := by
    intro i j hij
    exact (hsecond_subset i j hij).trans
      (T.toTreeOfSetsSystem.restrictedInterface_subset_interface I1 i j hij)
  have hI2card : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j) (hij_lt : i < j),
      (I2 i j hij hij_lt).card = W := by
    intro i j hij hij_lt
    by_cases hi : color i = 1
    · simpa [I2, hi, (second i).endpoint_card ⟨j, hij⟩] using
        (T.connector i j hij).sourceIndexSetOfSubset_card
          (hsecond_subset_interface i j hij)
    · simpa [I2, hi, (second j).endpoint_card ⟨i, T.metaTree.symm hij⟩] using
        (T.connector i j hij).targetIndexSetOfSubset_card
          (hsecond_subset_interface j i (T.metaTree.symm hij))
  have hI2_subset_I1 : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j)
      (hij_lt : i < j), I2 i j hij hij_lt ⊆ I1 i j hij hij_lt := by
    intro i j hij hij_lt
    by_cases hi : color i = 1
    · have hsource : (second i).endpoint ⟨j, hij⟩ ⊆
          (T.connector i j hij).sourceSet (I1 i j hij hij_lt) := by
        simpa only [TreeOfSetsSystem.restrictedInterface, dif_pos hij_lt] using
          hsecond_subset i j hij
      simpa [I2, hi] using
        (T.connector i j hij).sourceIndexSetOfSubset_subset_indexSet hsource
    · have hj_not_lt : ¬ j < i := not_lt_of_ge hij_lt.le
      have htarget : (second j).endpoint ⟨i, T.metaTree.symm hij⟩ ⊆
          (T.connector i j hij).targetSet (I1 i j hij hij_lt) := by
        simpa only [TreeOfSetsSystem.restrictedInterface, dif_neg hj_not_lt] using
          hsecond_subset j i (T.metaTree.symm hij)
      simpa [I2, hi] using
        (T.connector i j hij).targetIndexSetOfSubset_subset_indexSet htarget
  have hI2_endpoint : ∀ (i j : Fin m) (hij : T.metaTree.Adj i j)
      (hi : color i = 1),
      T.toTreeOfSetsSystem.restrictedInterface I2 i j hij =
        (second i).endpoint ⟨j, hij⟩ := by
    intro i j hij hi
    by_cases hij_lt : i < j
    · simpa [TreeOfSetsSystem.restrictedInterface, I2, hij_lt, hi] using
        (T.connector i j hij).sourceSet_sourceIndexSetOfSubset
          (hsecond_subset_interface i j hij)
    · have hji : j < i :=
        lt_of_le_of_ne (le_of_not_gt hij_lt) hij.ne.symm
      have hj : color j = 0 :=
        color_zero_of_adj_color_one color hij hi
      have hj1 : color j ≠ 1 := by omega
      simpa [TreeOfSetsSystem.restrictedInterface, I2, hij_lt, hji, hj1] using
        (T.connector j i (T.metaTree.symm hij)).targetSet_targetIndexSetOfSubset
          (hsecond_subset_interface i j hij)
  let D : TreeOfSetsSystem.StrongRestrictionData T.toTreeOfSetsSystem W := {
    width_pos := hWpos
    indexSet := I2
    indexSet_card := hI2card
    interface_nodeWellLinked := by
      intro i j hij
      by_cases hi : color i = 1
      · rw [hI2_endpoint i j hij hi]
        exact (second i).endpoint_nodeWellLinked ⟨j, hij⟩
      · have hi0 : color i = 0 := finTwo_eq_zero_of_ne_one (color i) hi
        apply (first i).endpoint_nodeWellLinked ⟨j, hij⟩ |>.mono_terminals
        rw [← hI1_endpoint i j hij hi0]
        exact restrictedInterface_mono_of_indexSets T.toTreeOfSetsSystem I2 I1
          hI2_subset_I1 i j hij
    interface_pair_nodeLinked := by
      intro i j k hij hik hjk
      by_cases hi : color i = 1
      · rw [hI2_endpoint i j hij hi, hI2_endpoint i k hik hi]
        exact (second i).endpoint_pair_nodeLinked ⟨j, hij⟩ ⟨k, hik⟩ hjk
      · have hi0 : color i = 0 := finTwo_eq_zero_of_ne_one (color i) hi
        apply NodeLinkedIn.mono_terminals
          ((first i).endpoint_pair_nodeLinked ⟨j, hij⟩ ⟨k, hik⟩ hjk)
        · rw [← hI1_endpoint i j hij hi0]
          exact restrictedInterface_mono_of_indexSets T.toTreeOfSetsSystem I2 I1
            hI2_subset_I1 i j hij
        · rw [← hI1_endpoint i k hik hi0]
          exact restrictedInterface_mono_of_indexSets T.toTreeOfSetsSystem I2 I1
            hI2_subset_I1 i k hik }
  exact ⟨D.toStrongTreeOfSetsSystem, fun _ => rfl⟩

/-- Compatibility wrapper for the source-sharp strongification theorem. -/
theorem exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp
    {q0 groupedWidth0 carrierWidth0 passWidth
      q1 groupedWidth1 carrierWidth1 W : ℕ}
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (hq0 : 0 < q0) (hq0Width : q0 ≤ w)
    (hscale0 : alphaDen ≤ alphaNum * q0)
    (hgroupWidth0 : groupedWidth0 ≤ w / (3 * q0))
    (hextract0 : carrierWidth0 ≤ (3 * groupedWidth0) / (20 * Delta))
    (hpassCarrier : passWidth ≤ carrierWidth0)
    (hlink0 : 4 * Delta * passWidth ≤ carrierWidth0)
    (hq1 : 0 < q1) (hq1Width : q1 ≤ passWidth)
    (hscale1 : alphaDen ≤ alphaNum * q1)
    (hgroupWidth1 : groupedWidth1 ≤ passWidth / (3 * q1))
    (hextract1 : carrierWidth1 ≤ (3 * groupedWidth1) / (20 * Delta))
    (hWCarrier : W ≤ carrierWidth1)
    (hlink1 : 4 * Delta * W ≤ carrierWidth1)
    (hWpos : 0 < W) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  obtain ⟨S, _hclusters⟩ :=
    exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp_with_same_clusters
      T hdegree hDelta
      hq0 hq0Width hscale0 hgroupWidth0 hextract0 hpassCarrier hlink0
      hq1 hq1Width hscale1 hgroupWidth1 hextract1 hWCarrier hlink1 hWpos
  exact ⟨S⟩

end BandwidthTreeOfSetsSystem
end SimpleGraph

end Lax17Proofs
