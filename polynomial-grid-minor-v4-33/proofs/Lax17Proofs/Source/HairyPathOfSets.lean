import Mathlib.Tactic
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.Degree

namespace Lax17Proofs

universe u v w

/-!
# Hairy path-of-sets systems

This file formalizes the hairy Path-of-Sets System definition from Section 2 of
Chuzhoy--Tan.  A hairy system consists of a strong path-of-sets system together
with one additional disjoint cluster per base cluster and a node-disjoint family
of "hair" paths connecting each base cluster to its corresponding hair cluster.
-/

namespace SimpleGraph

/-- If two large sets `A` and `B` are disjoint and a third large set `X` may
overlap them, one can thin all three to equally-sized pairwise disjoint subsets.

This is the finite-set bookkeeping used in Chuzhoy--Tan Lemma A.4 after the
cluster-splitting theorem supplies large endpoint sets `A''`, `B''`, and `X''`.
The factor `3` pays for deleting the chosen `A`- and `B`-subsets from `X`. -/
theorem exists_pairwise_disjoint_subsets_of_three_large_sets
    {V : Type*} [DecidableEq V] {A B X : Finset V} {w : ℕ}
    (hAB : Disjoint A B)
    (hA : 3 * w ≤ A.card) (hB : 3 * w ≤ B.card)
    (hX : 3 * w ≤ X.card) :
    ∃ A' B' X' : Finset V,
      A' ⊆ A ∧ B' ⊆ B ∧ X' ⊆ X ∧
        A'.card = w ∧ B'.card = w ∧ X'.card = w ∧
          Disjoint A' B' ∧ Disjoint A' X' ∧ Disjoint B' X' := by
  classical
  have hwA : w ≤ A.card := by omega
  have hwB : w ≤ B.card := by omega
  rcases Finset.exists_subset_card_eq hwA with ⟨A', hA'sub, hA'card⟩
  rcases Finset.exists_subset_card_eq hwB with ⟨B', hB'sub, hB'card⟩
  have havoid_card : (A' ∪ B').card ≤ 2 * w := by
    calc
      (A' ∪ B').card ≤ A'.card + B'.card := Finset.card_union_le A' B'
      _ = 2 * w := by omega
  have hdiff_card : w ≤ X.card - (A' ∪ B').card := by
    omega
  have hXavailable : w ≤ (X \ (A' ∪ B')).card :=
    le_trans hdiff_card (Finset.le_card_sdiff (A' ∪ B') X)
  rcases Finset.exists_subset_card_eq hXavailable with ⟨X', hX'sub_sdiff, hX'card⟩
  have hX'sub : X' ⊆ X := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hX'sub_sdiff hv)).1
  have hA'B' : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp hAB (hA'sub hvA) (hB'sub hvB)
  have hA'X' : Disjoint A' X' := by
    rw [Finset.disjoint_left]
    intro v hvA hvX
    have hvnot : v ∉ A' ∪ B' :=
      (Finset.mem_sdiff.mp (hX'sub_sdiff hvX)).2
    exact hvnot (Finset.mem_union_left B' hvA)
  have hB'X' : Disjoint B' X' := by
    rw [Finset.disjoint_left]
    intro v hvB hvX
    have hvnot : v ∉ A' ∪ B' :=
      (Finset.mem_sdiff.mp (hX'sub_sdiff hvX)).2
    exact hvnot (Finset.mem_union_right A' hvB)
  exact ⟨A', B', X', hA'sub, hB'sub, hX'sub, hA'card, hB'card,
    hX'card, hA'B', hA'X', hB'X'⟩

/-- A hairy Path-of-Sets System of length `ell` and width `w`. -/
structure HairyPathOfSetsSystem {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ) where
  /-- The underlying strong Path-of-Sets System. -/
  base : StrongPathOfSetsSystem G ell w
  /-- The additional hair clusters. -/
  hairCluster : Fin ell → Finset V
  /-- Each hair cluster is connected. -/
  hairCluster_connected : ∀ i : Fin ell, IsCluster G (hairCluster i)
  /-- Distinct hair clusters are disjoint. -/
  hairCluster_disjoint :
    ∀ ⦃i j : Fin ell⦄, i ≠ j → Disjoint (hairCluster i) (hairCluster j)
  /-- Hair clusters are disjoint from all base clusters. -/
  hairCluster_disjoint_base :
    ∀ i j : Fin ell, Disjoint (hairCluster i) (base.cluster j)
  /-- Hair clusters are disjoint from all base connectors. -/
  hairCluster_disjoint_baseConnectors :
    ∀ i j : Fin ell, ∀ hj : j.1 + 1 < ell,
      Disjoint (hairCluster i) (base.connector j hj).toPathPacking.vertexSet
  /-- Base-side endpoints of the hair paths. -/
  x : Fin ell → Finset V
  /-- Hair-cluster-side endpoints of the hair paths. -/
  y : Fin ell → Finset V
  /-- Base-side hair endpoints lie in their base cluster. -/
  x_subset_cluster : ∀ i : Fin ell, x i ⊆ base.cluster i
  /-- Hair-side endpoints lie in their hair cluster. -/
  y_subset_hairCluster : ∀ i : Fin ell, y i ⊆ hairCluster i
  /-- The base-side endpoint sets have size `w`. -/
  x_card : ∀ i : Fin ell, (x i).card = w
  /-- The hair-side endpoint sets have size `w`. -/
  y_card : ∀ i : Fin ell, (y i).card = w
  /-- The base-side hair endpoints avoid the nails of their base cluster. -/
  x_disjoint_nails :
    ∀ i : Fin ell, Disjoint (x i) (base.left i ∪ base.right i)
  /-- The hair-side endpoint sets are node-well-linked in their hair clusters. -/
  y_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (hairCluster i) (y i)
  /-- The left nails and base-side hair endpoints are linked in the base cluster. -/
  left_x_nodeLinked :
    ∀ i : Fin ell, NodeLinkedIn G (base.cluster i) (base.left i) (x i)
  /-- Hair path packings connecting `x i` to `y i`. -/
  hairConnector : ∀ i : Fin ell, PerfectPathPacking G (x i) (y i)
  /-- Each hair path packing has size `w`. -/
  hairConnector_card :
    ∀ i : Fin ell, (hairConnector i).card = w
  /-- Hair path families for different indices are mutually node-disjoint. -/
  hairConnector_mutually_nodeDisjoint :
    ∀ ⦃i j : Fin ell⦄, i ≠ j →
      (hairConnector i).toPathPacking.MutuallyNodeDisjoint
        (hairConnector j).toPathPacking
  /-- Hair paths are node-disjoint from all base connector paths. -/
  hairConnector_disjoint_baseConnectors :
    ∀ (i j : Fin ell) (hj : j.1 + 1 < ell),
      (hairConnector i).toPathPacking.MutuallyNodeDisjoint
        (base.connector j hj).toPathPacking
  /-- Hair paths are internally disjoint from all base clusters. -/
  hairConnector_internally_disjoint_baseClusters :
    ∀ i j : Fin ell,
      (hairConnector i).toPathPacking.InternallyDisjointFromSet (base.cluster j)
  /-- Hair paths are internally disjoint from all hair clusters. -/
  hairConnector_internally_disjoint_hairClusters :
    ∀ i j : Fin ell,
      (hairConnector i).toPathPacking.InternallyDisjointFromSet (hairCluster j)

namespace HairyPathOfSetsSystem

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {ell w : ℕ}

/-- A chosen `w'`-element subset of the hair-connector paths for cluster `i`. -/
noncomputable def hairConnectorIndexSet (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    Finset (H.hairConnector i).Index :=
  Classical.choose ((H.hairConnector i).exists_indexSet_card_eq (by
    simpa [H.hairConnector_card i] using hle))

@[simp] theorem hairConnectorIndexSet_card
    (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (H.hairConnectorIndexSet hle i).card = w' :=
  (Classical.choose_spec ((H.hairConnector i).exists_indexSet_card_eq (by
    simpa [H.hairConnector_card i] using hle))).1

/-- Base-side hair endpoints after restricting the hair connector family to
`w'` paths. -/
noncomputable def xTrim (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  (H.hairConnector i).sourceSet (H.hairConnectorIndexSet hle i)

/-- Hair-side endpoints after restricting the hair connector family to `w'`
paths. -/
noncomputable def yTrim (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) : Finset V :=
  (H.hairConnector i).targetSet (H.hairConnectorIndexSet hle i)

theorem xTrim_subset_x (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    H.xTrim hle i ⊆ H.x i :=
  (H.hairConnector i).sourceSet_subset_left (H.hairConnectorIndexSet hle i)

theorem yTrim_subset_y (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    H.yTrim hle i ⊆ H.y i :=
  (H.hairConnector i).targetSet_subset_right (H.hairConnectorIndexSet hle i)

@[simp] theorem xTrim_card (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (H.xTrim hle i).card = w' := by
  simp [xTrim]

@[simp] theorem yTrim_card (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hle : w' ≤ w) (i : Fin ell) :
    (H.yTrim hle i).card = w' := by
  simp [yTrim]

/-- Restrict the width of a hairy path-of-sets system.  The base strong system
is width-restricted using its connector paths, while each hair connector is
restricted to a selected `w'`-element subfamily and the associated endpoint
sets. -/
noncomputable def restrictWidth (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hpos : 0 < w') (hle : w' ≤ w) :
    HairyPathOfSetsSystem G ell w' where
  base := H.base.restrictWidth hpos hle
  hairCluster := H.hairCluster
  hairCluster_connected := H.hairCluster_connected
  hairCluster_disjoint := H.hairCluster_disjoint
  hairCluster_disjoint_base := H.hairCluster_disjoint_base
  hairCluster_disjoint_baseConnectors := by
    intro i j hj
    rw [Finset.disjoint_left]
    intro v hvHair hvConn
    have hvConnRestrict :
        v ∈ (((H.base.connector j hj).restrictIndexSet
          (H.base.connectorIndexSet hle j hj)).toPathPacking.vertexSet) := by
      simpa [StrongPathOfSetsSystem.restrictWidth, PathOfSetsSystem.restrictWidth]
        using hvConn
    have hvConnOld :
        v ∈ (H.base.connector j hj).toPathPacking.vertexSet :=
      (H.base.connector j hj).restrictIndexSet_vertexSet_subset
        (H.base.connectorIndexSet hle j hj) hvConnRestrict
    exact Finset.disjoint_left.mp
      (H.hairCluster_disjoint_baseConnectors i j hj) hvHair hvConnOld
  x := H.xTrim hle
  y := H.yTrim hle
  x_subset_cluster := by
    intro i v hv
    exact H.x_subset_cluster i (H.xTrim_subset_x hle i hv)
  y_subset_hairCluster := by
    intro i v hv
    exact H.y_subset_hairCluster i (H.yTrim_subset_y hle i hv)
  x_card := H.xTrim_card hle
  y_card := H.yTrim_card hle
  x_disjoint_nails := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvx hvnail
    have hvx_old : v ∈ H.x i := H.xTrim_subset_x hle i hvx
    have hvnail_old : v ∈ H.base.left i ∪ H.base.right i := by
      rcases Finset.mem_union.mp hvnail with hvleft | hvright
      · exact Finset.mem_union_left _ <|
          H.base.toPathOfSetsSystem.leftTrim_subset_left hle i hvleft
      · exact Finset.mem_union_right _ <|
          H.base.toPathOfSetsSystem.rightTrim_subset_right hle i hvright
    exact Finset.disjoint_left.mp (H.x_disjoint_nails i) hvx_old hvnail_old
  y_nodeWellLinked := by
    intro i
    exact (H.y_nodeWellLinked i).mono_terminals (H.yTrim_subset_y hle i)
  left_x_nodeLinked := by
    intro i
    exact (H.left_x_nodeLinked i).mono_terminals
      (H.base.toPathOfSetsSystem.leftTrim_subset_left hle i)
      (H.xTrim_subset_x hle i)
  hairConnector := fun i =>
    (H.hairConnector i).restrictIndexSet (H.hairConnectorIndexSet hle i)
  hairConnector_card := by
    intro i
    change Fintype.card
        {a : (H.hairConnector i).Index // a ∈ H.hairConnectorIndexSet hle i} = w'
    simp
  hairConnector_mutually_nodeDisjoint := by
    intro i j hij a b
    simpa [PerfectPathPacking.restrictIndexSet, GraphPath.NodeDisjoint] using
      H.hairConnector_mutually_nodeDisjoint hij a.1 b.1
  hairConnector_disjoint_baseConnectors := by
    intro i j hj a b
    simpa [PathOfSetsSystem.restrictWidth, PerfectPathPacking.copyTerminals,
      PerfectPathPacking.restrictIndexSet, GraphPath.NodeDisjoint] using
      H.hairConnector_disjoint_baseConnectors i j hj a.1 b.1
  hairConnector_internally_disjoint_baseClusters := by
    intro i j a
    simpa [PerfectPathPacking.restrictIndexSet] using
      H.hairConnector_internally_disjoint_baseClusters i j a.1
  hairConnector_internally_disjoint_hairClusters := by
    intro i j a
    simpa [PerfectPathPacking.restrictIndexSet] using
      H.hairConnector_internally_disjoint_hairClusters i j a.1

/-- Restrict a hairy path-of-sets system to its first `ell'` clusters. -/
noncomputable def restrictLength (H : HairyPathOfSetsSystem G ell w)
    {ell' : ℕ} (hpos : 0 < ell') (hle : ell' ≤ ell) :
    HairyPathOfSetsSystem G ell' w where
  base := H.base.restrictLength hpos hle
  hairCluster := fun i => H.hairCluster (Fin.castLE hle i)
  hairCluster_connected := fun i => H.hairCluster_connected (Fin.castLE hle i)
  hairCluster_disjoint := by
    intro i j hij
    apply H.hairCluster_disjoint
    intro h
    apply hij
    exact Fin.ext (by simpa [Fin.val_castLE] using congrArg Fin.val h)
  hairCluster_disjoint_base := by
    intro i j
    exact H.hairCluster_disjoint_base (Fin.castLE hle i) (Fin.castLE hle j)
  hairCluster_disjoint_baseConnectors := by
    intro i j hj
    have hj' : (Fin.castLE hle j).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hj hle
    simpa [StrongPathOfSetsSystem.restrictLength, PathOfSetsSystem.restrictLength,
      Fin.val_castLE] using
      H.hairCluster_disjoint_baseConnectors
        (Fin.castLE hle i) (Fin.castLE hle j) hj'
  x := fun i => H.x (Fin.castLE hle i)
  y := fun i => H.y (Fin.castLE hle i)
  x_subset_cluster := fun i => H.x_subset_cluster (Fin.castLE hle i)
  y_subset_hairCluster := fun i => H.y_subset_hairCluster (Fin.castLE hle i)
  x_card := fun i => H.x_card (Fin.castLE hle i)
  y_card := fun i => H.y_card (Fin.castLE hle i)
  x_disjoint_nails := fun i => H.x_disjoint_nails (Fin.castLE hle i)
  y_nodeWellLinked := fun i => H.y_nodeWellLinked (Fin.castLE hle i)
  left_x_nodeLinked := fun i => H.left_x_nodeLinked (Fin.castLE hle i)
  hairConnector := fun i => H.hairConnector (Fin.castLE hle i)
  hairConnector_card := fun i => H.hairConnector_card (Fin.castLE hle i)
  hairConnector_mutually_nodeDisjoint := by
    intro i j hij
    apply H.hairConnector_mutually_nodeDisjoint
    intro h
    apply hij
    exact Fin.ext (by simpa [Fin.val_castLE] using congrArg Fin.val h)
  hairConnector_disjoint_baseConnectors := by
    intro i j hj
    have hj' : (Fin.castLE hle j).1 + 1 < ell := by
      simpa [Fin.val_castLE] using lt_of_lt_of_le hj hle
    simpa [StrongPathOfSetsSystem.restrictLength, PathOfSetsSystem.restrictLength,
      Fin.val_castLE] using
      H.hairConnector_disjoint_baseConnectors
        (Fin.castLE hle i) (Fin.castLE hle j) hj'
  hairConnector_internally_disjoint_baseClusters := by
    intro i j
    simpa [StrongPathOfSetsSystem.restrictLength, PathOfSetsSystem.restrictLength] using
      H.hairConnector_internally_disjoint_baseClusters
        (Fin.castLE hle i) (Fin.castLE hle j)
  hairConnector_internally_disjoint_hairClusters := by
    intro i j
    exact H.hairConnector_internally_disjoint_hairClusters
      (Fin.castLE hle i) (Fin.castLE hle j)

/-- Simultaneously restrict a hairy path-of-sets system in length and width. -/
noncomputable def restrict (H : HairyPathOfSetsSystem G ell w)
    {ell' w' : ℕ} (hell_pos : 0 < ell') (hw_pos : 0 < w')
    (hell : ell' ≤ ell) (hw : w' ≤ w) :
    HairyPathOfSetsSystem G ell' w' :=
  (H.restrictWidth hw_pos hw).restrictLength hell_pos hell

/-- A hairy path-of-sets system that is long and wide enough contains an exact
`g^2` by `g^2` hairy subsystem. -/
noncomputable def restrictSquare
    (H : HairyPathOfSetsSystem G ell w) {g : ℕ}
    (hg : 2 ≤ g) (hell : g ^ 2 ≤ ell) (hw : g ^ 2 ≤ w) :
    HairyPathOfSetsSystem G (g ^ 2) (g ^ 2) :=
  H.restrict
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    hell hw

/-- View a hairy path-of-sets system inside a same-vertex supergraph. -/
def mapLe (H : HairyPathOfSetsSystem G ell w)
    {G' : _root_.SimpleGraph V} (hGG' : G ≤ G') :
    HairyPathOfSetsSystem G' ell w where
  base := H.base.mapLe hGG'
  hairCluster := H.hairCluster
  hairCluster_connected := by
    intro i
    exact IsCluster.mono_graph (H.hairCluster_connected i) hGG'
  hairCluster_disjoint := H.hairCluster_disjoint
  hairCluster_disjoint_base := H.hairCluster_disjoint_base
  hairCluster_disjoint_baseConnectors := by
    intro i j hj
    simpa [StrongPathOfSetsSystem.mapLe, PathOfSetsSystem.mapLe] using
      H.hairCluster_disjoint_baseConnectors i j hj
  x := H.x
  y := H.y
  x_subset_cluster := H.x_subset_cluster
  y_subset_hairCluster := H.y_subset_hairCluster
  x_card := H.x_card
  y_card := H.y_card
  x_disjoint_nails := H.x_disjoint_nails
  y_nodeWellLinked := by
    intro i
    exact NodeWellLinkedIn.mono_graph (H.y_nodeWellLinked i) hGG'
  left_x_nodeLinked := by
    intro i
    exact NodeLinkedIn.mono_graph (H.left_x_nodeLinked i) hGG'
  hairConnector := fun i => (H.hairConnector i).mapLe hGG'
  hairConnector_card := by
    intro i
    simpa using H.hairConnector_card i
  hairConnector_mutually_nodeDisjoint := by
    intro i j hij a b
    change GraphPath.NodeDisjoint
      (((H.hairConnector i).path a).mapLe hGG')
      (((H.hairConnector j).path b).mapLe hGG')
    simpa [GraphPath.NodeDisjoint] using
      H.hairConnector_mutually_nodeDisjoint hij a b
  hairConnector_disjoint_baseConnectors := by
    intro i j hj a b
    change GraphPath.NodeDisjoint
      (((H.hairConnector i).path a).mapLe hGG')
      (((H.base.connector j hj).path b).mapLe hGG')
    simpa [GraphPath.NodeDisjoint] using
      H.hairConnector_disjoint_baseConnectors i j hj a b
  hairConnector_internally_disjoint_baseClusters := by
    intro i j a
    change (((H.hairConnector i).path a).mapLe hGG').InternallyDisjointFromSet
      (H.base.cluster j)
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      H.hairConnector_internally_disjoint_baseClusters i j a
  hairConnector_internally_disjoint_hairClusters := by
    intro i j a
    change (((H.hairConnector i).path a).mapLe hGG').InternallyDisjointFromSet
      (H.hairCluster j)
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      H.hairConnector_internally_disjoint_hairClusters i j a

/-- The local graph on a base cluster after adding the corresponding hair
connector paths. -/
noncomputable def hairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    _root_.SimpleGraph V :=
  clusterWithPackingGraph G (H.base.cluster i) (H.x i) (H.y i)
    (H.hairConnector i).toPathPacking

/-- The local graph around a hair connector is a subgraph of the ambient graph. -/
theorem hairLocalGraph_le
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    H.hairLocalGraph i ≤ G :=
  clusterWithPackingGraph_le (H.hairConnector i).toPathPacking

/-- Base-side hair terminals lie on the corresponding hair-connector packing. -/
theorem x_subset_hairConnector_vertexSet
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    H.x i ⊆ (H.hairConnector i).toPathPacking.vertexSet := by
  intro v hv
  let a := (H.hairConnector i).indexOfSource ⟨v, hv⟩
  have hsource : ((H.hairConnector i).path a).source = v := by
    have h :=
      congrArg Subtype.val
        ((H.hairConnector i).source_indexOfSource ⟨v, hv⟩)
    simpa [a] using h
  exact ((H.hairConnector i).toPathPacking.mem_vertexSet).2
    ⟨a, by simpa [hsource] using
      GraphPath.source_mem_vertexSet ((H.hairConnector i).path a)⟩

/-- Hair-side terminals lie on the corresponding hair-connector packing. -/
theorem y_subset_hairConnector_vertexSet
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    H.y i ⊆ (H.hairConnector i).toPathPacking.vertexSet := by
  intro v hv
  let a := (H.hairConnector i).indexOfTarget ⟨v, hv⟩
  have htarget : ((H.hairConnector i).path a).target = v := by
    have h :=
      congrArg Subtype.val
        ((H.hairConnector i).target_indexOfTarget ⟨v, hv⟩)
    simpa [a] using h
  exact ((H.hairConnector i).toPathPacking.mem_vertexSet).2
    ⟨a, by simpa [htarget] using
      GraphPath.target_mem_vertexSet ((H.hairConnector i).path a)⟩

/-- A path in the hair-local graph whose source is in the local footprint stays
inside the base cluster together with the corresponding hair-connector paths. -/
theorem hairLocalGraph_path_vertexSet_subset_localVertexSet
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (Q : GraphPath (H.hairLocalGraph i))
    (hsource :
      Q.source ∈ H.base.cluster i ∪ (H.hairConnector i).toPathPacking.vertexSet) :
    Q.vertexSet ⊆
      H.base.cluster i ∪ (H.hairConnector i).toPathPacking.vertexSet := by
  simpa [hairLocalGraph, clusterWithPackingVertexSet] using
    GraphPath.vertexSet_subset_clusterWithPackingVertexSet
      (P := (H.hairConnector i).toPathPacking) Q hsource

/-- A path in the hair-local graph starting in the base cluster stays in the
local base-cluster-plus-hair-connector footprint. -/
theorem hairLocalGraph_path_vertexSet_subset_localVertexSet_of_source_mem_cluster
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (Q : GraphPath (H.hairLocalGraph i))
    (hsource : Q.source ∈ H.base.cluster i) :
    Q.vertexSet ⊆
      H.base.cluster i ∪ (H.hairConnector i).toPathPacking.vertexSet :=
  H.hairLocalGraph_path_vertexSet_subset_localVertexSet i Q
    (Finset.mem_union_left _ hsource)

/-- A path in the hair-local graph starting on a hair-connector path stays in
the local base-cluster-plus-hair-connector footprint. -/
theorem hairLocalGraph_path_vertexSet_subset_localVertexSet_of_source_mem_hairConnector
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (Q : GraphPath (H.hairLocalGraph i))
    (hsource : Q.source ∈ (H.hairConnector i).toPathPacking.vertexSet) :
    Q.vertexSet ⊆
      H.base.cluster i ∪ (H.hairConnector i).toPathPacking.vertexSet :=
  H.hairLocalGraph_path_vertexSet_subset_localVertexSet i Q
    (Finset.mem_union_right _ hsource)

/-- A hair connector is disjoint from every nonmatching base cluster. -/
theorem hairConnector_vertexSet_disjoint_baseCluster_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairConnector i).toPathPacking.vertexSet (H.base.cluster j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvConn hvCluster
  rcases ((H.hairConnector i).toPathPacking.mem_vertexSet).1 hvConn with
    ⟨a, hvPath⟩
  have hendpoint :=
    H.hairConnector_internally_disjoint_baseClusters i j a hvPath hvCluster
  rcases hendpoint with hsource | htarget
  · have hsource_cluster :
        ((H.hairConnector i).path a).source ∈ H.base.cluster i :=
      H.x_subset_cluster i ((H.hairConnector i).source_mem a)
    exact Finset.disjoint_left.mp (H.base.cluster_disjoint hij)
      hsource_cluster (by simpa [hsource] using hvCluster)
  · have htarget_hair :
        ((H.hairConnector i).path a).target ∈ H.hairCluster i :=
      H.y_subset_hairCluster i ((H.hairConnector i).target_mem a)
    exact Finset.disjoint_left.mp (H.hairCluster_disjoint_base i j)
      htarget_hair (by simpa [htarget] using hvCluster)

/-- A hair connector is disjoint from every nonmatching hair cluster. -/
theorem hairConnector_vertexSet_disjoint_hairCluster_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairConnector i).toPathPacking.vertexSet (H.hairCluster j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvConn hvHair
  rcases ((H.hairConnector i).toPathPacking.mem_vertexSet).1 hvConn with
    ⟨a, hvPath⟩
  have hendpoint :=
    H.hairConnector_internally_disjoint_hairClusters i j a hvPath hvHair
  rcases hendpoint with hsource | htarget
  · have hsource_cluster :
        ((H.hairConnector i).path a).source ∈ H.base.cluster i :=
      H.x_subset_cluster i ((H.hairConnector i).source_mem a)
    exact Finset.disjoint_left.mp (H.hairCluster_disjoint_base j i)
      hvHair (by simpa [hsource] using hsource_cluster)
  · have htarget_hair :
        ((H.hairConnector i).path a).target ∈ H.hairCluster i :=
      H.y_subset_hairCluster i ((H.hairConnector i).target_mem a)
    exact Finset.disjoint_left.mp (H.hairCluster_disjoint hij)
      htarget_hair (by simpa [htarget] using hvHair)

/-- Hair connector families for different clusters have disjoint total vertex
sets. -/
theorem hairConnector_vertexSet_disjoint_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairConnector i).toPathPacking.vertexSet
      (H.hairConnector j).toPathPacking.vertexSet :=
  PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
    (H.hairConnector_mutually_nodeDisjoint hij)

/-- The local footprint of a hair-local graph. -/
noncomputable def hairLocalVertexSet
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) : Finset V :=
  H.base.cluster i ∪ (H.hairConnector i).toPathPacking.vertexSet

/-- Local footprints of distinct hair-local graphs are disjoint. -/
theorem hairLocalVertexSet_disjoint_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairLocalVertexSet i) (H.hairLocalVertexSet j) := by
  classical
  rw [hairLocalVertexSet, hairLocalVertexSet, Finset.disjoint_left]
  intro v hvi hvj
  rcases Finset.mem_union.mp hvi with hbasei | hconni
  · rcases Finset.mem_union.mp hvj with hbasej | hconnj
    · exact Finset.disjoint_left.mp (H.base.cluster_disjoint hij)
        hbasei hbasej
    · exact Finset.disjoint_left.mp
        (H.hairConnector_vertexSet_disjoint_baseCluster_of_ne
          (i := j) (j := i) (fun h => hij h.symm))
        hconnj hbasei
  · rcases Finset.mem_union.mp hvj with hbasej | hconnj
    · exact Finset.disjoint_left.mp
        (H.hairConnector_vertexSet_disjoint_baseCluster_of_ne
          (i := i) (j := j) hij)
        hconni hbasej
    · exact Finset.disjoint_left.mp
        (H.hairConnector_vertexSet_disjoint_of_ne hij) hconni hconnj

/-- A hair-local footprint is disjoint from every nonmatching hair cluster. -/
theorem hairLocalVertexSet_disjoint_hairCluster_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairLocalVertexSet i) (H.hairCluster j) := by
  classical
  rw [hairLocalVertexSet, Finset.disjoint_left]
  intro v hvi hvj
  rcases Finset.mem_union.mp hvi with hbase | hconn
  · exact Finset.disjoint_left.mp (H.hairCluster_disjoint_base j i)
      hvj hbase
  · exact Finset.disjoint_left.mp
      (H.hairConnector_vertexSet_disjoint_hairCluster_of_ne hij)
      hconn hvj

/-- A hair-local footprint is disjoint from every nonmatching base cluster. -/
theorem hairLocalVertexSet_disjoint_baseCluster_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (H.hairLocalVertexSet i) (H.base.cluster j) := by
  classical
  rw [hairLocalVertexSet, Finset.disjoint_left]
  intro v hvi hvj
  rcases Finset.mem_union.mp hvi with hbase | hconn
  · exact Finset.disjoint_left.mp (H.base.cluster_disjoint hij) hbase hvj
  · exact Finset.disjoint_left.mp
      (H.hairConnector_vertexSet_disjoint_baseCluster_of_ne hij) hconn hvj

/-- A hair-local footprint is disjoint from a base connector whose two endpoint
clusters are both different from the hair-local base cluster. -/
theorem hairLocalVertexSet_disjoint_baseConnector_of_ne
    (H : HairyPathOfSetsSystem G ell w) {i j : Fin ell}
    (hj : j.1 + 1 < ell)
    (hij : i ≠ j) (hinext : i ≠ ⟨j.1 + 1, hj⟩) :
    Disjoint (H.hairLocalVertexSet i)
      (H.base.connector j hj).toPathPacking.vertexSet := by
  classical
  rw [hairLocalVertexSet, Finset.disjoint_left]
  intro v hvi hvConn
  rcases Finset.mem_union.mp hvi with hbase | hhair
  · exact Finset.disjoint_left.mp
      ((H.base.connector_vertexSet_disjoint_cluster_of_ne j hj i hij hinext).symm)
      hbase hvConn
  · exact Finset.disjoint_left.mp
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (H.hairConnector_disjoint_baseConnectors i j hj))
      hhair hvConn

/-- A vertex in the local hair-graph footprint that also lies in the matching
hair cluster must be one of the hair-side terminals. -/
theorem mem_y_of_mem_hairLocalVertexSet_and_hairCluster
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) {v : V}
    (hvLocal : v ∈ H.hairLocalVertexSet i)
    (hvHair : v ∈ H.hairCluster i) :
    v ∈ H.y i := by
  classical
  rw [hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvConn
  · exact False.elim
      (Finset.disjoint_left.mp (H.hairCluster_disjoint_base i i)
        hvHair hvBase)
  · rcases ((H.hairConnector i).toPathPacking.mem_vertexSet).1 hvConn with
      ⟨a, hvPath⟩
    have hend :
        ((H.hairConnector i).path a).IsEndpoint v :=
      H.hairConnector_internally_disjoint_hairClusters i i a hvPath hvHair
    rcases hend with hsource | htarget
    · have hsourceBase :
          ((H.hairConnector i).path a).source ∈ H.base.cluster i :=
        H.x_subset_cluster i ((H.hairConnector i).source_mem a)
      exact False.elim
        (Finset.disjoint_left.mp (H.hairCluster_disjoint_base i i)
          hvHair (by simpa [hsource] using hsourceBase))
    · exact by
        simpa [htarget] using (H.hairConnector i).target_mem a

/-- Width-thinning a hairy system only removes hair-connector paths from each
local graph. -/
theorem restrictWidth_hairLocalGraph_le
    (H : HairyPathOfSetsSystem G ell w)
    {w' : ℕ} (hpos : 0 < w') (hle : w' ≤ w) (i : Fin ell) :
    (H.restrictWidth hpos hle).hairLocalGraph i ≤ H.hairLocalGraph i := by
  change clusterWithPackingGraph G (H.base.cluster i)
      (H.xTrim hle i) (H.yTrim hle i)
      ((H.hairConnector i).restrictIndexSet
        (H.hairConnectorIndexSet hle i)).toPathPacking ≤
    clusterWithPackingGraph G (H.base.cluster i)
      (H.x i) (H.y i) (H.hairConnector i).toPathPacking
  exact clusterWithPackingGraph_le_of_spanningGraph_le
    ((H.hairConnector i).restrictIndexSet_spanningGraph_le
      (H.hairConnectorIndexSet hle i))

/-- The base strong system supplies a full-width linkage from the left nails to
the right nails in each cluster. -/
theorem exists_left_right_linkage
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking G (H.base.left i) (H.base.right i),
      P.card = w ∧ P.StaysIn (H.base.cluster i) := by
  rcases NodeLinkedIn.exists_pathPacking (H.base.left_right_nodeLinked i) with
    ⟨P, hcard, hstay⟩
  refine ⟨P, ?_, hstay⟩
  simpa [H.base.left_card i, H.base.right_card i] using hcard

/-- The base strong system supplies a perfect full-width linkage from the left
nails to the right nails in each cluster. -/
theorem exists_left_right_perfect_linkage
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PerfectPathPacking G (H.base.left i) (H.base.right i),
      P.card = w ∧ P.toPathPacking.StaysIn (H.base.cluster i) := by
  rcases H.exists_left_right_linkage i with ⟨P, hcard, hstay⟩
  have hleft : P.card = (H.base.left i).card :=
    hcard.trans (H.base.left_card i).symm
  have hright : P.card = (H.base.right i).card :=
    hcard.trans (H.base.right_card i).symm
  refine ⟨P.toPerfectOfCardEq hleft hright, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hcard
  · exact PathPacking.orient_staysIn hstay

/-- A hairy system supplies a full-width linkage from the left nails to the
base-side hair endpoints in each cluster. -/
theorem exists_left_x_linkage
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking G (H.base.left i) (H.x i),
      P.card = w ∧ P.StaysIn (H.base.cluster i) := by
  rcases NodeLinkedIn.exists_pathPacking (H.left_x_nodeLinked i) with
    ⟨P, hcard, hstay⟩
  refine ⟨P, ?_, hstay⟩
  simpa [H.base.left_card i, H.x_card i] using hcard

/-- A hairy system supplies a perfect full-width linkage from the left nails to
the base-side hair endpoints in each cluster. -/
theorem exists_left_x_perfect_linkage
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PerfectPathPacking G (H.base.left i) (H.x i),
      P.card = w ∧ P.toPathPacking.StaysIn (H.base.cluster i) := by
  rcases H.exists_left_x_linkage i with ⟨P, hcard, hstay⟩
  have hleft : P.card = (H.base.left i).card :=
    hcard.trans (H.base.left_card i).symm
  have hx : P.card = (H.x i).card :=
    hcard.trans (H.x_card i).symm
  refine ⟨P.toPerfectOfCardEq hleft hx, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hcard
  · exact PathPacking.orient_staysIn hstay

/-- The left-right linkage inside a base cluster can be viewed inside any
local graph formed from that cluster plus an additional path packing. -/
theorem exists_left_right_linkage_inClusterWithPackingGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    {S T : Finset V} (Q : PathPacking G S T) :
    ∃ P : PathPacking
        (clusterWithPackingGraph G (H.base.cluster i) S T Q)
        (H.base.left i) (H.base.right i),
      P.card = w := by
  rcases H.exists_left_right_linkage i with ⟨P, hcard, hstay⟩
  exact ⟨P.inClusterWithPackingGraph hstay Q, by simpa using hcard⟩

/-- The left-to-hair-base linkage inside a base cluster can be viewed inside
any local graph formed from that cluster plus an additional path packing. -/
theorem exists_left_x_linkage_inClusterWithPackingGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    {S T : Finset V} (Q : PathPacking G S T) :
    ∃ P : PathPacking
        (clusterWithPackingGraph G (H.base.cluster i) S T Q)
        (H.base.left i) (H.x i),
      P.card = w := by
  rcases H.exists_left_x_linkage i with ⟨P, hcard, hstay⟩
  exact ⟨P.inClusterWithPackingGraph hstay Q, by simpa using hcard⟩

/-- The left-to-`x` linkage is available in the local graph obtained by adding
the corresponding hair-connector paths to the base cluster. -/
theorem exists_left_x_linkage_inHairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking
        (H.hairLocalGraph i)
        (H.base.left i) (H.x i),
      P.card = w :=
  H.exists_left_x_linkage_inClusterWithPackingGraph i (H.hairConnector i).toPathPacking

/-- The local left-to-`x` linkage in the hair-local graph still stays inside
the base cluster. -/
theorem exists_left_x_linkage_inHairLocalGraph_with_staysIn
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking
        (H.hairLocalGraph i)
        (H.base.left i) (H.x i),
      P.card = w ∧ P.StaysIn (H.base.cluster i) := by
  rcases H.exists_left_x_linkage i with ⟨P, hcard, hstay⟩
  refine ⟨P.inClusterWithPackingGraph hstay
    (H.hairConnector i).toPathPacking, ?_, ?_⟩
  · simpa using hcard
  · exact PathPacking.inClusterWithPackingGraph_staysIn P hstay
      (H.hairConnector i).toPathPacking

/-- The perfect left-to-`x` linkage is available in the local graph obtained by
adding the corresponding hair-connector paths to the base cluster. -/
theorem exists_left_x_perfect_linkage_inHairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PerfectPathPacking
        (H.hairLocalGraph i)
        (H.base.left i) (H.x i),
      P.card = w := by
  rcases H.exists_left_x_perfect_linkage i with ⟨P, hcard, hstay⟩
  exact ⟨P.inClusterWithPackingGraph hstay (H.hairConnector i).toPathPacking,
    by simpa using hcard⟩

/-- The local perfect left-to-`x` linkage in the hair-local graph still stays
inside the base cluster. -/
theorem exists_left_x_perfect_linkage_inHairLocalGraph_with_staysIn
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PerfectPathPacking
        (H.hairLocalGraph i)
        (H.base.left i) (H.x i),
      P.card = w ∧ P.toPathPacking.StaysIn (H.base.cluster i) := by
  rcases H.exists_left_x_perfect_linkage i with ⟨P, hcard, hstay⟩
  refine ⟨P.inClusterWithPackingGraph hstay
    (H.hairConnector i).toPathPacking, ?_, ?_⟩
  · simpa using hcard
  · exact PerfectPathPacking.inClusterWithPackingGraph_staysIn P hstay
      (H.hairConnector i).toPathPacking

/-- The hair connector itself is available as a perfect packing in the local
graph obtained by adding its paths to the base cluster. -/
noncomputable def hairConnector_inHairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    PerfectPathPacking
        (H.hairLocalGraph i)
        (H.x i) (H.y i) :=
  (H.hairConnector i).inOwnClusterWithPackingGraph (H.base.cluster i)

@[simp] theorem hairConnector_inHairLocalGraph_card
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    (H.hairConnector_inHairLocalGraph i).card = w := by
  calc
    (H.hairConnector_inHairLocalGraph i).card = (H.hairConnector i).card := by
      change ((H.hairConnector i).inOwnClusterWithPackingGraph
        (H.base.cluster i)).card = (H.hairConnector i).card
      exact PerfectPathPacking.inOwnClusterWithPackingGraph_card
        (H.hairConnector i) (H.base.cluster i)
    _ = w := H.hairConnector_card i

@[simp] theorem hairConnector_inHairLocalGraph_path_vertexSet
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector i).Index) :
    ((H.hairConnector_inHairLocalGraph i).path a).vertexSet =
      ((H.hairConnector i).path a).vertexSet := by
  change (((H.hairConnector i).inOwnClusterWithPackingGraph
    (H.base.cluster i)).path a).vertexSet =
      ((H.hairConnector i).path a).vertexSet
  exact PerfectPathPacking.inOwnClusterWithPackingGraph_path_vertexSet
    (H.hairConnector i) (H.base.cluster i) a

@[simp] theorem hairConnector_inHairLocalGraph_path_source
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector i).Index) :
    ((H.hairConnector_inHairLocalGraph i).path a).source =
      ((H.hairConnector i).path a).source := by
  simp [hairConnector_inHairLocalGraph,
    PerfectPathPacking.inOwnClusterWithPackingGraph,
    PerfectPathPacking.inSpanningGraph, PerfectPathPacking.mapLe,
    PathPacking.inSpanningGraph, PathPacking.mapLe, PathPacking.transfer,
    GraphPath.transfer, GraphPath.mapLe]

@[simp] theorem hairConnector_inHairLocalGraph_path_target
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector i).Index) :
    ((H.hairConnector_inHairLocalGraph i).path a).target =
      ((H.hairConnector i).path a).target := by
  simp [hairConnector_inHairLocalGraph,
    PerfectPathPacking.inOwnClusterWithPackingGraph,
    PerfectPathPacking.inSpanningGraph, PerfectPathPacking.mapLe,
    PathPacking.inSpanningGraph, PathPacking.mapLe, PathPacking.transfer,
    GraphPath.transfer, GraphPath.mapLe]

/-- Hair connector paths are nontrivial: their source lies in the base cluster,
while their target lies in the disjoint hair cluster. -/
theorem hairConnector_source_ne_target
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector i).Index) :
    ((H.hairConnector i).path a).source ≠
      ((H.hairConnector i).path a).target := by
  intro h
  have hsource_cluster :
      ((H.hairConnector i).path a).source ∈ H.base.cluster i :=
    H.x_subset_cluster i ((H.hairConnector i).source_mem a)
  have htarget_hair :
      ((H.hairConnector i).path a).target ∈ H.hairCluster i :=
    H.y_subset_hairCluster i ((H.hairConnector i).target_mem a)
  exact Finset.disjoint_left.mp (H.hairCluster_disjoint_base i i)
    htarget_hair (by simpa [h] using hsource_cluster)

/-- Local-graph version of `hairConnector_source_ne_target`. -/
theorem hairConnector_inHairLocalGraph_source_ne_target
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector_inHairLocalGraph i).Index) :
    ((H.hairConnector_inHairLocalGraph i).path a).source ≠
      ((H.hairConnector_inHairLocalGraph i).path a).target := by
  simpa using H.hairConnector_source_ne_target i a

/-- The target of a local hair-connector path is adjacent to the penultimate
vertex of that path. -/
theorem hairConnector_inHairLocalGraph_target_adj_penultimate
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector_inHairLocalGraph i).Index) :
    (H.hairLocalGraph i).Adj
      ((H.hairConnector_inHairLocalGraph i).path a).target
      ((H.hairConnector_inHairLocalGraph i).path a).walk.penultimate := by
  have hne := H.hairConnector_inHairLocalGraph_source_ne_target i a
  have hnotNil :
      ¬ ((H.hairConnector_inHairLocalGraph i).path a).walk.Nil :=
    _root_.SimpleGraph.Walk.not_nil_of_ne hne
  exact (((H.hairConnector_inHairLocalGraph i).path a).walk.adj_penultimate
    hnotNil).symm

/-- The target of a local hair-connector path is adjacent to the penultimate
vertex of the original ambient hair path. -/
theorem hairConnector_inHairLocalGraph_target_adj_original_penultimate
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (a : (H.hairConnector i).Index) :
    (H.hairLocalGraph i).Adj
      ((H.hairConnector i).path a).target
      ((H.hairConnector i).path a).walk.penultimate := by
  have hne := H.hairConnector_source_ne_target i a
  have hnotNil : ¬ ((H.hairConnector i).path a).walk.Nil :=
    _root_.SimpleGraph.Walk.not_nil_of_ne hne
  have hedge :
      s(((H.hairConnector i).path a).target,
        ((H.hairConnector i).path a).walk.penultimate) ∈
          ((H.hairConnector i).path a).edgeSet := by
    have hlast :=
      ((H.hairConnector i).path a).walk.mk_penultimate_end_mem_edges hnotNil
    simpa [GraphPath.edgeSet, Sym2.eq_swap] using hlast
  have hspan :
      ((H.hairConnector i).toPathPacking.spanningGraph).Adj
        ((H.hairConnector i).path a).target
        ((H.hairConnector i).path a).walk.penultimate := by
    rw [PathPacking.spanningGraph_adj_iff_exists_path_edge]
    constructor
    · exact ⟨a, hedge⟩
    · exact (((H.hairConnector i).path a).walk.adj_penultimate hnotNil).ne.symm
  change (clusterWithPackingGraph G (H.base.cluster i) (H.x i) (H.y i)
    (H.hairConnector i).toPathPacking).Adj
      ((H.hairConnector i).path a).target
      ((H.hairConnector i).path a).walk.penultimate
  exact Or.inr hspan

/-- Every `y_i` endpoint has a neighbor in the hair-local graph, namely the
penultimate vertex on its unique hair-connector path. -/
theorem exists_hairLocalGraph_neighbor_of_mem_y
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    {y : V} (hy : y ∈ H.y i) :
    ∃ z : V, (H.hairLocalGraph i).Adj y z := by
  let a := (H.hairConnector_inHairLocalGraph i).indexOfTarget ⟨y, hy⟩
  have htarget :
      ((H.hairConnector_inHairLocalGraph i).path a).target = y := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.target_indexOfTarget
          (H.hairConnector_inHairLocalGraph i) ⟨y, hy⟩)
    simpa [a] using h
  have htarget_original :
      ((H.hairConnector i).path a).target = y := by
    simpa using htarget
  exact ⟨((H.hairConnector_inHairLocalGraph i).path a).walk.penultimate,
    by simpa [htarget_original] using
      H.hairConnector_inHairLocalGraph_target_adj_penultimate i a⟩

/-- The unique neighbor of a `y_i` endpoint in the hair-local graph is the
penultimate vertex on its hair-connector path. -/
theorem hairLocalGraph_neighbor_eq_penultimate_of_mem_y
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    {y z : V} (hy : y ∈ H.y i)
    (hadj : (H.hairLocalGraph i).Adj y z) :
    z =
      ((H.hairConnector i).path
        ((H.hairConnector_inHairLocalGraph i).indexOfTarget ⟨y, hy⟩)).walk.penultimate := by
  let a := (H.hairConnector_inHairLocalGraph i).indexOfTarget ⟨y, hy⟩
  have htarget :
      ((H.hairConnector_inHairLocalGraph i).path a).target = y := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.target_indexOfTarget
          (H.hairConnector_inHairLocalGraph i) ⟨y, hy⟩)
    simpa [a] using h
  have htarget_original :
      ((H.hairConnector i).path a).target = y := by
    simpa using htarget
  have hy_hair : y ∈ H.hairCluster i := H.y_subset_hairCluster i hy
  have hy_not_cluster : y ∉ H.base.cluster i := by
    intro hy_cluster
    exact Finset.disjoint_left.mp (H.hairCluster_disjoint_base i i)
      hy_hair hy_cluster
  have hadj_spanning :
      ((H.hairConnector i).toPathPacking.spanningGraph).Adj y z := by
    change (clusterWithPackingGraph G (H.base.cluster i) (H.x i) (H.y i)
      (H.hairConnector i).toPathPacking).Adj y z at hadj
    exact (clusterWithPackingGraph_adj_iff_spanningGraph_adj_of_left_not_mem
      (H.hairConnector i).toPathPacking hy_not_cluster).mp hadj
  rcases PathPacking.spanningGraph_adj_iff_exists_path_edge
      (H.hairConnector i).toPathPacking |>.mp hadj_spanning with
    ⟨⟨b, hb_edge_finset⟩, _hyz_ne⟩
  have hb_edge :
      s(y, z) ∈ ((H.hairConnector i).path b).walk.edges := by
    simpa [GraphPath.edgeSet] using hb_edge_finset
  have hy_in_b : y ∈ ((H.hairConnector i).path b).vertexSet := by
    have hy_support :
        y ∈ ((H.hairConnector i).path b).walk.support :=
      ((H.hairConnector i).path b).walk.fst_mem_support_of_mem_edges hb_edge
    simpa [GraphPath.vertexSet] using hy_support
  have hy_in_a : y ∈ ((H.hairConnector i).path a).vertexSet := by
    simpa [htarget_original] using
      GraphPath.target_mem_vertexSet ((H.hairConnector i).path a)
  have hba : b = a := by
    by_contra hne
    exact Finset.disjoint_left.mp
      ((H.hairConnector i).toPathPacking.node_disjoint hne)
      hy_in_b hy_in_a
  subst b
  have hedge_target :
      s(((H.hairConnector i).path a).target, z) ∈
        ((H.hairConnector i).path a).walk.edges := by
    simpa [htarget_original] using hb_edge
  have hz_eq :=
    ((H.hairConnector i).path a).isPath.eq_penultimate_of_mem_edges
      hedge_target
  simpa [a] using hz_eq

/-- Hair endpoints have degree exactly one in the corresponding hair-local
graph. -/
theorem hairLocalGraph_degreeEquals_one_of_mem_y
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    {y : V} (hy : y ∈ H.y i) :
    DegreeEquals (H.hairLocalGraph i) y 1 := by
  let a := (H.hairConnector_inHairLocalGraph i).indexOfTarget ⟨y, hy⟩
  have htarget :
      ((H.hairConnector_inHairLocalGraph i).path a).target = y := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.target_indexOfTarget
          (H.hairConnector_inHairLocalGraph i) ⟨y, hy⟩)
    simpa [a] using h
  have htarget_original :
      ((H.hairConnector i).path a).target = y := by
    simpa using htarget
  refine degreeEquals_one_of_unique_neighbor
    (u := ((H.hairConnector i).path a).walk.penultimate) ?hadj ?huniq
  · simpa [htarget_original] using
      H.hairConnector_inHairLocalGraph_target_adj_original_penultimate i a
  · intro z hz
    simpa [a] using
      H.hairLocalGraph_neighbor_eq_penultimate_of_mem_y i hy hz

/-- The left-right linkage is also present in the hair-local graph. -/
theorem exists_left_right_linkage_inHairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking (H.hairLocalGraph i)
        (H.base.left i) (H.base.right i),
      P.card = w :=
  H.exists_left_right_linkage_inClusterWithPackingGraph i (H.hairConnector i).toPathPacking

/-- The local left-right linkage in the hair-local graph still stays inside
the base cluster. -/
theorem exists_left_right_linkage_inHairLocalGraph_with_staysIn
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ P : PathPacking (H.hairLocalGraph i)
        (H.base.left i) (H.base.right i),
      P.card = w ∧ P.StaysIn (H.base.cluster i) := by
  rcases H.exists_left_right_linkage i with ⟨P, hcard, hstay⟩
  refine ⟨P.inClusterWithPackingGraph hstay
    (H.hairConnector i).toPathPacking, ?_, ?_⟩
  · simpa using hcard
  · exact PathPacking.inClusterWithPackingGraph_staysIn P hstay
      (H.hairConnector i).toPathPacking

/-- A local left-to-`x_i` path that stays in the base cluster can be
concatenated with the corresponding hair-connector path without repeating a
vertex.  The only possible shared vertex is the glued `x_i` endpoint. -/
theorem left_x_hairConnector_concat_isPath
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (P : PerfectPathPacking (H.hairLocalGraph i) (H.base.left i) (H.x i))
    (hPstay : P.toPathPacking.StaysIn (H.base.cluster i)) :
    ∀ a : P.Index,
      ((P.path a).walk.append
        (((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).walk.copy
            (PerfectPathPacking.source_indexOfSourceTarget P
              (H.hairConnector_inHairLocalGraph i) a) rfl)).IsPath := by
  intro a
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path a)
    ((H.hairConnector_inHairLocalGraph i).path
      (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a))
    (PerfectPathPacking.source_indexOfSourceTarget P
      (H.hairConnector_inHairLocalGraph i) a).symm ?_
  intro v hvP hvQ
  have hv_cluster : v ∈ H.base.cluster i := hPstay a hvP
  have hvQ_original :
      v ∈ ((H.hairConnector i).path
        (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).vertexSet := by
    change v ∈ (((H.hairConnector i).inOwnClusterWithPackingGraph
      (H.base.cluster i)).path
        (P.indexOfSourceTarget ((H.hairConnector i).inOwnClusterWithPackingGraph
          (H.base.cluster i)) a)).vertexSet at hvQ
    rw [PerfectPathPacking.inOwnClusterWithPackingGraph_path_vertexSet] at hvQ
    exact hvQ
  have hendpoint :=
    H.hairConnector_internally_disjoint_baseClusters i i
      (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)
      hvQ_original hv_cluster
  rcases hendpoint with hsource | htarget
  · exact hsource.trans
      (PerfectPathPacking.source_indexOfSourceTarget P
        (H.hairConnector_inHairLocalGraph i) a)
  · have hy_mem :
        ((H.hairConnector i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).target ∈
            H.hairCluster i :=
        H.y_subset_hairCluster i
          ((H.hairConnector i).target_mem
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a))
    have hdisj := H.hairCluster_disjoint_base i i
    exact False.elim
      (Finset.disjoint_left.mp hdisj hy_mem (by simpa [htarget] using hv_cluster))

/-- The concatenated local left-to-hair paths are pairwise node-disjoint. -/
theorem left_x_hairConnector_concat_nodeDisjoint
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (P : PerfectPathPacking (H.hairLocalGraph i) (H.base.left i) (H.x i))
    (hPstay : P.toPathPacking.StaysIn (H.base.cluster i))
    (hpath :
      ∀ a : P.Index,
        ((P.path a).walk.append
          (((H.hairConnector_inHairLocalGraph i).path
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget P
                (H.hairConnector_inHairLocalGraph i) a) rfl)).IsPath) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((P.path a).appendWithEq
          ((H.hairConnector_inHairLocalGraph i).path
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a))
          (PerfectPathPacking.source_indexOfSourceTarget P
            (H.hairConnector_inHairLocalGraph i) a).symm
          (hpath a))
        ((P.path b).appendWithEq
          ((H.hairConnector_inHairLocalGraph i).path
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b))
          (PerfectPathPacking.source_indexOfSourceTarget P
            (H.hairConnector_inHairLocalGraph i) b).symm
          (hpath b)) := by
  classical
  have hcross :
      ∀ ⦃a b : P.Index⦄, a ≠ b → ∀ ⦃v : V⦄,
        v ∈ (P.path a).vertexSet →
        v ∈ ((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)).vertexSet →
        False := by
    intro a b hab v hvP hvQ
    have hv_cluster : v ∈ H.base.cluster i := hPstay a hvP
    have hvQ_original :
        v ∈ ((H.hairConnector i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)).vertexSet := by
      simpa using hvQ
    have hendpoint :=
      H.hairConnector_internally_disjoint_baseClusters i i
        (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)
        hvQ_original hv_cluster
    rcases hendpoint with hsource | htarget
    · have hv_eq_target :
          v = (P.path b).target := by
        exact hsource.trans
          ((hairConnector_inHairLocalGraph_path_source H i
              (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)).symm.trans
            (PerfectPathPacking.source_indexOfSourceTarget P
              (H.hairConnector_inHairLocalGraph i) b))
      have hvPb : v ∈ (P.path b).vertexSet := by
        simp [hv_eq_target]
      exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hab) hvP hvPb
    · have hy_mem :
          ((H.hairConnector i).path
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)).target ∈
              H.hairCluster i :=
          H.y_subset_hairCluster i
            ((H.hairConnector i).target_mem
              (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b))
      have hdisj := H.hairCluster_disjoint_base i i
      exact Finset.disjoint_left.mp hdisj hy_mem (by simpa [htarget] using hv_cluster)
  intro a b hab
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvB
  have hvA_union :
      v ∈ (P.path a).vertexSet ∨
        v ∈ ((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (P.path a)
        ((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a))
        (PerfectPathPacking.source_indexOfSourceTarget P
          (H.hairConnector_inHairLocalGraph i) a).symm
        (hpath a) hvA
    simpa [Finset.mem_union] using hsubset
  have hvB_union :
      v ∈ (P.path b).vertexSet ∨
        v ∈ ((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b)).vertexSet := by
    have hsubset :=
      GraphPath.appendWithEq_vertexSet_subset
        (P.path b)
        ((H.hairConnector_inHairLocalGraph i).path
          (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b))
        (PerfectPathPacking.source_indexOfSourceTarget P
          (H.hairConnector_inHairLocalGraph i) b).symm
        (hpath b) hvB
    simpa [Finset.mem_union] using hsubset
  rcases hvA_union with hvPa | hvQa
  · rcases hvB_union with hvPb | hvQb
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hab) hvPa hvPb
    · exact hcross hab hvPa hvQb
  · rcases hvB_union with hvPb | hvQb
    · exact hcross hab.symm hvPb hvQa
    · have hq_ne :
          P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a ≠
            P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b := by
        intro hq
        have htargets : (P.path a).target = (P.path b).target := by
          have hs :=
            congrArg
              (fun q => ((H.hairConnector_inHairLocalGraph i).path q).source)
              hq
          exact (PerfectPathPacking.source_indexOfSourceTarget P
              (H.hairConnector_inHairLocalGraph i) a).symm.trans
            (hs.trans
              (PerfectPathPacking.source_indexOfSourceTarget P
                (H.hairConnector_inHairLocalGraph i) b))
        exact hab (P.target_bijective.1 (Subtype.ext htargets))
      exact Finset.disjoint_left.mp
        ((H.hairConnector_inHairLocalGraph i).toPathPacking.node_disjoint hq_ne)
        hvQa hvQb

/-- Concatenating a local perfect linkage from the left nails to `x_i` with
the hair connector gives a perfect local linkage from the left nails to `y_i`,
provided the concatenated paths are simple and mutually node-disjoint. -/
theorem exists_left_y_perfect_linkage_inHairLocalGraph_of_concat
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (P : PerfectPathPacking (H.hairLocalGraph i) (H.base.left i) (H.x i))
    (hPcard : P.card = w)
    (hpath :
      ∀ a : P.Index,
        ((P.path a).walk.append
          (((H.hairConnector_inHairLocalGraph i).path
            (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a)).walk.copy
              (PerfectPathPacking.source_indexOfSourceTarget P
                (H.hairConnector_inHairLocalGraph i) a) rfl)).IsPath)
    (hnode :
      Pairwise fun a b =>
        GraphPath.NodeDisjoint
          ((P.path a).appendWithEq
            ((H.hairConnector_inHairLocalGraph i).path
              (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) a))
            (PerfectPathPacking.source_indexOfSourceTarget P
              (H.hairConnector_inHairLocalGraph i) a).symm
            (hpath a))
          ((P.path b).appendWithEq
            ((H.hairConnector_inHairLocalGraph i).path
              (P.indexOfSourceTarget (H.hairConnector_inHairLocalGraph i) b))
            (PerfectPathPacking.source_indexOfSourceTarget P
              (H.hairConnector_inHairLocalGraph i) b).symm
            (hpath b))) :
    ∃ R : PerfectPathPacking (H.hairLocalGraph i)
        (H.base.left i) (H.y i),
      R.card = w := by
  refine ⟨P.concat (H.hairConnector_inHairLocalGraph i) hpath hnode, ?_⟩
  simpa using hPcard

/-- A hairy system supplies a perfect full-width local linkage from the left
nails of each base cluster to the endpoints in the corresponding hair cluster. -/
theorem exists_left_y_perfect_linkage_inHairLocalGraph
    (H : HairyPathOfSetsSystem G ell w) (i : Fin ell) :
    ∃ R : PerfectPathPacking (H.hairLocalGraph i)
        (H.base.left i) (H.y i),
      R.card = w := by
  rcases H.exists_left_x_perfect_linkage_inHairLocalGraph_with_staysIn i with
    ⟨P, hPcard, hPstay⟩
  let hpath := H.left_x_hairConnector_concat_isPath i P hPstay
  exact H.exists_left_y_perfect_linkage_inHairLocalGraph_of_concat i P hPcard
    hpath (H.left_x_hairConnector_concat_nodeDisjoint i P hPstay hpath)

end HairyPathOfSetsSystem

end SimpleGraph

end Lax17Proofs
