import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthBridge
import Lax17Proofs.Source.ChekuriChuzhoySection5ClusterSkeleton
import Lax17Proofs.Source.ChekuriChuzhoySection5DisjointBundleSelection
import Lax17Proofs.Source.TreeOfSetsBandwidth

namespace Lax17Proofs

universe u v w

/-!
# Section 5 skeleton-to-tree assembly

This file performs the final deterministic assembly in Chekuri--Chuzhoy
Section 5.4.2.  A degree-three auxiliary spanning tree selects a disjoint
family of large parallel-edge bundles from the terminal skeleton.  The
source-sharp Hall transversal retains the requested width in every bundle,
and the corresponding host paths form the connectors of a
`BandwidthTreeOfSetsSystem`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5ClusterSkeleton


open Finset
open ChekuriChuzhoySection5ClusterSkeleton
open ChekuriChuzhoySection5DisjointBundleSelection
open ChekuriChuzhoySection5Selection

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m w : Nat}
variable {cluster : Fin m → Finset V}

namespace ClusterPathSkeleton

/-- The finite type of skeleton groups. -/
abbrev GroupIndex (S : ClusterPathSkeleton G cluster) :=
  {U : Finset S.graph.Edge // U ∈ S.groups.parts}

/-- The unique group containing an edge copy. -/
noncomputable def groupOf
    (S : ClusterPathSkeleton G cluster) (e : S.graph.Edge) :
    S.GroupIndex := by
  classical
  exact ⟨S.groups.part e, S.groups.part_mem.mpr (by simp)⟩

theorem groupOf_eq_iff_mem
    (S : ClusterPathSkeleton G cluster)
    (e : S.graph.Edge) (U : S.GroupIndex) :
    S.groupOf e = U ↔ e ∈ U.1 := by
  classical
  constructor
  · intro h
    rw [← h]
    exact S.groups.mem_part (by simp)
  · intro he
    apply Subtype.ext
    exact S.groups.part_eq_of_mem U.2 he

theorem filter_groupOf_eq
    (S : ClusterPathSkeleton G cluster) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U) = U.1 := by
  classical
  ext e
  simp [S.groupOf_eq_iff_mem e U]

theorem image_groupOf_univ
    (S : ClusterPathSkeleton G cluster) :
    (Finset.univ.image S.groupOf) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro U
  rcases S.groups.nonempty_of_mem_parts U.2 with ⟨e, he⟩
  exact Finset.mem_image.mpr
    ⟨e, Finset.mem_univ e, (S.groupOf_eq_iff_mem e U).2 he⟩

theorem groupFiber_card_le
    (S : ClusterPathSkeleton G cluster) {k : Nat}
    (hsize : S.GroupSizeAtMost k) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U).card ≤ k := by
  rw [S.filter_groupOf_eq U]
  exact hsize U.1 U.2

theorem isGroupTransversal_of_exact
    (S : ClusterPathSkeleton G cluster)
    {selected : Finset S.graph.Edge}
    (hselected :
      IsExactGroupTransversal Finset.univ S.groupOf selected) :
    S.IsGroupTransversal selected := by
  classical
  intro U hU
  let g : S.GroupIndex := ⟨U, hU⟩
  have hg : g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf := by
    rw [S.image_groupOf_univ]
    simp
  rcases hselected.existsUnique_mem_group hg with ⟨e, he, hunique⟩
  have heU : e ∈ U := (S.groupOf_eq_iff_mem e g).1 he.2
  have hsubset : selected ∩ U ⊆ {e} := by
    intro f hf
    have hfSelected := (Finset.mem_inter.mp hf).1
    have hfU := (Finset.mem_inter.mp hf).2
    have hfg : S.groupOf f = g := (S.groupOf_eq_iff_mem f g).2 hfU
    have hfe : f = e := hunique f ⟨hfSelected, hfg⟩
    simpa [hfe]
  have heInter : e ∈ selected ∩ U :=
    Finset.mem_inter.mpr ⟨he.1, heU⟩
  exact Finset.card_eq_one.mpr
    ⟨e, Finset.Subset.antisymm hsubset (by
      intro f hf
      have hfe : f = e := Finset.mem_singleton.mp hf
      simpa [hfe] using heInter)⟩

/-- Skeleton bundles belonging to the edges of the auxiliary tree. -/
noncomputable def treeBundles
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m)) :
    Finset (Finset S.graph.Edge) := by
  classical
  exact T.edgeFinset.image S.edgeBundleKey

theorem treeBundles_pairwiseDisjoint
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m)) :
    (↑(S.treeBundles T) : Set (Finset S.graph.Edge)).PairwiseDisjoint id := by
  classical
  intro B hB C hC hBC
  rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hC with ⟨q, hq, rfl⟩
  apply S.edgeBundleKey_disjoint_of_ne
  intro hpq
  apply hBC
  simpa [hpq]

/-- A selected exact-width subbundle for every unoriented auxiliary-tree
edge. -/
structure TreeBundleSelection
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m)) (w : Nat) where
  selected : Finset S.graph.Edge
  groupTransversal : S.IsGroupTransversal selected
  chosen :
    (p : Sym2 (Fin m)) → p ∈ T.edgeSet → Finset S.graph.Edge
  chosen_subset :
    ∀ p hp, chosen p hp ⊆ selected ∩ S.edgeBundleKey p
  chosen_card :
    ∀ p hp, (chosen p hp).card = w

/-- Source-sharp simultaneous selection along all edges of an auxiliary
tree.  Pairwise-disjoint endpoint-pair bundles remove the extra factor in the
number of tree edges. -/
theorem exists_treeBundleSelection
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m))
    (hm : 0 < m)
    (hgroups : S.GroupSizeAtMost m)
    (hbundle :
      ∀ p ∈ T.edgeSet, m * w ≤ (S.edgeBundleKey p).card) :
    Nonempty (TreeBundleSelection S T w) := by
  classical
  have hbundles :
      ∀ B ∈ S.treeBundles T, B ⊆ (Finset.univ : Finset S.graph.Edge) := by
    intro B hB
    exact Finset.subset_univ _
  have hgroupSize :
      ∀ g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf,
        (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = g).card ≤ m := by
    intro g _hg
    exact S.groupFiber_card_le hgroups g
  have hbundleSize :
      ∀ B ∈ S.treeBundles T, m * w ≤ B.card := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
    apply hbundle p
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hp
  rcases
      exists_exactGroupTransversal_retaining_pairwiseDisjoint_bundles
        (Finset.univ : Finset S.graph.Edge) S.groupOf
        (S.treeBundles T) m w hm hbundles
        (S.treeBundles_pairwiseDisjoint T) hgroupSize hbundleSize with
    ⟨selected, hselected, hretained⟩
  have htransversal : S.IsGroupTransversal selected :=
    S.isGroupTransversal_of_exact hselected
  have hlarge :
      ∀ p, p ∈ T.edgeSet →
        w ≤ (selected ∩ S.edgeBundleKey p).card := by
    intro p hp
    apply hretained (S.edgeBundleKey p)
    apply Finset.mem_image.mpr
    refine ⟨p, ?_, rfl⟩
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hp
  let chosen :
      (p : Sym2 (Fin m)) → p ∈ T.edgeSet → Finset S.graph.Edge :=
    fun p hp => Classical.choose (Finset.exists_subset_card_eq (hlarge p hp))
  have hchosenSpec :
      ∀ p hp,
        chosen p hp ⊆ selected ∩ S.edgeBundleKey p ∧
          (chosen p hp).card = w := by
    intro p hp
    exact Classical.choose_spec (Finset.exists_subset_card_eq (hlarge p hp))
  exact ⟨{
    selected := selected
    groupTransversal := htransversal
    chosen := chosen
    chosen_subset := fun p hp => (hchosenSpec p hp).1
    chosen_card := fun p hp => (hchosenSpec p hp).2 }⟩

namespace TreeBundleSelection

variable {S : ClusterPathSkeleton G cluster}
variable {T : _root_.SimpleGraph (Fin m)}

/-- The selected named edge copies on one oriented auxiliary-tree edge.  The
underlying selection depends only on the corresponding unoriented edge. -/
noncomputable def chosenForAdj
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    Finset S.graph.Edge :=
  A.chosen s(i, j) (by simpa using hij)

theorem chosenForAdj_subset
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    A.chosenForAdj i j hij ⊆ A.selected ∩ S.edgeBundle i j := by
  simpa [chosenForAdj, S.edgeBundle_eq_edgeBundleKey] using
    A.chosen_subset s(i, j) (by simpa using hij)

theorem mem_selected_of_mem_chosenForAdj
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) {e : S.graph.Edge}
    (he : e ∈ A.chosenForAdj i j hij) :
    e ∈ A.selected :=
  (Finset.mem_inter.mp (A.chosenForAdj_subset i j hij he)).1

theorem mem_edgeBundle_of_mem_chosenForAdj
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) {e : S.graph.Edge}
    (he : e ∈ A.chosenForAdj i j hij) :
    e ∈ S.edgeBundle i j :=
  (Finset.mem_inter.mp (A.chosenForAdj_subset i j hij he)).2

@[simp] theorem chosenForAdj_card
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    (A.chosenForAdj i j hij).card = w := by
  simpa [chosenForAdj] using
    A.chosen_card s(i, j) (by simpa using hij)

/-- The selected host paths on an oriented auxiliary-tree edge, before
promoting their actually used endpoints to a perfect packing. -/
noncomputable def bundlePathPacking
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    PathPacking G
      (ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i))
      (ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster j)) where
  Index := {e : S.graph.Edge // e ∈ A.chosenForAdj i j hij}
  path := fun e => S.hostPath e.1
  connects := by
    intro e
    exact S.hostPath_endpoints_interface_of_mem_edgeBundle
      (A.mem_edgeBundle_of_mem_chosenForAdj i j hij e.2)
  node_disjoint := by
    intro e f hef
    exact S.one_per_group_node_disjoint A.selected A.groupTransversal
      (A.mem_selected_of_mem_chosenForAdj i j hij e.2)
      (A.mem_selected_of_mem_chosenForAdj i j hij f.2)
      (fun h => hef (Subtype.ext h))

@[simp] theorem bundlePathPacking_card
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    (A.bundlePathPacking i j hij).card = w := by
  classical
  simp [bundlePathPacking, PathPacking.card]

theorem bundlePathPacking_internallyDisjointFromSet
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) (r : Fin m) :
    (A.bundlePathPacking i j hij).InternallyDisjointFromSet (cluster r) := by
  intro e
  exact S.internally_disjoint_clusters e.1 r

/-- Selected path families belonging to distinct auxiliary-tree edges are
mutually node-disjoint. -/
theorem bundlePathPacking_mutuallyNodeDisjoint
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j)
    (p q : Fin m) (hpq : T.Adj p q)
    (hedge : s(i, j) ≠ s(p, q)) :
    (A.bundlePathPacking i j hij).MutuallyNodeDisjoint
      (A.bundlePathPacking p q hpq) := by
  intro e f
  apply S.one_per_group_node_disjoint A.selected A.groupTransversal
  · exact A.mem_selected_of_mem_chosenForAdj i j hij e.2
  · exact A.mem_selected_of_mem_chosenForAdj p q hpq f.2
  · intro hef
    apply hedge
    have hei : S.edgeKey e.1 = s(i, j) := by
      apply S.mem_edgeBundleKey.mp
      rw [← S.edgeBundle_eq_edgeBundleKey i j]
      exact A.mem_edgeBundle_of_mem_chosenForAdj i j hij e.2
    have hef' : S.edgeKey f.1 = s(p, q) := by
      apply S.mem_edgeBundleKey.mp
      rw [← S.edgeBundle_eq_edgeBundleKey p q]
      exact A.mem_edgeBundle_of_mem_chosenForAdj p q hpq f.2
    exact hei.symm.trans (by simpa [hef] using hef')

/-- The endpoint set at `i` induced by the selected paths on the edge
`{i,j}`.  The path family is stored only in the increasing orientation. -/
noncomputable def selectedInterface
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    Finset V := by
  classical
  by_cases h : i < j
  · exact (A.bundlePathPacking i j hij).sourceSet
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    exact
      (A.bundlePathPacking j i (T.symm hij)).targetSet

theorem selectedInterface_subset_interfaceVertices
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    A.selectedInterface i j hij ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) := by
  classical
  by_cases h : i < j
  · simpa [selectedInterface, h] using
      (A.bundlePathPacking i j hij).sourceSet_subset_left
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [selectedInterface, h, hji] using
      (A.bundlePathPacking j i (T.symm hij)).targetSet_subset_right

theorem selectedInterface_subset_cluster
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    A.selectedInterface i j hij ⊆ cluster i :=
  (A.selectedInterface_subset_interfaceVertices i j hij).trans
    (ChekuriChuzhoySection5Clustering.interfaceVertices_subset G (cluster i))

@[simp] theorem selectedInterface_card
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    (A.selectedInterface i j hij).card = w := by
  classical
  by_cases h : i < j
  · simp [selectedInterface, h]
  · simp [selectedInterface, h]

private theorem exists_selected_hostPath_of_mem_selectedInterface
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) {v : V}
    (hv : v ∈ A.selectedInterface i j hij) :
    ∃ e : S.graph.Edge,
      e ∈ A.selected ∧ S.edgeKey e = s(i, j) ∧
        v ∈ (S.hostPath e).vertexSet := by
  classical
  by_cases h : i < j
  · have hv' :
        v ∈ (A.bundlePathPacking i j hij).sourceSet := by
      simpa [selectedInterface, h] using hv
    rcases
      (A.bundlePathPacking i j hij)
          |>.exists_orient_source_eq_of_mem_sourceSet hv' with
      ⟨e, he⟩
    refine
      ⟨e.1, A.mem_selected_of_mem_chosenForAdj i j hij e.2, ?_, ?_⟩
    · apply S.mem_edgeBundleKey.mp
      rw [← S.edgeBundle_eq_edgeBundleKey i j]
      exact A.mem_edgeBundle_of_mem_chosenForAdj i j hij e.2
    · have hsource :=
        GraphPath.source_mem_vertexSet
          ((A.bundlePathPacking i j hij).orient.path e)
      rw [he] at hsource
      simpa [bundlePathPacking] using hsource
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    have hv' :
        v ∈ (A.bundlePathPacking j i (T.symm hij)).targetSet := by
      simpa [selectedInterface, h, hji] using hv
    rcases
      (A.bundlePathPacking j i (T.symm hij))
          |>.exists_orient_target_eq_of_mem_targetSet hv' with
      ⟨e, he⟩
    refine
      ⟨e.1,
        A.mem_selected_of_mem_chosenForAdj j i (T.symm hij) e.2, ?_, ?_⟩
    · have hekey : S.edgeKey e.1 = s(j, i) := by
        apply S.mem_edgeBundleKey.mp
        rw [← S.edgeBundle_eq_edgeBundleKey j i]
        exact A.mem_edgeBundle_of_mem_chosenForAdj j i (T.symm hij) e.2
      simpa [Sym2.eq_swap] using hekey
    · have htarget :=
        GraphPath.target_mem_vertexSet
          ((A.bundlePathPacking j i (T.symm hij)).orient.path e)
      rw [he] at htarget
      simpa [bundlePathPacking] using htarget

theorem selectedInterface_disjoint
    (A : TreeBundleSelection S T w)
    {i j k : Fin m} (hij : T.Adj i j) (hik : T.Adj i k)
    (hjk : j ≠ k) :
    Disjoint (A.selectedInterface i j hij)
      (A.selectedInterface i k hik) := by
  rw [Finset.disjoint_left]
  intro v hvj hvk
  rcases A.exists_selected_hostPath_of_mem_selectedInterface
      i j hij hvj with
    ⟨e, heSelected, heKey, hve⟩
  rcases A.exists_selected_hostPath_of_mem_selectedInterface
      i k hik hvk with
    ⟨f, hfSelected, hfKey, hvf⟩
  have hef : e ≠ f := by
    intro hef
    apply hjk
    apply Sym2.congr_right.mp
    exact heKey.symm.trans (by simpa [hef] using hfKey)
  exact Finset.disjoint_left.mp
    (S.one_per_group_node_disjoint A.selected A.groupTransversal
      heSelected hfSelected hef) hve hvf

/-- The selected perfect connector.  Both orientations use the same
increasing-orientation packing, with the decreasing one obtained by
reversal. -/
noncomputable def selectedConnector
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    PerfectPathPacking G
      (A.selectedInterface i j hij)
      (A.selectedInterface j i (T.symm hij)) := by
  classical
  by_cases h : i < j
  · let P := (A.bundlePathPacking i j hij).toPerfectUsedTerminals
    exact P.copyTerminals
      (by simp [selectedInterface, h])
      (by simp [selectedInterface, not_lt_of_ge h.le])
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    let P :=
      (A.bundlePathPacking j i (T.symm hij)).toPerfectUsedTerminals.reverse
    exact P.copyTerminals
      (by simp [selectedInterface, h])
      (by simp [selectedInterface, hji])

@[simp] theorem selectedConnector_card
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) :
    (A.selectedConnector i j hij).card = w :=
  (A.selectedConnector i j hij).card_eq_left_card.trans
    (A.selectedInterface_card i j hij)

theorem selectedConnector_internallyDisjointFromSet
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) (r : Fin m) :
    (A.selectedConnector i j hij).toPathPacking
      |>.InternallyDisjointFromSet (cluster r) := by
  classical
  by_cases h : i < j
  · have hP :=
      (A.bundlePathPacking i j hij).toPerfectUsedTerminals_internallyDisjointFromSet
        (A.bundlePathPacking_internallyDisjointFromSet i j hij r)
    simpa [selectedConnector, h] using hP
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    have hP :=
      (A.bundlePathPacking j i (T.symm hij))
        |>.toPerfectUsedTerminals_internallyDisjointFromSet
          (A.bundlePathPacking_internallyDisjointFromSet
            j i (T.symm hij) r)
    have hPrev :=
      PerfectPathPacking.reverse_internallyDisjointFromSet _ hP
    simpa [selectedConnector, h, hji] using hPrev

omit [Fintype V] in
private theorem toPerfectUsedTerminals_vertexSet_eq
    {S₀ T₀ : Finset V} (P : PathPacking G S₀ T₀) :
    P.toPerfectUsedTerminals.toPathPacking.vertexSet = P.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      simpa [PathPacking.toPerfectUsedTerminals] using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      simpa [PathPacking.toPerfectUsedTerminals] using ha⟩

omit [Fintype V] in
private theorem reverse_vertexSet_eq
    {S₀ T₀ : Finset V} (P : PerfectPathPacking G S₀ T₀) :
    P.reverse.toPathPacking.vertexSet = P.toPathPacking.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

theorem selectedConnector_vertexSet_eq_of_lt
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) (hij_lt : i < j) :
    (A.selectedConnector i j hij).toPathPacking.vertexSet =
      (A.bundlePathPacking i j hij).vertexSet := by
  let P := (A.bundlePathPacking i j hij).toPerfectUsedTerminals
  calc
    (A.selectedConnector i j hij).toPathPacking.vertexSet =
        P.toPathPacking.vertexSet := by
      simp [P, selectedConnector, hij_lt]
    _ = (A.bundlePathPacking i j hij).vertexSet :=
      toPerfectUsedTerminals_vertexSet_eq _

theorem selectedConnector_vertexSet_eq_of_not_lt
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j) (hij_lt : ¬ i < j) :
    (A.selectedConnector i j hij).toPathPacking.vertexSet =
      (A.bundlePathPacking j i (T.symm hij)).vertexSet := by
  have hji : j < i :=
    lt_of_le_of_ne (le_of_not_gt hij_lt) hij.ne.symm
  let P :=
    (A.bundlePathPacking j i (T.symm hij)).toPerfectUsedTerminals
  calc
    (A.selectedConnector i j hij).toPathPacking.vertexSet =
        P.reverse.toPathPacking.vertexSet := by
      simp [P, selectedConnector, hij_lt]
    _ = P.toPathPacking.vertexSet :=
      reverse_vertexSet_eq P
    _ = (A.bundlePathPacking j i (T.symm hij)).vertexSet :=
      toPerfectUsedTerminals_vertexSet_eq _

theorem selectedConnector_mutuallyNodeDisjoint
    (A : TreeBundleSelection S T w)
    (i j : Fin m) (hij : T.Adj i j)
    (p q : Fin m) (hpq : T.Adj p q)
    (hedge : s(i, j) ≠ s(p, q)) :
    (A.selectedConnector i j hij).toPathPacking.MutuallyNodeDisjoint
      (A.selectedConnector p q hpq).toPathPacking := by
  classical
  intro a b
  by_cases hij_lt : i < j
  · by_cases hpq_lt : p < q
    · have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (A.bundlePathPacking_mutuallyNodeDisjoint
          i j hij p q hpq hedge)
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector i j hij).toPathPacking a)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_lt i j hij hij_lt]))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector p q hpq).toPathPacking b)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_lt p q hpq hpq_lt]))
    · have hedge' : s(i, j) ≠ s(q, p) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (A.bundlePathPacking_mutuallyNodeDisjoint
          i j hij q p (T.symm hpq) hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector i j hij).toPathPacking a)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_lt i j hij hij_lt]))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector p q hpq).toPathPacking b)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_not_lt
              p q hpq hpq_lt]))
  ·
    by_cases hpq_lt : p < q
    · have hedge' : s(j, i) ≠ s(p, q) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (A.bundlePathPacking_mutuallyNodeDisjoint
          j i (T.symm hij) p q hpq hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector i j hij).toPathPacking a)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_not_lt
              i j hij hij_lt]))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector p q hpq).toPathPacking b)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_lt p q hpq hpq_lt]))
    · have hedge' : s(j, i) ≠ s(q, p) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (A.bundlePathPacking_mutuallyNodeDisjoint
          j i (T.symm hij) q p (T.symm hpq) hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector i j hij).toPathPacking a)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_not_lt
              i j hij hij_lt]))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (A.selectedConnector p q hpq).toPathPacking b)
          (by
            rw [A.selectedConnector_vertexSet_eq_of_not_lt
              p q hpq hpq_lt]))

/-- The union of all selected interfaces incident with one auxiliary-tree
vertex. -/
noncomputable def boundaryReserve
    (A : TreeBundleSelection S T w)
    (hdegree : MaxDegreeAtMost T 3) (i : Fin m) :
    Finset V :=
  (MaxDegreeAtMost.neighborFinset hdegree i).attach.biUnion fun j =>
    A.selectedInterface i j.1
      ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2)

theorem selectedInterface_subset_boundaryReserve
    (A : TreeBundleSelection S T w)
    (hdegree : MaxDegreeAtMost T 3)
    (i j : Fin m) (hij : T.Adj i j) :
    A.selectedInterface i j hij ⊆ A.boundaryReserve hdegree i := by
  classical
  intro v hv
  apply Finset.mem_biUnion.mpr
  let hjmem :
      j ∈ MaxDegreeAtMost.neighborFinset hdegree i :=
    (MaxDegreeAtMost.mem_neighborFinset hdegree i j).2 hij
  let j' :
      {x : Fin m // x ∈ MaxDegreeAtMost.neighborFinset hdegree i} :=
    ⟨j, hjmem⟩
  refine ⟨j', by simp [j'], ?_⟩
  simpa [boundaryReserve, j'] using hv

theorem boundaryReserve_subset_interfaceVertices
    (A : TreeBundleSelection S T w)
    (hdegree : MaxDegreeAtMost T 3) (i : Fin m) :
    A.boundaryReserve hdegree i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) := by
  classical
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨j, _hj, hvj⟩
  exact A.selectedInterface_subset_interfaceVertices i j.1
    ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2) hvj

theorem boundaryReserve_subset_cluster
    (A : TreeBundleSelection S T w)
    (hdegree : MaxDegreeAtMost T 3) (i : Fin m) :
    A.boundaryReserve hdegree i ⊆ cluster i :=
  (A.boundaryReserve_subset_interfaceVertices hdegree i).trans
    (ChekuriChuzhoySection5Clustering.interfaceVertices_subset G (cluster i))

theorem boundaryReserve_card_le
    (A : TreeBundleSelection S T w)
    (hdegree : MaxDegreeAtMost T 3) (i : Fin m) :
    (A.boundaryReserve hdegree i).card ≤ 3 * w := by
  classical
  calc
    (A.boundaryReserve hdegree i).card ≤
        (MaxDegreeAtMost.neighborFinset hdegree i).attach.card * w := by
      apply Finset.card_biUnion_le_card_mul
      intro j _hj
      exact (A.selectedInterface_card i j.1
        ((MaxDegreeAtMost.mem_neighborFinset hdegree i j.1).1 j.2)).le
    _ = (MaxDegreeAtMost.neighborFinset hdegree i).card * w := by
      simp
    _ ≤ 3 * w :=
      Nat.mul_le_mul_right w
        (MaxDegreeAtMost.card_neighborFinset_le hdegree i)

end TreeBundleSelection

/-- The selected cluster skeleton and a degree-three auxiliary tree produce
the bandwidth tree-of-sets system used by the Section 5 strongification
stage.  The truncation cap only needs to cover the at most three selected
width-`w` interfaces incident with each cluster. -/
theorem exists_bandwidthTreeOfSetsSystem_with_same_clusters
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m))
    {cap alphaNum alphaDen : Nat}
    (hm : 0 < m) (hw : 0 < w)
    (hTree : T.IsTree)
    (hdegree : MaxDegreeAtMost T 3)
    (hgroups : S.GroupSizeAtMost m)
    (hbundle :
      ∀ p ∈ T.edgeSet, m * w ≤ (S.edgeBundleKey p).card)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    ∃ B : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen,
      ∀ i : Fin m, B.cluster i = cluster i := by
  classical
  rcases S.exists_treeBundleSelection T hm hgroups hbundle with ⟨A⟩
  refine ⟨{
    toTreeOfSetsSystem := {
      clusterCount_pos := hm
      width_pos := hw
      metaTree := T
      meta_isTree := hTree
      meta_maxDegree_three := hdegree
      cluster := cluster
      cluster_connected := hclusterConnected
      cluster_disjoint := hclusterDisjoint
      interface := A.selectedInterface
      interface_subset_cluster := A.selectedInterface_subset_cluster
      interface_card := A.selectedInterface_card
      interface_disjoint := A.selectedInterface_disjoint
      connector := A.selectedConnector
      connector_card := A.selectedConnector_card
      connector_internally_disjoint_clusters := by
        intro i j hij r a
        exact A.selectedConnector_internallyDisjointFromSet i j hij r a
      connector_mutually_nodeDisjoint :=
        A.selectedConnector_mutuallyNodeDisjoint }
    boundaryReserve := A.boundaryReserve hdegree
    boundaryReserve_subset_cluster :=
      A.boundaryReserve_subset_cluster hdegree
    interface_subset_boundaryReserve :=
      A.selectedInterface_subset_boundaryReserve hdegree
    boundaryReserve_scaledEdgeWellLinked := by
      intro i
      exact
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth.scaledEdgeWellLinkedIn_of_subset_interface
          (hband i)
          (A.boundaryReserve_subset_interfaceVertices hdegree i)
          ((A.boundaryReserve_card_le hdegree i).trans hcap) }, ?_⟩
  exact fun _ => rfl

/-- Compatibility wrapper for the deterministic tree assembly. -/
theorem exists_bandwidthTreeOfSetsSystem
    (S : ClusterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin m))
    {cap alphaNum alphaDen : Nat}
    (hm : 0 < m) (hw : 0 < w)
    (hTree : T.IsTree)
    (hdegree : MaxDegreeAtMost T 3)
    (hgroups : S.GroupSizeAtMost m)
    (hbundle :
      ∀ p ∈ T.edgeSet, m * w ≤ (S.edgeBundleKey p).card)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    Nonempty (BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) := by
  obtain ⟨B, _hclusters⟩ :=
    S.exists_bandwidthTreeOfSetsSystem_with_same_clusters T
      hm hw hTree hdegree hgroups hbundle
      hclusterConnected hclusterDisjoint hband hcap
  exact ⟨B⟩

end ClusterPathSkeleton
end ChekuriChuzhoySection5ClusterSkeleton
end SimpleGraph

end Lax17Proofs
