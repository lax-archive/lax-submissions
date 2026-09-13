import Lax17Proofs.Source.ChekuriChuzhoySection5Phase2Assembly
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Leaves
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Concatenation
import Lax17Proofs.Source.PathPackingSupportDegree

namespace Lax17Proofs

universe u v w

/-!
# Phase 2 pruning and lifting

Chekuri--Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, journal
Section 5.4.2, prunes the Phase 2 host before applying the superterminal
construction.  Directness is therefore required only in that pruned
same-vertex subgraph.  This module builds the Phase 2 skeleton there, lifts
its host paths, and completes the ordinary bandwidth tree-of-sets assembly in
the original graph without changing its clusters or interfaces.
-/

namespace SimpleGraph


namespace ChekuriChuzhoySection5Clustering

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H G : _root_.SimpleGraph V}

/-- A boundary vertex witnessed in a same-vertex subgraph remains a boundary
vertex after edges are added. -/
theorem interfaceVertices_mono_graph
    (hHG : H ≤ G) (C : Finset V) :
    interfaceVertices H C ⊆ interfaceVertices G C := by
  intro v hv
  rcases mem_interfaceVertices.mp hv with ⟨hvC, x, hxC, hvx⟩
  exact mem_interfaceVertices.mpr ⟨hvC, x, hxC, hHG hvx⟩

end ChekuriChuzhoySection5Clustering

namespace ChekuriChuzhoySection5ClusterSkeleton
namespace ClusterPathSkeleton

open ChekuriChuzhoySection5Clustering

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H G : _root_.SimpleGraph V} {m : Nat}
variable {cluster : Fin m → Finset V}

/-- Lift every stored host path in a cluster skeleton to a same-vertex
supergraph.  Named edges, groups, clusters, and all path vertex sets remain
unchanged. -/
def mapLe
    (S : ClusterPathSkeleton H cluster)
    (hHG : H ≤ G) :
    ClusterPathSkeleton G cluster where
  graph := S.graph
  hostPath := fun e => (S.hostPath e).mapLe hHG
  host_source_mem := by
    intro e
    simpa [GraphPath.mapLe] using S.host_source_mem e
  host_target_mem := by
    intro e
    simpa [GraphPath.mapLe] using S.host_target_mem e
  host_source_interface := by
    intro e
    have hmem :=
      interfaceVertices_mono_graph hHG (cluster (S.graph.left e))
        (S.host_source_interface e)
    simpa [GraphPath.mapLe] using hmem
  host_target_interface := by
    intro e
    have hmem :=
      interfaceVertices_mono_graph hHG (cluster (S.graph.right e))
        (S.host_target_interface e)
    simpa [GraphPath.mapLe] using hmem
  groups := S.groups
  internally_disjoint_clusters := by
    intro e r
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      S.internally_disjoint_clusters e r
  one_per_group_node_disjoint := by
    intro selected hselected e he f hf hef
    simpa [GraphPath.NodeDisjoint] using
      S.one_per_group_node_disjoint
        selected hselected he hf hef

@[simp] theorem mapLe_edgeBundleKey
    (S : ClusterPathSkeleton H cluster)
    (hHG : H ≤ G) (p : Sym2 (Fin m)) :
    (S.mapLe hHG).edgeBundleKey p = S.edgeBundleKey p :=
  rfl

end ClusterPathSkeleton
end ChekuriChuzhoySection5ClusterSkeleton

namespace ChekuriChuzhoySection5Phase2Pruning

open ChekuriChuzhoySection5AuxiliaryTree
open ChekuriChuzhoySection5ClusterSkeleton
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5Phase1Concatenation
open ChekuriChuzhoySection5Phase1RootExtraction
open ChekuriChuzhoySection5Superterminals
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A degree-at-most-one vertex of the ambient graph cannot be internal to a
simple path. -/
theorem graphPath_isEndpoint_of_degreeAtMost_one
    {G : _root_.SimpleGraph V} (P : GraphPath G) {x : V}
    (hdegree : DegreeAtMost G x 1) (hx : x ∈ P.vertexSet) :
    P.IsEndpoint x := by
  classical
  by_cases hsource : x = P.source
  · exact Or.inl hsource
  by_cases htarget : x = P.target
  · exact Or.inr htarget
  rcases P.exists_two_edgeSet_incident_of_mem_vertexSet_of_not_endpoint
      hx hsource htarget with
    ⟨e₁, he₁, hxe₁, e₂, he₂, hxe₂, hne⟩
  rcases hdegree with ⟨N, hN, hcard⟩
  rcases Sym2.mem_iff_exists.mp hxe₁ with ⟨y, rfl⟩
  rcases Sym2.mem_iff_exists.mp hxe₂ with ⟨z, he₂eq⟩
  have hxy : G.Adj x y := by
    simpa using GraphPath.edgeSet_subset_edgeSet P he₁
  have hxz : G.Adj x z := by
    simpa [he₂eq] using GraphPath.edgeSet_subset_edgeSet P he₂
  have hyN : y ∈ N := (hN y).2 hxy
  have hzN : z ∈ N := (hN z).2 hxz
  have hyz : y = z := (Finset.card_le_one.mp hcard) y hyN z hzN
  exfalso
  apply hne
  simpa [he₂eq, hyz]

/-- The semantic content of the paper's Phase 2 pruning: if every vertex of
the selected routers has retained degree at most one, then every path between
distinct selected boundary sets is direct with respect to every router. -/
theorem boundaryPathsDirect_of_degreeAtMost_one_on_selectedUnion
    {G : _root_.SimpleGraph V} {m : Nat}
    (cluster B : Fin m → Finset V)
    (hdegree :
      ∀ x ∈
        ChekuriChuzhoySection5Phase1Leaves.selectedUnion cluster,
        DegreeAtMost G x 1) :
    BoundaryPathsDirect G cluster B := by
  intro i j _hij P _hsource _htarget r x hxP hxCluster
  apply graphPath_isEndpoint_of_degreeAtMost_one P
    (hdegree x
      (ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr
        ⟨r, hxCluster⟩))
    hxP

/-! ## The canonical retained leaf incidences -/

/-- All canonical leaf-to-root legs, regarded as one node-disjoint packing.
The source carrier is widened to the union of the selected routers. -/
noncomputable def canonicalLeafLegPacking
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    PathPacking G
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) root where
  Index := Σ i : Fin m, (C.leafLeg E i).Index
  path a := (C.leafLeg E a.1).path a.2
  connects := by
    rintro ⟨i, a⟩
    exact Or.inl
      ⟨ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr
          ⟨i, C.leafEndpoint_subset_leaf E i
            ((C.leafLeg E i).source_mem a)⟩,
        C.targetSet_subset_root i
          (E.endpoint_subset i ((C.leafLeg E i).target_mem a))⟩
  node_disjoint := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      apply (C.leafLeg E i).toPathPacking.node_disjoint
      intro habIndex
      apply hab
      cases habIndex
      rfl
    · exact C.leafLeg_mutuallyNodeDisjoint E hij a b

theorem canonicalLeafLegPacking_internallyDisjoint_selectedUnion
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    (canonicalLeafLegPacking C E).InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
  rintro ⟨i, a⟩
  exact C.leafLeg_internallyDisjointLeaves E i a

/-- The paper's Phase 2 pruning before superterminals are added: retain all
edges with both ends outside the selected routers and the canonical leaf-leg
edges that give each selected boundary vertex its one external incidence. -/
noncomputable def canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    _root_.SimpleGraph V :=
  inducedOnFinset G
      (Finset.univ \
        ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) ⊔
    (canonicalLeafLegPacking C E).spanningGraph

theorem canonicalPhase2PrunedGraph_le
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    canonicalPhase2PrunedGraph C E ≤ G := by
  apply sup_le
  · exact inducedOnFinset_le
  · exact (canonicalLeafLegPacking C E).spanningGraph_le

theorem canonicalPhase2PrunedGraph_degreeAtMost_one_on_selectedUnion
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    ∀ x ∈
      ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter,
      DegreeAtMost (canonicalPhase2PrunedGraph C E) x 1 := by
  intro x hx
  have hleg :
      DegreeAtMost (canonicalLeafLegPacking C E).spanningGraph x 1 := by
    apply
      (canonicalLeafLegPacking C E).degreeAtMost_one_spanningGraph_of_endpoint_only
    rintro ⟨i, a⟩ hxa
    exact C.leafLeg_internallyDisjointLeaves E i a hxa hx
  rcases hleg with ⟨N, hN, hcard⟩
  refine ⟨N, ?_, hcard⟩
  intro y
  simp only [canonicalPhase2PrunedGraph, _root_.SimpleGraph.sup_adj]
  constructor
  · intro hy
    exact Or.inr ((hN y).1 hy)
  · rintro (houtside | hleg)
    · have hxOutside :=
        (inducedOnFinset_adj G _ x y |>.mp houtside).2.1
      exact False.elim ((Finset.mem_sdiff.mp hxOutside).2 hx)
    · exact (hN y).2 hleg

theorem canonicalPhase2PrunedGraph_boundaryPathsDirect
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    BoundaryPathsDirect (canonicalPhase2PrunedGraph C E)
      leafRouter (C.leafEndpoint E) := by
  exact boundaryPathsDirect_of_degreeAtMost_one_on_selectedUnion
    leafRouter (C.leafEndpoint E)
    (canonicalPhase2PrunedGraph_degreeAtMost_one_on_selectedUnion C E)

theorem leafLeg_edge_mem_canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    (i : Fin m) (a : (C.leafLeg E i).Index) {e : Sym2 V}
    (he : e ∈ ((C.leafLeg E i).path a).edgeSet) :
    e ∈ (canonicalPhase2PrunedGraph C E).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [_root_.SimpleGraph.mem_edgeSet]
      apply Or.inr
      apply
        (canonicalLeafLegPacking C E).spanningGraph_adj_iff_exists_path_edge.mpr
      refine ⟨⟨⟨i, a⟩, he⟩, ?_⟩
      have hxy : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet
          ((C.leafLeg E i).path a) he
      exact hxy.ne

theorem rootLinkage_edge_mem_canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j)
    (a : (C.rootLinkage E hij).Index) {e : Sym2 V}
    (he : e ∈ ((C.rootLinkage E hij).path a).edgeSet) :
    e ∈ (canonicalPhase2PrunedGraph C E).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [_root_.SimpleGraph.mem_edgeSet]
      apply Or.inl
      rw [inducedOnFinset_adj]
      have hxy : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet
          ((C.rootLinkage E hij).path a) he
      have hends :=
        GraphPath.endpoints_mem_vertexSet_of_edgeSet
          ((C.rootLinkage E hij).path a) he
      have hxRoot := C.rootLinkage_staysIn_root E hij a hends.1
      have hyRoot := C.rootLinkage_staysIn_root E hij a hends.2
      exact
        ⟨hxy,
          Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ x,
              fun hxLeaves =>
                Finset.disjoint_left.mp C.root_disjoint_selectedLeaves
                  hxRoot hxLeaves⟩,
          Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ y,
              fun hyLeaves =>
                Finset.disjoint_left.mp C.root_disjoint_selectedLeaves
                  hyRoot hyLeaves⟩⟩

theorem rootToLeafLeg_edge_mem_canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j)
    (a : (C.rootToLeafLeg E hij).Index) {e : Sym2 V}
    (he : e ∈ ((C.rootToLeafLeg E hij).path a).edgeSet) :
    e ∈ (canonicalPhase2PrunedGraph C E).edgeSet := by
  rcases Finset.mem_union.mp (C.rootToLeafLeg_path_edgeSet_subset E hij a he)
      with heRoot | heLeg
  · exact rootLinkage_edge_mem_canonicalPhase2PrunedGraph
      C E hij a heRoot
  · apply leafLeg_edge_mem_canonicalPhase2PrunedGraph C E j
      ((C.rootLinkage E hij).indexOfSourceTarget
        (C.leafLeg E j).reverse a)
    simpa using heLeg

theorem pairPacking_edge_mem_canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j)
    (a : (C.pairPacking E hij).Index) {e : Sym2 V}
    (he : e ∈ ((C.pairPacking E hij).path a).edgeSet) :
    e ∈ (canonicalPhase2PrunedGraph C E).edgeSet := by
  rcases Finset.mem_union.mp (C.pairPacking_path_edgeSet_subset E hij a he)
      with heLeg | heRest
  · exact leafLeg_edge_mem_canonicalPhase2PrunedGraph C E i a heLeg
  · exact rootToLeafLeg_edge_mem_canonicalPhase2PrunedGraph C E hij
      ((C.leafLeg E i).indexOfSourceTarget
        (C.rootToLeafLeg E hij) a) heRest

/-- Transfer the Phase 1 all-pairs packing to the canonical Phase 2 pruned
host.  Endpoints and cardinality are unchanged. -/
noncomputable def pairPackingInCanonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    PerfectPathPacking (canonicalPhase2PrunedGraph C E)
      (C.leafEndpoint E i) (C.leafEndpoint E j) :=
  (C.pairPacking E hij).transfer (canonicalPhase2PrunedGraph C E) (by
    intro a e he
    apply pairPacking_edge_mem_canonicalPhase2PrunedGraph C E hij a
    exact List.mem_toFinset.mpr
      (by simpa [GraphPath.edgeSet] using he))

@[simp] theorem pairPackingInCanonicalPhase2PrunedGraph_card
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (pairPackingInCanonicalPhase2PrunedGraph C E hij).card = width := by
  change (C.pairPacking E hij).card = width
  exact C.pairPacking_card E hij

/-- Every retained leaf endpoint remains a genuine interface vertex in the
canonical pruned host: its first leaf-leg edge is retained, while the other
endpoint of that edge lies outside all selected routers. -/
theorem leafEndpoint_subset_interface_canonicalPhase2PrunedGraph
    {G : _root_.SimpleGraph V} {m q width : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    C.leafEndpoint E i ⊆
      interfaceVertices (canonicalPhase2PrunedGraph C E) (leafRouter i) := by
  classical
  intro v hv
  let L := C.leafLeg E i
  rcases L.source_bijective.2 ⟨v, hv⟩ with ⟨a, ha⟩
  have hsource : (L.path a).source = v :=
    congrArg Subtype.val ha
  have htargetRoot : (L.path a).target ∈ root :=
    C.targetSet_subset_root i
      (E.endpoint_subset i (L.target_mem a))
  have hsourceLeaf : (L.path a).source ∈ leafRouter i := by
    rw [hsource]
    exact C.leafEndpoint_subset_leaf E i hv
  have hne : (L.path a).source ≠ (L.path a).target := by
    intro h
    exact Finset.disjoint_left.mp C.root_disjoint_selectedLeaves
      htargetRoot
      (ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr
        ⟨i, by simpa [h] using hsourceLeaf⟩)
  let x := (L.path a).reverse.penultimate
  have hreverseNontrivial :
      (L.path a).reverse.source ≠ (L.path a).reverse.target := by
    simpa using hne.symm
  have hxAdjSource : G.Adj x (L.path a).source := by
    simpa [x] using
      (L.path a).reverse.penultimate_adj_target hreverseNontrivial
  have hxVertex : x ∈ (L.path a).vertexSet := by
    have := (L.path a).reverse.penultimate_mem_vertexSet hreverseNontrivial
    simpa [x] using this
  have hxOutside : x ∉ leafRouter i := by
    intro hxLeaf
    have hxSelected :
        x ∈ ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter :=
      ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mpr ⟨i, hxLeaf⟩
    rcases C.leafLeg_internallyDisjointLeaves E i a hxVertex hxSelected
      with hxSource | hxTarget
    · exact hxAdjSource.ne hxSource
    · exact Finset.disjoint_left.mp C.root_disjoint_selectedLeaves
        (by simpa [hxTarget] using htargetRoot) hxSelected
  have heReverse :
      s((L.path a).reverse.penultimate, (L.path a).reverse.target) ∈
        (L.path a).reverse.edgeSet := by
    exact List.mem_toFinset.mpr
      ((L.path a).reverse.walk.mk_penultimate_end_mem_edges
        ((L.path a).reverse.walk_not_nil_of_source_ne_target
          hreverseNontrivial))
  have he : s((L.path a).source, x) ∈ (L.path a).edgeSet := by
    simpa [x, Sym2.eq_swap] using heReverse
  have hePruned :
      s((L.path a).source, x) ∈
        (canonicalPhase2PrunedGraph C E).edgeSet :=
    leafLeg_edge_mem_canonicalPhase2PrunedGraph C E i a he
  apply mem_interfaceVertices.mpr
  refine ⟨C.leafEndpoint_subset_leaf E i hv, x, hxOutside, ?_⟩
  simpa [hsource, _root_.SimpleGraph.mem_edgeSet] using hePruned

private theorem graph_edgeBundle_eq_skeleton_edgeBundleKey
    {G : _root_.SimpleGraph V} {m : Nat}
    {cluster : Fin m → Finset V}
    (S : ClusterPathSkeleton G cluster) (p : Sym2 (Fin m)) :
    S.graph.edgeBundle p = S.edgeBundleKey p := by
  classical
  ext e
  simp [FiniteEdgeIndexedGraph.edgeKey, ClusterPathSkeleton.edgeKey]

/-- Phase 2 may be assembled in a pruned same-vertex host and then lifted to
the original graph.  In particular, the all-boundary-path directness
hypothesis is imposed on `H`, not on the original graph `G`, where adding
edges can create irrelevant non-direct paths.  The supplied cluster finsets
are retained exactly in the output.  Connectivity and bandwidth are required
only in `G`: pruning need not preserve the internal cluster edges. -/
theorem
    exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings_in_pruned_subgraph_with_same_clusters
    (G H : _root_.SimpleGraph V)
    (hHG : H ≤ G)
    {m mu w cap alphaNum alphaDen : Nat}
    (cluster B : Fin m → Finset V)
    (hm : 2 ≤ m) (hmu : 1 ≤ mu) (hw : 0 < w)
    (hwidth : m ^ 4 * w ≤ 2 * mu)
    (hBcard : ∀ i : Fin m, (B i).card = mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆ interfaceVertices H (cluster i))
    (hdirect : BoundaryPathsDirect H cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j →
        ∃ P : PathPacking H (B i) (B j), P.card = mu)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    ∃ T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen,
      ∀ i : Fin m, T.cluster i = cluster i := by
  obtain ⟨S, hSconnected, hSgroups, hSdegree⟩ :=
    exists_regularClusterPathSkeleton_of_pairwise_direct_packings
      H cluster B mu hm hmu hBcard hinterface hdirect hpacking
  let S' : ClusterPathSkeleton G cluster := S.mapLe hHG
  obtain ⟨T, _hTheavySupport, hTtree, hTdegree, hTheavy⟩ :=
    claim517_exists_boundedDegreeAuxiliarySpanningTree
      S.graph hm (by omega : 0 < 2 * mu) hSdegree hSconnected
  have hbundle :
      ∀ p ∈ T.edgeSet, m * w ≤ (S'.edgeBundleKey p).card := by
    intro p hp
    induction p using Sym2.inductionOn with
    | _ i j =>
        have hij : T.Adj i j := by
          simpa [_root_.SimpleGraph.mem_edgeSet] using hp
        have hheavy :
            heavyThreshold m (2 * mu) ≤
              S.graph.bundleCapacity s(i, j) :=
          hTheavy i j hij
        have hcard :
            m * w ≤ (S.graph.edgeBundle s(i, j)).card :=
          mul_width_le_bundleCard_of_heavy
            S.graph s(i, j) (by omega) hwidth hheavy
        simpa [S', graph_edgeBundle_eq_skeleton_edgeBundleKey
          S s(i, j)] using hcard
  exact
    S'.exists_bandwidthTreeOfSetsSystem_with_same_clusters T
      (by omega) hw hTtree hTdegree (by simpa [S'] using hSgroups) hbundle
      hclusterConnected hclusterDisjoint hband hcap

/-- The complete qualitative Phase 1-to-Phase 2 bridge.  A root-clean leaf
packing family and root extraction provide the canonical pruned host, exact
all-pairs direct boundary packings in that host, and hence the ordinary
bandwidth tree-of-sets system in the original graph. -/
theorem exists_bandwidthTreeOfSetsSystem_of_rootCleanLeafPackingFamily
    {G : _root_.SimpleGraph V} {m q width w cap alphaNum alphaDen : Nat}
    {leafRouter : Fin m → Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    (hm : 2 ≤ m) (hwidthPos : 1 ≤ width) (hw : 0 < w)
    (hPhase2Width : m ^ 4 * w ≤ 2 * width)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (leafRouter i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (leafRouter i) (leafRouter j))
    (hband :
      ∀ i : Fin m,
        TruncatedScaledBandwidth
          G (leafRouter i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    ∃ T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen,
      ∀ i : Fin m, T.cluster i = leafRouter i := by
  apply
    exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings_in_pruned_subgraph_with_same_clusters
      G (canonicalPhase2PrunedGraph C E)
      (canonicalPhase2PrunedGraph_le C E)
      leafRouter (C.leafEndpoint E) hm hwidthPos hw hPhase2Width
      (C.leafEndpoint_card E)
      (leafEndpoint_subset_interface_canonicalPhase2PrunedGraph C E)
      (canonicalPhase2PrunedGraph_boundaryPathsDirect C E)
      ?_ hclusterConnected hclusterDisjoint hband hcap
  intro i j hij
  refine ⟨(pairPackingInCanonicalPhase2PrunedGraph C E hij).toPathPacking, ?_⟩
  exact pairPackingInCanonicalPhase2PrunedGraph_card C E hij

end ChekuriChuzhoySection5Phase2Pruning
end SimpleGraph

end Lax17Proofs
