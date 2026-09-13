import Lax17Proofs.Source.TreewidthSparsifierTheorem51Transcript
import Lax17Proofs.Source.TreewidthSparsifierBlueThinning

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: assembled physical support

This file begins the global assembly in Step 1 of Theorem 5.1.  A realized
transcript stores one local red/blue layer per round.  Under the cluster
budget, those layers lie in pairwise distinct clusters.  Consequently the
union of all blue path supports still has maximum degree two.

The red support additionally contains the path-of-sets connectors and is
assembled below after the indexed-record interface.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- A terminal of a perfect path packing has degree at most one in the
packing support.  The existing path-level lemma is promoted here using
pairwise node-disjointness of the packing. -/
theorem perfectPathPacking_spanningGraph_degreeAtMost_one_of_mem_terminal
    {K : _root_.SimpleGraph V} {S T : Finset V}
    (Q : PerfectPathPacking K S T) {v : V}
    (hv : v ∈ S ∨ v ∈ T) :
    DegreeAtMost Q.toPathPacking.spanningGraph v 1 := by
  classical
  let i : Q.Index :=
    if hvS : v ∈ S then Q.indexOfSource ⟨v, hvS⟩
    else Q.indexOfTarget ⟨v, hv.resolve_left hvS⟩
  have hvi : v ∈ (Q.path i).vertexSet := by
    by_cases hvS : v ∈ S
    · have hs :
          (Q.path (Q.indexOfSource ⟨v, hvS⟩)).source = v :=
        congrArg Subtype.val (Q.source_indexOfSource ⟨v, hvS⟩)
      simpa [i, hvS, hs] using
        GraphPath.source_mem_vertexSet
          (Q.path (Q.indexOfSource ⟨v, hvS⟩))
    · have ht :
          (Q.path
            (Q.indexOfTarget ⟨v, hv.resolve_left hvS⟩)).target = v :=
        congrArg Subtype.val
          (Q.target_indexOfTarget ⟨v, hv.resolve_left hvS⟩)
      simpa [i, hvS, ht] using
        GraphPath.target_mem_vertexSet
          (Q.path (Q.indexOfTarget ⟨v, hv.resolve_left hvS⟩))
  have hvEndpoint : (Q.path i).IsEndpoint v := by
    by_cases hvS : v ∈ S
    · left
      simpa [i, hvS] using
        (congrArg Subtype.val (Q.source_indexOfSource ⟨v, hvS⟩)).symm
    · right
      simpa [i, hvS] using
        (congrArg Subtype.val
          (Q.target_indexOfTarget ⟨v, hv.resolve_left hvS⟩)).symm
  let N :=
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.pathNeighborFinset
      (Q.path i) v
  refine ⟨N, ?_,
    Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.pathNeighborFinset_card_le_one_of_isEndpoint
      (Q.path i) hvEndpoint⟩
  intro w
  constructor
  · intro hw
    have he : s(v, w) ∈ (Q.path i).edgeSet :=
      (Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.mem_pathNeighborFinset
        (Q.path i)).1 hw |>.2
    have hne : v ≠ w := by
      have hadj : K.Adj v w := by
        simpa using GraphPath.edgeSet_subset_edgeSet (Q.path i) he
      exact hadj.ne
    exact
      (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨⟨i, he⟩, hne⟩
  · intro hvw
    rcases
        (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).1 hvw with
      ⟨⟨j, he⟩, _hne⟩
    have hvj : v ∈ (Q.path j).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path j) he).1
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (Q.node_disjoint hne) hvi hvj
    subst j
    exact
      (Lax17Proofs.SimpleGraph.TreewidthSparsifier.GraphPath.mem_pathNeighborFinset
        (Q.path i)).2
      ⟨(GraphPath.endpoints_mem_vertexSet_of_edgeSet (Q.path i) he).2, he⟩

namespace BuildState.ExpanderBlocks

/-- The physical record at a specified position in the realized transcript. -/
def recordAt (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) : RecordedLayer P :=
  E.finalState.records.get j

@[simp] theorem recordAt_mem (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) :
    E.recordAt j ∈ E.finalState.records :=
  List.get_mem _ _

/-- Record ordinals are exactly their positions in the transcript list. -/
@[simp] theorem recordAt_ordinal (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) :
    (E.recordAt j).ordinal = j.1 := by
  have hget := congrArg (fun xs : List ℕ => xs[j.1]?)
    E.finalState.record_ordinals
  simpa [recordAt] using hget

/-- With enough clusters, the record at position `j` is physically realized
in cluster `j`. -/
theorem recordAt_index_eq
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) :
    (E.recordAt j).index.1 = j.1 := by
  rw [← E.recordAt_ordinal j]
  exact record_index_eq_ordinal_of_budget P E hbudget (E.recordAt_mem j)

/-- Consecutive source-relevant records use the labelling transported by the
preceding red routing and connector.  The total-responder `stay` alternative
is impossible here because the two records occupy clusters `j` and `j+1`. -/
theorem recordAt_nextLabel
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) :
    let j₀ : Fin E.finalState.records.length :=
      ⟨j.1, by omega⟩
    let j₁ : Fin E.finalState.records.length :=
      ⟨j.1 + 1, by omega⟩
    ∃ hi : (E.recordAt j₀).index.1 + 1 < ell,
      ∀ x : Fin h,
        ((E.recordAt j₁).label x).1 =
          ((E.recordAt j₀).layer.nextLabel hi x).1 := by
  classical
  dsimp only
  let j₀ : Fin E.finalState.records.length :=
    ⟨j.1, by omega⟩
  let j₁ : Fin E.finalState.records.length :=
    ⟨j.1 + 1, by omega⟩
  have hj :
      j.1 + 1 < E.finalState.records.length := by
    omega
  have hfollow :
      RecordFollows (E.recordAt j₀) (E.recordAt j₁) := by
    simpa [recordAt, j₀, j₁] using
      E.finalState.records_follow.getElem j.1 hj
  rcases hfollow with hadv | hstay
  · exact ⟨hadv.1, hadv.2.2⟩
  · have hindex₀ := E.recordAt_index_eq hbudget j₀
    have hindex₁ := E.recordAt_index_eq hbudget j₁
    have heq := congrArg Fin.val hstay.1
    dsimp [j₀, j₁] at hindex₀ hindex₁ heq
    omega

/-- The union of the physical blue path supports of all recorded layers. -/
noncomputable def blueSupport (E : ExpanderBlocks P count) :
    _root_.SimpleGraph V :=
  ⨆ j : Fin E.finalState.records.length,
    (E.recordAt j).layer.blue.toPathPacking.spanningGraph

/-- The union of the red path supports internal to recorded clusters. -/
noncomputable def localRedSupport (E : ExpanderBlocks P count) :
    _root_.SimpleGraph V :=
  ⨆ j : Fin E.finalState.records.length,
    (E.recordAt j).layer.red.toPathPacking.spanningGraph

theorem blueSupport_le_ambient (E : ExpanderBlocks P count) :
    E.blueSupport ≤ G := by
  classical
  apply iSup_le
  intro j
  exact
    (E.recordAt j).layer.blue.toPathPacking.spanningGraph_le.trans
      ((E.recordAt j).layer.localGraph_le_induced.trans inducedOnFinset_le)

theorem localRedSupport_le_ambient (E : ExpanderBlocks P count) :
    E.localRedSupport ≤ G := by
  classical
  apply iSup_le
  intro j
  exact
    (E.recordAt j).layer.red.toPathPacking.spanningGraph_le.trans
      ((E.recordAt j).layer.localGraph_le_induced.trans inducedOnFinset_le)

private theorem blueSupport_adj_iff (E : ExpanderBlocks P count)
    {v w : V} :
    E.blueSupport.Adj v w ↔
      ∃ j : Fin E.finalState.records.length,
        (E.recordAt j).layer.blue.toPathPacking.spanningGraph.Adj v w := by
  classical
  simp [blueSupport]

private theorem localRedSupport_adj_iff (E : ExpanderBlocks P count)
    {v w : V} :
    E.localRedSupport.Adj v w ↔
      ∃ j : Fin E.finalState.records.length,
        (E.recordAt j).layer.red.toPathPacking.spanningGraph.Adj v w := by
  classical
  simp [localRedSupport]

private theorem blue_adj_left_mem_cluster
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) {v w : V}
    (hvw :
      (E.recordAt j).layer.blue.toPathPacking.spanningGraph.Adj v w) :
    v ∈ P.cluster (E.recordAt j).index := by
  have hlocal : (E.recordAt j).layer.localGraph.Adj v w :=
    (E.recordAt j).layer.blue.toPathPacking.spanningGraph_le hvw
  exact ((E.recordAt j).layer.localGraph_le_induced hlocal).2.1

private theorem red_adj_left_mem_cluster
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) {v w : V}
    (hvw :
      (E.recordAt j).layer.red.toPathPacking.spanningGraph.Adj v w) :
    v ∈ P.cluster (E.recordAt j).index := by
  have hlocal : (E.recordAt j).layer.localGraph.Adj v w :=
    (E.recordAt j).layer.red.toPathPacking.spanningGraph_le hvw
  exact ((E.recordAt j).layer.localGraph_le_induced hlocal).2.1

/-- Blue supports in different realized clusters are vertex-disjoint. -/
private theorem blue_neighbor_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin E.finalState.records.length} {v w z : V}
    (hvw :
      (E.recordAt j).layer.blue.toPathPacking.spanningGraph.Adj v w)
    (hvz :
      (E.recordAt k).layer.blue.toPathPacking.spanningGraph.Adj v z) :
    j = k := by
  have hvj : v ∈ P.cluster (E.recordAt j).index :=
    E.blue_adj_left_mem_cluster j hvw
  have hvk : v ∈ P.cluster (E.recordAt k).index :=
    E.blue_adj_left_mem_cluster k hvz
  have hindex : (E.recordAt j).index = (E.recordAt k).index := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
  apply Fin.ext
  rw [← E.recordAt_index_eq hbudget j,
    ← E.recordAt_index_eq hbudget k]
  exact congrArg Fin.val hindex

/-- The global blue support has maximum degree two.  This is the global form
of the source observation that blue paths from distinct rounds occupy
distinct clusters. -/
theorem blueSupport_maxDegreeAtMost_two
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    MaxDegreeAtMost E.blueSupport 2 := by
  classical
  intro v
  by_cases hex :
      ∃ j : Fin E.finalState.records.length,
        ∃ w : V,
          (E.recordAt j).layer.blue.toPathPacking.spanningGraph.Adj v w
  · let j := Classical.choose hex
    let w := Classical.choose (Classical.choose_spec hex)
    have hvw :
        (E.recordAt j).layer.blue.toPathPacking.spanningGraph.Adj v w :=
      Classical.choose_spec (Classical.choose_spec hex)
    rcases
        perfectPathPacking_spanningGraph_degreeAtMost_two
          (E.recordAt j).layer.blue v with
      ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro z
    constructor
    · intro hz
      exact (E.blueSupport_adj_iff).2 ⟨j, (hN z).1 hz⟩
    · intro hvz
      rcases (E.blueSupport_adj_iff).1 hvz with ⟨k, hvzk⟩
      have hjk : j = k :=
        E.blue_neighbor_unique hbudget hvw hvzk
      subst k
      exact (hN z).2 hvzk
  · refine ⟨∅, ?_, by simp⟩
    intro z
    constructor
    · simp
    · intro hvz
      rcases (E.blueSupport_adj_iff).1 hvz with ⟨j, hvzj⟩
      exact False.elim (hex ⟨j, z, hvzj⟩)

/-- The red supports internal to distinct realized clusters also retain
maximum degree two. -/
theorem localRedSupport_maxDegreeAtMost_two
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    MaxDegreeAtMost E.localRedSupport 2 := by
  classical
  intro v
  by_cases hex :
      ∃ j : Fin E.finalState.records.length,
        ∃ w : V,
          (E.recordAt j).layer.red.toPathPacking.spanningGraph.Adj v w
  · let j := Classical.choose hex
    let w := Classical.choose (Classical.choose_spec hex)
    have hvw :
        (E.recordAt j).layer.red.toPathPacking.spanningGraph.Adj v w :=
      Classical.choose_spec (Classical.choose_spec hex)
    rcases
        perfectPathPacking_spanningGraph_degreeAtMost_two
          (E.recordAt j).layer.red v with
      ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro z
    constructor
    · intro hz
      exact (E.localRedSupport_adj_iff).2 ⟨j, (hN z).1 hz⟩
    · intro hvz
      rcases (E.localRedSupport_adj_iff).1 hvz with ⟨k, hvzk⟩
      have hvj : v ∈ P.cluster (E.recordAt j).index :=
        E.red_adj_left_mem_cluster j hvw
      have hvk : v ∈ P.cluster (E.recordAt k).index :=
        E.red_adj_left_mem_cluster k hvzk
      have hindex : (E.recordAt j).index = (E.recordAt k).index := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
      have hjk : j = k := by
        apply Fin.ext
        rw [← E.recordAt_index_eq hbudget j,
          ← E.recordAt_index_eq hbudget k]
        exact congrArg Fin.val hindex
      subst k
      exact (hN z).2 hvzk
  · refine ⟨∅, ?_, by simp⟩
    intro z
    constructor
    · simp
    · intro hvz
      rcases (E.localRedSupport_adj_iff).1 hvz with ⟨j, hvzj⟩
      exact False.elim (hex ⟨j, z, hvzj⟩)

/-- The number of physical records fits in the available cluster prefix. -/
theorem records_length_le_ell
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    E.finalState.records.length ≤ ell := by
  rw [E.records_length_eq_flattened_length]
  exact E.flattened_length_le.trans hbudget

/-- The cluster on the left of a gap in the realized record prefix. -/
def gapIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) : Fin ell :=
  ⟨j.1, by
    have hrecords := E.records_length_le_ell hbudget
    omega⟩

/-- A realized gap really has a following cluster. -/
theorem gapIndex_succ_lt
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) :
    (E.gapIndex hbudget j).1 + 1 < ell := by
  have hrecords := E.records_length_le_ell hbudget
  dsimp [gapIndex]
  omega

/-- The connector packing between two consecutive recorded layers. -/
noncomputable def connectorAt
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) :=
  P.connector (E.gapIndex hbudget j) (E.gapIndex_succ_lt hbudget j)

/-- The union of all connector supports between consecutive recorded
clusters. -/
noncomputable def connectorSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    _root_.SimpleGraph V :=
  ⨆ j : Fin (E.finalState.records.length - 1),
    (E.connectorAt hbudget j).toPathPacking.spanningGraph

theorem connectorSupport_le_ambient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    E.connectorSupport hbudget ≤ G := by
  classical
  apply iSup_le
  intro j
  exact (E.connectorAt hbudget j).toPathPacking.spanningGraph_le

private theorem connectorSupport_adj_iff
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v w : V} :
    (E.connectorSupport hbudget).Adj v w ↔
      ∃ j : Fin (E.finalState.records.length - 1),
        (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w := by
  classical
  simp [connectorSupport]

private theorem connector_adj_has_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) {v w : V}
    (hvw :
      (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w) :
    ∃ a : (E.connectorAt hbudget j).Index,
      v ∈ ((E.connectorAt hbudget j).path a).vertexSet := by
  rcases
      (PathPacking.spanningGraph_adj_iff_exists_path_edge
        (E.connectorAt hbudget j).toPathPacking).1 hvw with
    ⟨⟨a, he⟩, _hne⟩
  exact ⟨a,
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.connectorAt hbudget j).path a) he).1⟩

private theorem connector_gap_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin (E.finalState.records.length - 1)} {v w z : V}
    (hvw :
      (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w)
    (hvz :
      (E.connectorAt hbudget k).toPathPacking.spanningGraph.Adj v z) :
    j = k := by
  rcases E.connector_adj_has_path hbudget j hvw with ⟨a, hva⟩
  rcases E.connector_adj_has_path hbudget k hvz with ⟨b, hvb⟩
  by_contra hjk
  have hgap :
      E.gapIndex hbudget j ≠ E.gapIndex hbudget k := by
    intro heq
    apply hjk
    apply Fin.ext
    simpa [gapIndex] using congrArg Fin.val heq
  have hdisj :=
    P.connector_mutually_nodeDisjoint
      (E.gapIndex_succ_lt hbudget j)
      (E.gapIndex_succ_lt hbudget k) hgap a b
  exact Finset.disjoint_left.mp hdisj hva hvb

/-- Connector families across distinct gaps are mutually node-disjoint, so
their global union has maximum degree two. -/
theorem connectorSupport_maxDegreeAtMost_two
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    MaxDegreeAtMost (E.connectorSupport hbudget) 2 := by
  classical
  intro v
  by_cases hex :
      ∃ j : Fin (E.finalState.records.length - 1),
        ∃ w : V,
          (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w
  · let j := Classical.choose hex
    let w := Classical.choose (Classical.choose_spec hex)
    have hvw :
        (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w :=
      Classical.choose_spec (Classical.choose_spec hex)
    rcases
        perfectPathPacking_spanningGraph_degreeAtMost_two
          (E.connectorAt hbudget j) v with
      ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro z
    constructor
    · intro hz
      exact (E.connectorSupport_adj_iff hbudget).2
        ⟨j, (hN z).1 hz⟩
    · intro hvz
      rcases (E.connectorSupport_adj_iff hbudget).1 hvz with
        ⟨k, hvzk⟩
      have hjk := E.connector_gap_unique hbudget hvw hvzk
      subst k
      exact (hN z).2 hvzk
  · refine ⟨∅, ?_, by simp⟩
    intro z
    constructor
    · simp
    · intro hvz
      rcases (E.connectorSupport_adj_iff hbudget).1 hvz with
        ⟨j, hvzj⟩
      exact False.elim (hex ⟨j, z, hvzj⟩)

private theorem localRedSupport_degreeAtMost_of_record
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) {v w : V}
    (hvw :
      (E.recordAt j).layer.red.toPathPacking.spanningGraph.Adj v w)
    {d : ℕ}
    (hdegree :
      DegreeAtMost
        (E.recordAt j).layer.red.toPathPacking.spanningGraph v d) :
    DegreeAtMost E.localRedSupport v d := by
  classical
  rcases hdegree with ⟨N, hN, hcard⟩
  refine ⟨N, ?_, hcard⟩
  intro z
  constructor
  · intro hz
    exact E.localRedSupport_adj_iff.mpr ⟨j, (hN z).mp hz⟩
  · intro hvz
    rcases E.localRedSupport_adj_iff.mp hvz with ⟨k, hvzk⟩
    have hvj : v ∈ P.cluster (E.recordAt j).index :=
      E.red_adj_left_mem_cluster j hvw
    have hvk : v ∈ P.cluster (E.recordAt k).index :=
      E.red_adj_left_mem_cluster k hvzk
    have hindex : (E.recordAt j).index = (E.recordAt k).index := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
    have hjk : j = k := by
      apply Fin.ext
      rw [← E.recordAt_index_eq hbudget j,
        ← E.recordAt_index_eq hbudget k]
      exact congrArg Fin.val hindex
    subst k
    exact (hN z).mpr hvzk

private theorem connectorSupport_degreeAtMost_of_gap
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) {v w : V}
    (hvw :
      (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w)
    {d : ℕ}
    (hdegree :
      DegreeAtMost
        (E.connectorAt hbudget j).toPathPacking.spanningGraph v d) :
    DegreeAtMost (E.connectorSupport hbudget) v d := by
  classical
  rcases hdegree with ⟨N, hN, hcard⟩
  refine ⟨N, ?_, hcard⟩
  intro z
  constructor
  · intro hz
    exact (E.connectorSupport_adj_iff hbudget).mpr
      ⟨j, (hN z).mp hz⟩
  · intro hvz
    rcases (E.connectorSupport_adj_iff hbudget).mp hvz with ⟨k, hvzk⟩
    have hjk := E.connector_gap_unique hbudget hvw hvzk
    subst k
    exact (hN z).mpr hvzk

private theorem local_and_connector_degreeAtMost_one
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v w z : V}
    (hlocal : E.localRedSupport.Adj v w)
    (hconnector : (E.connectorSupport hbudget).Adj v z) :
    DegreeAtMost E.localRedSupport v 1 ∧
      DegreeAtMost (E.connectorSupport hbudget) v 1 := by
  classical
  rcases E.localRedSupport_adj_iff.mp hlocal with ⟨j, hvwj⟩
  rcases (E.connectorSupport_adj_iff hbudget).mp hconnector with ⟨k, hvzk⟩
  rcases E.connector_adj_has_path hbudget k hvzk with ⟨a, hva⟩
  have hvcluster : v ∈ P.cluster (E.recordAt j).index :=
    E.red_adj_left_mem_cluster j hvwj
  have hvEndpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget k) (E.gapIndex_succ_lt hbudget k)
      (E.recordAt j).index a hva hvcluster
  have hvLocalTerminal :
      v ∈ P.left (E.recordAt j).index ∨
        v ∈ P.right (E.recordAt j).index := by
    rcases hvEndpoint with hvSource | hvTarget
    · have hvRightGap :
          v ∈ P.right (E.gapIndex hbudget k) := by
        simpa [hvSource] using (E.connectorAt hbudget k).source_mem a
      have hvGapCluster :
          v ∈ P.cluster (E.gapIndex hbudget k) :=
        P.right_subset_cluster (E.gapIndex hbudget k) hvRightGap
      have hindex :
          E.gapIndex hbudget k = (E.recordAt j).index := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
          hvGapCluster hvcluster
      exact Or.inr (by simpa [hindex] using hvRightGap)
    · let next : Fin ell :=
        ⟨(E.gapIndex hbudget k).1 + 1,
          E.gapIndex_succ_lt hbudget k⟩
      have hvLeftNext : v ∈ P.left next := by
        simpa [next, hvTarget] using (E.connectorAt hbudget k).target_mem a
      have hvNextCluster : v ∈ P.cluster next :=
        P.left_subset_cluster next hvLeftNext
      have hindex : next = (E.recordAt j).index := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
          hvNextCluster hvcluster
      exact Or.inl (by simpa [hindex] using hvLeftNext)
  have hvConnectorTerminal :
      v ∈ P.right (E.gapIndex hbudget k) ∨
        v ∈
          P.left
            ⟨(E.gapIndex hbudget k).1 + 1,
              E.gapIndex_succ_lt hbudget k⟩ := by
    rcases hvEndpoint with hvSource | hvTarget
    · exact Or.inl (by
        simpa [hvSource] using (E.connectorAt hbudget k).source_mem a)
    · exact Or.inr (by
        simpa [hvTarget] using (E.connectorAt hbudget k).target_mem a)
  constructor
  · apply E.localRedSupport_degreeAtMost_of_record hbudget j hvwj
    exact
      perfectPathPacking_spanningGraph_degreeAtMost_one_of_mem_terminal
        (E.recordAt j).layer.red hvLocalTerminal
  · apply E.connectorSupport_degreeAtMost_of_gap hbudget k hvzk
    exact
      perfectPathPacking_spanningGraph_degreeAtMost_one_of_mem_terminal
        (E.connectorAt hbudget k) hvConnectorTerminal

/-- The complete red support: cluster-internal red paths together with the
connectors that concatenate them into the global rails. -/
noncomputable def redSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    _root_.SimpleGraph V :=
  E.localRedSupport ⊔ E.connectorSupport hbudget

theorem redSupport_le_ambient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    E.redSupport hbudget ≤ G :=
  sup_le E.localRedSupport_le_ambient (E.connectorSupport_le_ambient hbudget)

/-- The concatenated red rails have maximum degree two. -/
theorem redSupport_maxDegreeAtMost_two
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    MaxDegreeAtMost (E.redSupport hbudget) 2 := by
  classical
  intro v
  by_cases hlocal : ∃ w : V, E.localRedSupport.Adj v w
  · by_cases hconnector :
        ∃ z : V, (E.connectorSupport hbudget).Adj v z
    · rcases hlocal with ⟨w, hvw⟩
      rcases hconnector with ⟨z, hvz⟩
      rcases E.local_and_connector_degreeAtMost_one hbudget hvw hvz with
        ⟨hred, hconn⟩
      simpa [redSupport] using degreeAtMost_sup hred hconn
    · rcases E.localRedSupport_maxDegreeAtMost_two hbudget v with
        ⟨N, hN, hcard⟩
      refine ⟨N, ?_, hcard⟩
      intro u
      constructor
      · exact fun hu => Or.inl ((hN u).mp hu)
      · intro hvu
        rcases hvu with hvu | hvu
        · exact (hN u).mpr hvu
        · exact False.elim (hconnector ⟨u, hvu⟩)
  · rcases E.connectorSupport_maxDegreeAtMost_two hbudget v with
      ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro u
    constructor
    · exact fun hu => Or.inr ((hN u).mp hu)
    · intro hvu
      rcases hvu with hvu | hvu
      · exact False.elim (hlocal ⟨u, hvu⟩)
      · exact (hN u).mpr hvu

/-- The Step-1 physical support before random thinning. -/
noncomputable def assembledSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    _root_.SimpleGraph V :=
  E.redSupport hbudget ⊔ E.blueSupport

theorem assembledSupport_le_ambient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    E.assembledSupport hbudget ≤ G :=
  sup_le (E.redSupport_le_ambient hbudget) E.blueSupport_le_ambient

/-- The assembled support has exactly the red/blue form consumed by the
degree-four thinning operation. -/
noncomputable def blueThinningInput
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    BlueThinningInput (E.assembledSupport hbudget) :=
  BlueThinningInput.ofTwoDegreeTwoSupports
    (E.assembledSupport hbudget) (E.redSupport hbudget) E.blueSupport
    rfl (E.redSupport_maxDegreeAtMost_two hbudget)
    (E.blueSupport_maxDegreeAtMost_two hbudget)

/-- Every thinning outcome is a degree-three subgraph of the original host. -/
theorem thinnedGraph_le_ambient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) :
    (E.blueThinningInput hbudget).thinnedGraph outcome ≤ G :=
  ((E.blueThinningInput hbudget).thinnedGraph_le outcome).trans
    (E.assembledSupport_le_ambient hbudget)

/-- Red and red-blue edges are never removed by the degree-four thinning. -/
theorem redSupport_le_thinnedGraph
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) :
    E.redSupport hbudget ≤
      (E.blueThinningInput hbudget).thinnedGraph outcome := by
  simpa [blueThinningInput, assembledSupport] using
    (BlueThinningInput.ofTwoDegreeTwoSupports_red_le_thinnedGraph
      (E.redSupport hbudget) E.blueSupport
      (E.redSupport_maxDegreeAtMost_two hbudget)
      (E.blueSupport_maxDegreeAtMost_two hbudget) outcome)

theorem thinnedGraph_maxDegreeAtMost_three
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) :
    MaxDegreeAtMost
      ((E.blueThinningInput hbudget).thinnedGraph outcome) 3 :=
  (E.blueThinningInput hbudget).thinnedGraph_maxDegreeAtMost outcome

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
