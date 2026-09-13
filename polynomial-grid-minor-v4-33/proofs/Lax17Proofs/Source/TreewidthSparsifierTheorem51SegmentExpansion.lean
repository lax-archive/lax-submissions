import Lax17Proofs.Source.TreewidthSparsifierPathBoundary

namespace Lax17Proofs

universe u v w

/-!
# Expanding the surviving segment graph

This module is the physical expansion step after Claim 5.3 in
Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*, Theorem 5.1.  It first
records the two finite sets which can contribute degree greater than two on
one unsuppressed red segment: branch vertices of the realized local layers
and the endpoints at which local red paths are joined to connectors.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- Branch vertices of one realized local layer which lie on a fixed physical
red segment. -/
noncomputable def segmentBranchVerticesAt
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (j : Fin E.finalState.records.length) : Finset V :=
  (E.exactRailSegmentPathAt hbudget hrecords B hB i).vertexSet ∩
    branchVertexFinset (E.recordAt j).layer.localGraph

theorem segmentBranchVerticesAt_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (j : Fin E.finalState.records.length) :
    (E.segmentBranchVerticesAt hbudget hrecords B hB i j).card ≤
      2 * B := by
  classical
  let s := E.exactRailSegmentList hbudget hrecords B hB i
  have hs :=
    E.exactRailSegmentList_mem hbudget hrecords B hB i
  let T := s.toFinset.filter fun v =>
    E.exactRailColour v = Sum.inl j
  have hsub :
      E.segmentBranchVerticesAt hbudget hrecords B hB i j ⊆ T := by
    intro v hv
    have hvList : v ∈ s := by
      have hvPath := (Finset.mem_inter.mp hv).1
      simpa [s, E.exactRailSegmentPathAt_vertexSet] using hvPath
    exact Finset.mem_filter.mpr
      ⟨by simpa [T] using hvList,
        E.exactRailColour_eq_record_of_branch hbudget j
          (Finset.mem_inter.mp hv).2⟩
  have hfilter :
      T.card ≤
        HeavySegments.colourCount
          E.exactRailColour (Sum.inl j) s := by
    have haux :
        ∀ xs : List V,
          (xs.toFinset.filter fun v =>
              E.exactRailColour v = Sum.inl j).card ≤
            HeavySegments.colourCount
              E.exactRailColour (Sum.inl j) xs := by
      intro xs
      induction xs with
      | nil =>
          simp [HeavySegments.colourCount]
      | cons v xs ih =>
          by_cases hv : E.exactRailColour v = Sum.inl j
          · calc
              (((v :: xs).toFinset.filter fun w =>
                    E.exactRailColour w = Sum.inl j).card) ≤
                  (xs.toFinset.filter fun w =>
                    E.exactRailColour w = Sum.inl j).card + 1 := by
                rw [List.toFinset_cons, Finset.filter_insert, if_pos hv]
                exact
                  Finset.card_insert_le v
                    (xs.toFinset.filter fun w =>
                      E.exactRailColour w = Sum.inl j)
              _ ≤ HeavySegments.colourCount
                    E.exactRailColour (Sum.inl j) xs + 1 :=
                Nat.add_le_add_right ih 1
              _ = HeavySegments.colourCount
                    E.exactRailColour (Sum.inl j) (v :: xs) := by
                simp [HeavySegments.colourCount, hv, Nat.add_comm]
          · rw [List.toFinset_cons, Finset.filter_insert, if_neg hv]
            simpa [HeavySegments.colourCount, hv] using ih
    simpa [T] using haux s
  exact (Finset.card_le_card hsub).trans (hfilter.trans
    (E.exactRailSegment_branch_count_le
      hbudget hrecords i.1 B hB s hs j))

/-- All realized local-layer branch vertices on a fixed segment. -/
noncomputable def segmentRecordedBranchVertices
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) : Finset V :=
  Finset.univ.biUnion
    (E.segmentBranchVerticesAt hbudget hrecords B hB i)

theorem segmentRecordedBranchVertices_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.segmentRecordedBranchVertices
        hbudget hrecords B hB i).card ≤
      E.finalState.records.length * (2 * B) := by
  classical
  calc
    (E.segmentRecordedBranchVertices
        hbudget hrecords B hB i).card ≤
        ∑ j : Fin E.finalState.records.length,
          (E.segmentBranchVerticesAt
            hbudget hrecords B hB i j).card := by
      simpa [segmentRecordedBranchVertices] using
        Finset.card_biUnion_le
          (s := (Finset.univ : Finset
            (Fin E.finalState.records.length)))
          (t := E.segmentBranchVerticesAt
            hbudget hrecords B hB i)
    _ ≤ ∑ _j : Fin E.finalState.records.length, 2 * B := by
      exact Finset.sum_le_sum fun j _ =>
        E.segmentBranchVerticesAt_card_le
          hbudget hrecords B hB i j
    _ = E.finalState.records.length * (2 * B) := by simp

/-- The two endpoints of every local red piece on one rail.  These are the
only possible degree-three exceptions created by adjoining the red
connectors to the local red/blue layer. -/
noncomputable def railGlueVertices
    (E : ExpanderBlocks P count)
    (x : Fin h) : Finset V :=
  Finset.univ.biUnion fun j : Fin E.finalState.records.length =>
    {(E.localRedPath j x).source, (E.localRedPath j x).target}

theorem railGlueVertices_card_le
    (E : ExpanderBlocks P count)
    (x : Fin h) :
    (E.railGlueVertices x).card ≤
      2 * E.finalState.records.length := by
  classical
  calc
    (E.railGlueVertices x).card ≤
        ∑ _j : Fin E.finalState.records.length, 2 := by
      calc
        (E.railGlueVertices x).card ≤
            ∑ j : Fin E.finalState.records.length,
              ({(E.localRedPath j x).source,
                (E.localRedPath j x).target} : Finset V).card := by
          simpa [railGlueVertices] using
            Finset.card_biUnion_le
              (s := (Finset.univ : Finset
                (Fin E.finalState.records.length)))
              (t := fun j =>
                ({(E.localRedPath j x).source,
                  (E.localRedPath j x).target} : Finset V))
        _ ≤ ∑ _j : Fin E.finalState.records.length, 2 := by
          exact Finset.sum_le_sum fun _ _ => Finset.card_le_two
    _ = 2 * E.finalState.records.length := by
      simp [Nat.mul_comm]

/-- A local-red support incidence exposes the actual labelled local red path
containing its left endpoint. -/
theorem localRedSupport_adj_has_localRedPath
    (E : ExpanderBlocks P count)
    {v w : V} (hvw : E.localRedSupport.Adj v w) :
    ∃ j : Fin E.finalState.records.length, ∃ x : Fin h,
      v ∈ (E.localRedPath j x).vertexSet := by
  classical
  simp only [localRedSupport, _root_.SimpleGraph.iSup_adj] at hvw
  rcases hvw with ⟨j, hvw⟩
  rcases
      ((E.recordAt j).layer.red.toPathPacking
        |>.spanningGraph_adj_iff_exists_path_edge).mp hvw with
    ⟨⟨a, he⟩, _hne⟩
  let source :
      {z : V // z ∈ P.left (E.recordAt j).index} :=
    ⟨((E.recordAt j).layer.red.path a).source,
      (E.recordAt j).layer.red.source_mem a⟩
  let x : Fin h := (E.recordAt j).label.symm source
  have hindex :
      (E.recordAt j).layer.red.indexOfSource
          ((E.recordAt j).label x) = a := by
    rw [show (E.recordAt j).label x = source by
      exact (E.recordAt j).label.apply_symm_apply source]
    exact (E.recordAt j).layer.red.indexOfSource_source a
  refine ⟨j, x, ?_⟩
  rw [localRedPath, hindex]
  exact
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.recordAt j).layer.red.path a) he).1

/-- A connector-support incidence exposes the actual labelled connector path
containing its left endpoint. -/
theorem connectorSupport_adj_has_connectorPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    {v w : V} (hvw : (E.connectorSupport hbudget).Adj v w) :
    ∃ j : Fin (E.finalState.records.length - 1), ∃ x : Fin h,
      v ∈ (E.connectorPath hbudget j x).vertexSet := by
  classical
  simp only [connectorSupport, _root_.SimpleGraph.iSup_adj] at hvw
  rcases hvw with ⟨j, hvw⟩
  rcases
      ((E.connectorAt hbudget j).toPathPacking
        |>.spanningGraph_adj_iff_exists_path_edge).mp hvw with
    ⟨⟨a, he⟩, _hne⟩
  have hsourceRecord :
      ((E.connectorAt hbudget j).path a).source ∈
        P.right (E.recordAt (E.gapRecord j)).index := by
    rw [E.gapRecord_index_eq_gapIndex hbudget j]
    exact (E.connectorAt hbudget j).source_mem a
  let source :
      {z : V //
        z ∈ P.right (E.recordAt (E.gapRecord j)).index} :=
    ⟨((E.connectorAt hbudget j).path a).source, hsourceRecord⟩
  let x : Fin h :=
    (E.recordAt (E.gapRecord j)).layer.rightLabel.symm source
  have hsourceEq :
      E.connectorSource hbudget j x =
        ⟨((E.connectorAt hbudget j).path a).source,
          (E.connectorAt hbudget j).source_mem a⟩ := by
    apply Subtype.ext
    change
      (((E.recordAt (E.gapRecord j)).layer.rightLabel
        ((E.recordAt (E.gapRecord j)).layer.rightLabel.symm source)).1) =
        source.1
    exact congrArg Subtype.val
      ((E.recordAt (E.gapRecord j)).layer.rightLabel.apply_symm_apply
        source)
  have hindex :
      (E.connectorAt hbudget j).indexOfSource
          (E.connectorSource hbudget j x) = a := by
    rw [hsourceEq]
    exact (E.connectorAt hbudget j).indexOfSource_source a
  refine ⟨j, x, ?_⟩
  rw [connectorPath, hindex]
  exact
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.connectorAt hbudget j).path a) he).1

theorem mem_railGlueVertices_of_localRedPath_endpoint
    (E : ExpanderBlocks P count)
    (x : Fin h)
    (j : Fin E.finalState.records.length) {v : V}
    (hv :
      v = (E.localRedPath j x).source ∨
        v = (E.localRedPath j x).target) :
    v ∈ E.railGlueVertices x := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  rcases hv with rfl | rfl <;> simp

/-- Away from the recorded glue vertices, a point of a local red path is not
incident with any connector-support edge. -/
theorem not_connectorSupport_adj_of_localRed_not_glue
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) (x : Fin h) {v : V}
    (hvLocal : v ∈ (E.localRedPath j x).vertexSet)
    (hvGlue : v ∉ E.railGlueVertices x) :
    ¬ ∃ w : V, (E.connectorSupport hbudget).Adj v w := by
  rintro ⟨w, hvw⟩
  obtain ⟨k, y, hvConnector⟩ :=
    E.connectorSupport_adj_has_connectorPath hbudget hvw
  have hxy :
      x = y :=
    E.localRedPath_connectorPath_label_unique
      hbudget j k hvLocal hvConnector
  subst y
  rcases E.localRedPath_connectorPath_intersection
      hbudget j k x hvLocal hvConnector with
    ⟨_hjk, hvTarget, _hvSource⟩ |
      ⟨_hjk, hvSource, _hvTarget⟩
  · exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.gapRecord k) (Or.inr hvTarget))
  · exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.nextRecord k) (Or.inl hvSource))

/-- A realized vertex cannot belong to two distinct recorded clusters. -/
theorem record_eq_of_mem_clusters
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    {j k : Fin E.finalState.records.length} {v : V}
    (hvj : v ∈ P.cluster (E.recordAt j).index)
    (hvk : v ∈ P.cluster (E.recordAt k).index) :
    j = k := by
  have hindex : (E.recordAt j).index = (E.recordAt k).index := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
  apply Fin.ext
  rw [← E.recordAt_index_eq hbudget j,
    ← E.recordAt_index_eq hbudget k]
  exact congrArg Fin.val hindex

/-- Away from glue vertices, a connector path cannot meet any local-red
support edge. -/
theorem not_localRedSupport_adj_of_connector_not_glue
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (k : Fin (E.finalState.records.length - 1)) (x : Fin h) {v : V}
    (hvConnector : v ∈ (E.connectorPath hbudget k x).vertexSet)
    (hvGlue : v ∉ E.railGlueVertices x) :
    ¬ ∃ w : V, E.localRedSupport.Adj v w := by
  rintro ⟨w, hvw⟩
  obtain ⟨j, y, hvLocal⟩ :=
    E.localRedSupport_adj_has_localRedPath hvw
  have hyx :
      y = x :=
    E.localRedPath_connectorPath_label_unique
      hbudget j k hvLocal hvConnector
  subst y
  rcases E.localRedPath_connectorPath_intersection
      hbudget j k x hvLocal hvConnector with
    ⟨_hjk, hvTarget, _hvSource⟩ |
      ⟨_hjk, hvSource, _hvTarget⟩
  · exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.gapRecord k) (Or.inr hvTarget))
  · exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.nextRecord k) (Or.inl hvSource))

/-- Away from glue vertices, a connector path cannot meet any local-blue
support edge.  This is exactly the internal-disjointness axiom of a strong
path-of-sets system. -/
theorem not_blueSupport_adj_of_connector_not_glue
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (k : Fin (E.finalState.records.length - 1)) (x : Fin h) {v : V}
    (hvConnector : v ∈ (E.connectorPath hbudget k x).vertexSet)
    (hvGlue : v ∉ E.railGlueVertices x) :
    ¬ ∃ w : V, E.blueSupport.Adj v w := by
  rintro ⟨w, hvw⟩
  obtain ⟨z, hvBlue, _hwBlue⟩ :=
    E.blueSupport_adj_has_localBlueIndex hvw
  have hvCluster :=
    E.localBluePath_vertex_mem_cluster hbudget z.1 z.2 hvBlue
  have hendpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget k) (E.gapIndex_succ_lt hbudget k)
      (E.recordAt z.1).index
      ((E.connectorAt hbudget k).indexOfSource
        (E.connectorSource hbudget k x))
      hvConnector hvCluster
  rcases hendpoint with hvSource | hvTarget
  · have hvLocalTarget :
        v = (E.localRedPath (E.gapRecord k) x).target := by
      calc
        v = (E.connectorPath hbudget k x).source := hvSource
        _ = (E.localRedPath (E.gapRecord k) x).target := by
          rw [E.connectorPath_source, E.localRedPath_target]
    exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.gapRecord k) (Or.inr hvLocalTarget))
  · have hvLocalSource :
        v = (E.localRedPath (E.nextRecord k) x).source := by
      calc
        v = (E.connectorPath hbudget k x).target := hvTarget
        _ = (E.localRedPath (E.nextRecord k) x).source := by
          rw [E.connectorPath_target, E.localRedPath_source]
    exact hvGlue
      (E.mem_railGlueVertices_of_localRedPath_endpoint
        x (E.nextRecord k) (Or.inl hvLocalSource))

/-- A nonbranch, nonglue vertex on a local red piece has assembled degree at
most two. -/
theorem assembledSupport_degreeAtMost_two_of_localRed
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length) (x : Fin h) {v : V}
    (hvLocal : v ∈ (E.localRedPath j x).vertexSet)
    (hvBranch :
      v ∉ branchVertexFinset (E.recordAt j).layer.localGraph)
    (hvGlue : v ∉ E.railGlueVertices x) :
    DegreeAtMost (E.assembledSupport hbudget) v 2 := by
  classical
  have hdegreeLocal :
      DegreeAtMost (E.recordAt j).layer.localGraph v 2 := by
    simpa [branchVertexFinset] using hvBranch
  have hvCluster :=
    E.localRedPath_vertex_mem_cluster j x hvLocal
  have hnoConnector :=
    E.not_connectorSupport_adj_of_localRed_not_glue
      hbudget j x hvLocal hvGlue
  have hadj_iff :
      ∀ w : V,
        (E.assembledSupport hbudget).Adj v w ↔
          (E.recordAt j).layer.localGraph.Adj v w := by
    intro w
    constructor
    · intro hvw
      rcases hvw with (hred | hblue)
      · rcases hred with hlocal | hconnector
        · simp only [localRedSupport, _root_.SimpleGraph.iSup_adj] at hlocal
          rcases hlocal with ⟨k, hvwk⟩
          have hvk :
              v ∈ P.cluster (E.recordAt k).index := by
            have hlocalGraph :
                (E.recordAt k).layer.localGraph.Adj v w :=
              (E.recordAt k).layer.red.toPathPacking.spanningGraph_le hvwk
            exact
              ((E.recordAt k).layer.localGraph_le_induced hlocalGraph).2.1
          have hjk :=
            E.record_eq_of_mem_clusters hbudget hvCluster hvk
          subst k
          rw [(E.recordAt j).layer.support_eq]
          exact Or.inl hvwk
        · exact False.elim (hnoConnector ⟨w, hconnector⟩)
      · simp only [blueSupport, _root_.SimpleGraph.iSup_adj] at hblue
        rcases hblue with ⟨k, hvwk⟩
        have hvk :
            v ∈ P.cluster (E.recordAt k).index := by
          have hlocalGraph :
              (E.recordAt k).layer.localGraph.Adj v w :=
            (E.recordAt k).layer.blue.toPathPacking.spanningGraph_le hvwk
          exact ((E.recordAt k).layer.localGraph_le_induced hlocalGraph).2.1
        have hjk :=
          E.record_eq_of_mem_clusters hbudget hvCluster hvk
        subst k
        rw [(E.recordAt j).layer.support_eq]
        exact Or.inr hvwk
    · intro hvw
      exact E.recordAt_localGraph_le_assembledSupport hbudget j hvw
  rcases hdegreeLocal with ⟨N, hN, hcard⟩
  exact ⟨N, fun w => (hN w).trans (hadj_iff w).symm, hcard⟩

/-- A nonglue vertex in a connector interior has assembled degree at most
two. -/
theorem assembledSupport_degreeAtMost_two_of_connector
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (k : Fin (E.finalState.records.length - 1)) (x : Fin h) {v : V}
    (hvConnector : v ∈ (E.connectorPath hbudget k x).vertexSet)
    (hvGlue : v ∉ E.railGlueVertices x) :
    DegreeAtMost (E.assembledSupport hbudget) v 2 := by
  classical
  have hnoLocal :=
    E.not_localRedSupport_adj_of_connector_not_glue
      hbudget k x hvConnector hvGlue
  have hnoBlue :=
    E.not_blueSupport_adj_of_connector_not_glue
      hbudget k x hvConnector hvGlue
  have hdegreeConnector :=
    E.connectorSupport_maxDegreeAtMost_two hbudget v
  rcases hdegreeConnector with ⟨N, hN, hcard⟩
  refine ⟨N, ?_, hcard⟩
  intro w
  constructor
  · intro hw
    exact Or.inl (Or.inr ((hN w).mp hw))
  · intro hvw
    rcases hvw with (hred | hblue)
    · rcases hred with hlocal | hconnector
      · exact False.elim (hnoLocal ⟨w, hlocal⟩)
      · exact (hN w).mpr hconnector
    · exact False.elim (hnoBlue ⟨w, hblue⟩)

/-- A physical red segment, regarded as a path in the assembled support. -/
noncomputable def exactRailSegmentPathInAssembled
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    GraphPath (E.assembledSupport hbudget) :=
  (E.exactRailSegmentPathAt hbudget hrecords B hB i).mapLe le_sup_left

@[simp] theorem exactRailSegmentPathInAssembled_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.exactRailSegmentPathInAssembled
      hbudget hrecords B hB i).vertexSet =
        (E.exactRailSegmentPathAt
          hbudget hrecords B hB i).vertexSet := by
  simp [exactRailSegmentPathInAssembled]

/-- The unsuppressed degree-greater-than-two vertices on one segment are
exactly accounted for by its recorded branch events and glue exceptions. -/
theorem segmentAmbientBranchVertices_subset
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    GraphPath.ambientBranchVertices
        (E.exactRailSegmentPathInAssembled
          hbudget hrecords B hB i) ⊆
      E.segmentRecordedBranchVertices hbudget hrecords B hB i ∪
        E.railGlueVertices i.1 := by
  classical
  intro v hv
  have hvData := Finset.mem_filter.mp hv
  have hvSegment :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet := by
    simpa using hvData.1
  by_cases hvGlue : v ∈ E.railGlueVertices i.1
  · exact Finset.mem_union.mpr (Or.inr hvGlue)
  by_cases hvRecorded :
      v ∈ E.segmentRecordedBranchVertices
        hbudget hrecords B hB i
  · exact Finset.mem_union.mpr (Or.inl hvRecorded)
  have hvRail :
      v ∈ (E.exactRailPath hbudget hrecords i.1).vertexSet :=
    E.exactRailSegmentPathAt_vertexSet_subset_rail
      hbudget hrecords B hB i hvSegment
  have hvCarrier :
      E.RedCarrier hbudget v i.1 :=
    E.exactRailPath_vertex_has_carrier
      hbudget hrecords hvRail
  have hdegree : DegreeAtMost (E.assembledSupport hbudget) v 2 := by
    rcases hvCarrier with ⟨j, hvLocal⟩ | ⟨k, hvConnector⟩
    · have hvNotBranch :
          v ∉ branchVertexFinset (E.recordAt j).layer.localGraph := by
        intro hvBranch
        apply hvRecorded
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        exact Finset.mem_inter.mpr ⟨hvSegment, hvBranch⟩
      exact E.assembledSupport_degreeAtMost_two_of_localRed
        hbudget j i.1 hvLocal hvNotBranch hvGlue
    · exact E.assembledSupport_degreeAtMost_two_of_connector
        hbudget k i.1 hvConnector hvGlue
  exact False.elim (hvData.2 hdegree)

theorem segmentAmbientBranchVertices_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (GraphPath.ambientBranchVertices
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i)).card ≤
      E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length := by
  classical
  calc
    (GraphPath.ambientBranchVertices
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i)).card ≤
        (E.segmentRecordedBranchVertices
            hbudget hrecords B hB i ∪
          E.railGlueVertices i.1).card :=
      Finset.card_le_card
        (E.segmentAmbientBranchVertices_subset
          hbudget hrecords B hB i)
    _ ≤
        (E.segmentRecordedBranchVertices
          hbudget hrecords B hB i).card +
          (E.railGlueVertices i.1).card :=
      Finset.card_union_le _ _
    _ ≤ E.finalState.records.length * (2 * B) +
          2 * E.finalState.records.length :=
      Nat.add_le_add
        (E.segmentRecordedBranchVertices_card_le
          hbudget hrecords B hB i)
        (E.railGlueVertices_card_le i.1)

/-- Degree-two suppression estimate for one physical red segment in the
pre-thinning support.  Every later thinning only removes edges. -/
theorem exactRailSegment_boundary_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    ((simpleEdgeIndexedGraph (E.assembledSupport hbudget)).boundary
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i).vertexSet).card ≤
      4 * (E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2) := by
  have hbase :=
    GraphPath.boundary_card_le_degree_mul_branch_add_two
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i)
      (E.blueThinningInput hbudget).max_degree_four
  exact hbase.trans
    (Nat.mul_le_mul_left 4
      (Nat.add_le_add_right
        (E.segmentAmbientBranchVertices_card_le
          hbudget hrecords B hB i) 2))

/-- A physical red segment in the final degree-three outcome. -/
noncomputable def exactRailSegmentPathInThinned
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    GraphPath
      ((E.blueThinningInput hbudget).thinnedGraph outcome) :=
  (E.exactRailSegmentPathAt hbudget hrecords B hB i).mapLe
    (E.redSupport_le_thinnedGraph hbudget outcome)

@[simp] theorem exactRailSegmentPathInThinned_vertexSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.exactRailSegmentPathInThinned
      hbudget hrecords B hB outcome i).vertexSet =
        (E.exactRailSegmentPathAt
          hbudget hrecords B hB i).vertexSet := by
  simp [exactRailSegmentPathInThinned]

@[simp] theorem exactRailSegmentPathInThinned_edgeSet
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.exactRailSegmentPathInThinned
      hbudget hrecords B hB outcome i).edgeSet =
        (E.exactRailSegmentPathAt
          hbudget hrecords B hB i).edgeSet := by
  simp [exactRailSegmentPathInThinned]

/-- Segments cut internally by a physical vertex bipartition. -/
noncomputable def splitSegments
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (X Y : Finset V) :
    Finset (ExactRailSegmentIndex E hbudget hrecords B hB) :=
  Finset.univ.filter fun i =>
    ¬ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet ⊆ X ∧
    ¬ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet ⊆ Y

/-- Every internally split red segment contributes a physical cut edge in
every thinning outcome. -/
theorem exists_splitSegment_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (hi : i ∈ E.splitSegments hbudget hrecords B hB X Y) :
    ∃ e ∈
        (E.exactRailSegmentPathInThinned
          hbudget hrecords B hB outcome i).edgeSet,
      e ∈ Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y := by
  classical
  let Q :=
    E.exactRailSegmentPathInThinned
      hbudget hrecords B hB outcome i
  have hiData := (Finset.mem_filter.mp hi).2
  have hnotX : ¬ Q.vertexSet ⊆ X := by
    simpa [Q] using hiData.1
  have hnotY : ¬ Q.vertexSet ⊆ Y := by
    simpa [Q] using hiData.2
  have hsub : Q.vertexSet ⊆ X ∪ Y := by
    intro v hv
    rw [hcover]
    exact Finset.mem_univ v
  have hsource : Q.source ∈ X ∪ Y := hsub (GraphPath.source_mem_vertexSet Q)
  rcases Finset.mem_union.mp hsource with hx | hy
  · exact
      Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
        Q hsub hx hnotX
  · obtain ⟨e, heQ, heYX⟩ :=
      Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
        (X := Y) (Y := X) Q
        (by simpa [Finset.union_comm] using hsub) hy hnotY
    refine ⟨e, heQ, ?_⟩
    simpa [Section44.edgeBoundary_comm] using heYX

/-- Canonical physical cut edge charged by a split segment. -/
noncomputable def splitSegmentEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (i : {i : ExactRailSegmentIndex E hbudget hrecords B hB //
      i ∈ E.splitSegments hbudget hrecords B hB X Y}) : Sym2 V :=
  Classical.choose
    (E.exists_splitSegment_edgeBoundary
      hbudget hrecords B hB outcome hcover i.1 i.2)

theorem splitSegmentEdge_mem_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (i : {i : ExactRailSegmentIndex E hbudget hrecords B hB //
      i ∈ E.splitSegments hbudget hrecords B hB X Y}) :
    E.splitSegmentEdge hbudget hrecords B hB outcome hcover i ∈
      (E.exactRailSegmentPathAt
        hbudget hrecords B hB i.1).edgeSet := by
  simpa [splitSegmentEdge] using
    (Classical.choose_spec
      (E.exists_splitSegment_edgeBoundary
        hbudget hrecords B hB outcome hcover i.1 i.2)).1

theorem splitSegmentEdge_mem_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (i : {i : ExactRailSegmentIndex E hbudget hrecords B hB //
      i ∈ E.splitSegments hbudget hrecords B hB X Y}) :
    E.splitSegmentEdge hbudget hrecords B hB outcome hcover i ∈
      Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y :=
  (Classical.choose_spec
    (E.exists_splitSegment_edgeBoundary
      hbudget hrecords B hB outcome hcover i.1 i.2)).2

theorem splitSegmentEdge_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ) :
    Function.Injective
      (E.splitSegmentEdge
        hbudget hrecords B hB outcome hcover) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hdisjoint :=
    GraphPath.edgeDisjoint_of_nodeDisjoint
      (E.exactRailSegmentPathAt_nodeDisjoint
        hbudget hrecords B hB hne)
  exact Finset.disjoint_left.mp hdisjoint
    (E.splitSegmentEdge_mem_path
      hbudget hrecords B hB outcome hcover i)
    (by
      rw [hij]
      exact E.splitSegmentEdge_mem_path
        hbudget hrecords B hB outcome hcover j)

theorem splitSegments_card_le_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ) :
    (E.splitSegments hbudget hrecords B hB X Y).card ≤
      (Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card := by
  classical
  let f :
      {i : ExactRailSegmentIndex E hbudget hrecords B hB //
        i ∈ E.splitSegments hbudget hrecords B hB X Y} →
      {e : Sym2 V //
        e ∈ Section44.edgeBoundary
          ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y} :=
    fun i =>
      ⟨E.splitSegmentEdge hbudget hrecords B hB outcome hcover i,
        E.splitSegmentEdge_mem_boundary
          hbudget hrecords B hB outcome hcover i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact E.splitSegmentEdge_injective
      hbudget hrecords B hB outcome hcover
      (congrArg Subtype.val hij)
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Segment side induced by a physical cut: a segment is placed on `X` only
when all of its red vertices lie in `X`. -/
noncomputable def physicalSegmentSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (X : Finset V) :
    Finset (ExactRailSegmentIndex E hbudget hrecords B hB) :=
  Finset.univ.filter fun i =>
    (E.exactRailSegmentPathAt
      hbudget hrecords B hB i).vertexSet ⊆ X

@[simp] theorem mem_physicalSegmentSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (X : Finset V)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    i ∈ E.physicalSegmentSide hbudget hrecords B hB X ↔
      (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet ⊆ X := by
  simp [physicalSegmentSide]

/-- The initial physical terminal belongs to its named initial segment. -/
theorem initialTerminal_mem_initialTerminalSegment
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (x : Fin h) :
    E.initialTerminal hrecords x ∈
      (E.exactRailSegmentPathAt hbudget hrecords B hB
        (E.initialTerminalSegment
          hbudget hrecords B hB fallback x)).vertexSet := by
  obtain ⟨i, _hiRail, hiMem⟩ :=
    E.exists_exactRailSegmentIndex_of_redCarrier
      hbudget hrecords B hB
      (E.initialTerminal_redCarrier hbudget hrecords x)
  have howner :
      E.initialTerminalSegment hbudget hrecords B hB fallback x = i := by
    exact E.segmentOwner_eq_of_mem
      hbudget hrecords B hB fallback i hiMem
  simpa [howner] using hiMem

/-- Initial-terminal labels whose named segment is internally split. -/
noncomputable def splitInitialTerminalLabels
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (X Y : Finset V) : Finset (Fin h) :=
  Finset.univ.filter fun x =>
    E.initialTerminalSegment hbudget hrecords B hB fallback x ∈
      E.splitSegments hbudget hrecords B hB X Y

theorem splitInitialTerminalLabels_card_le
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (X Y : Finset V) :
    (E.splitInitialTerminalLabels
      hbudget hrecords B hB fallback X Y).card ≤
        (E.splitSegments hbudget hrecords B hB X Y).card := by
  classical
  let A :=
    E.splitInitialTerminalLabels
      hbudget hrecords B hB fallback X Y
  let f :=
    E.initialTerminalSegment hbudget hrecords B hB fallback
  have himage :
      A.image f ⊆ E.splitSegments hbudget hrecords B hB X Y := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  calc
    A.card = (A.image f).card := by
      symm
      exact Finset.card_image_of_injective A
        (E.initialTerminalSegment_injective
          hbudget hrecords B hB fallback)
    _ ≤ (E.splitSegments hbudget hrecords B hB X Y).card :=
      Finset.card_le_card himage

/-- Physical terminals on `X` are represented on the wholly-`X` segment
side, except for terminals whose initial segment is internally split. -/
theorem terminalSide_subset_segmentSide_union_split
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    E.terminalSide hrecords X ⊆
      E.initialTerminalSegmentSide hbudget hrecords B hB fallback
        (E.physicalSegmentSide hbudget hrecords B hB X) ∪
      E.splitInitialTerminalLabels
        hbudget hrecords B hB fallback X Y := by
  classical
  intro x hx
  have hxTerminal :
      E.initialTerminal hrecords x ∈ X :=
    (E.mem_terminalSide hrecords X x).mp hx
  let i :=
    E.initialTerminalSegment hbudget hrecords B hB fallback x
  have hxMem :
      E.initialTerminal hrecords x ∈
        (E.exactRailSegmentPathAt hbudget hrecords B hB i).vertexSet := by
    simpa [i] using
      E.initialTerminal_mem_initialTerminalSegment
        hbudget hrecords B hB fallback x
  by_cases hiX :
      (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet ⊆ X
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by
        exact (E.mem_physicalSegmentSide
          hbudget hrecords B hB X i).mpr hiX⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hiX, ?_⟩⟩
    intro hiY
    exact Finset.disjoint_left.mp hdisjoint hxTerminal (hiY hxMem)

/-- Every physical terminal on `Y` belongs to the complement of the
wholly-`X` segment side. -/
theorem terminalSide_subset_segmentSide_compl
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {X Y : Finset V}
    (hdisjoint : Disjoint X Y) :
    E.terminalSide hrecords Y ⊆
      E.initialTerminalSegmentSide hbudget hrecords B hB fallback
        (E.physicalSegmentSide hbudget hrecords B hB X)ᶜ := by
  classical
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.mem_compl]
  intro hiX
  have hyTerminal :
      E.initialTerminal hrecords x ∈ Y :=
    (E.mem_terminalSide hrecords Y x).mp hx
  have hmem :=
    E.initialTerminal_mem_initialTerminalSegment
      hbudget hrecords B hB fallback x
  have hsubset :=
    (E.mem_physicalSegmentSide
      hbudget hrecords B hB X _).mp hiX
  exact Finset.disjoint_left.mp hdisjoint (hsubset hmem) hyTerminal

theorem terminal_card_le_segment_card_add_split
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    (X ∩ P.left P.firstIndex).card ≤
      ((E.physicalSegmentSide hbudget hrecords B hB X) ∩
        E.initialTerminalSegments
          hbudget hrecords B hB fallback).card +
      (E.splitSegments hbudget hrecords B hB X Y).card := by
  rw [← E.terminalSide_card hbudget hrecords X,
    ← E.initialTerminalSegmentSide_card
      hbudget hrecords B hB fallback
        (E.physicalSegmentSide hbudget hrecords B hB X)]
  exact
    (Finset.card_le_card
      (E.terminalSide_subset_segmentSide_union_split
        hbudget hrecords B hB fallback hcover hdisjoint)).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left
          (E.splitInitialTerminalLabels_card_le
            hbudget hrecords B hB fallback X Y) _))

theorem terminal_compl_card_le_segment_compl_card
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {X Y : Finset V}
    (hdisjoint : Disjoint X Y) :
    (Y ∩ P.left P.firstIndex).card ≤
      ((E.physicalSegmentSide hbudget hrecords B hB X)ᶜ ∩
        E.initialTerminalSegments
          hbudget hrecords B hB fallback).card := by
  rw [← E.terminalSide_card hbudget hrecords Y,
    ← E.initialTerminalSegmentSide_card
      hbudget hrecords B hB fallback
        (E.physicalSegmentSide hbudget hrecords B hB X)ᶜ]
  exact Finset.card_le_card
    (E.terminalSide_subset_segmentSide_compl
      hbudget hrecords B hB fallback hdisjoint)

/-- A segment outside the wholly-`X` side which is not internally split lies
wholly in `Y`. -/
theorem segment_subset_right_of_not_side_of_not_split
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    {X Y : Finset V}
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (hiSide :
      i ∉ E.physicalSegmentSide hbudget hrecords B hB X)
    (hiSplit :
      i ∉ E.splitSegments hbudget hrecords B hB X Y) :
    (E.exactRailSegmentPathAt
      hbudget hrecords B hB i).vertexSet ⊆ Y := by
  have hnotX :
      ¬ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet ⊆ X := by
    simpa using hiSide
  have hnotBoth :
      ¬ (¬ (E.exactRailSegmentPathAt
            hbudget hrecords B hB i).vertexSet ⊆ X ∧
          ¬ (E.exactRailSegmentPathAt
            hbudget hrecords B hB i).vertexSet ⊆ Y) := by
    simpa [splitSegments] using hiSplit
  by_contra hnotY
  exact hnotBoth ⟨hnotX, hnotY⟩

/-- Terminal loss incurred when the physical cut splits red segments. -/
theorem terminal_min_le_segment_min_add_split
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    min (X ∩ P.left P.firstIndex).card
        (Y ∩ P.left P.firstIndex).card ≤
      min
          ((E.physicalSegmentSide hbudget hrecords B hB X) ∩
            E.initialTerminalSegments
              hbudget hrecords B hB fallback).card
          ((E.physicalSegmentSide hbudget hrecords B hB X)ᶜ ∩
            E.initialTerminalSegments
              hbudget hrecords B hB fallback).card +
        (E.splitSegments hbudget hrecords B hB X Y).card := by
  have hleft :=
    E.terminal_card_le_segment_card_add_split
      hbudget hrecords B hB fallback hcover hdisjoint
  have hright :=
    E.terminal_compl_card_le_segment_compl_card
      hbudget hrecords B hB fallback hdisjoint
  omega

/-- Every red-carried vertex lies in the physical segment selected by the
segment-owner map. -/
theorem redCarrier_mem_segmentOwner
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {v : V} {x : Fin h}
    (hv : E.RedCarrier hbudget v x) :
    v ∈ (E.exactRailSegmentPathAt hbudget hrecords B hB
      (E.segmentOwner hbudget hrecords B hB fallback v)).vertexSet := by
  obtain ⟨i, _hiRail, hiMem⟩ :=
    E.exists_exactRailSegmentIndex_of_redCarrier
      hbudget hrecords B hB hv
  have howner :=
    E.segmentOwner_eq_of_mem
      hbudget hrecords B hB fallback i hiMem
  simpa [howner] using hiMem

/-- An assembled edge outside the blue support has red-carried endpoints. -/
theorem nonBlue_assembled_edge_endpoints_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    {e : Sym2 V}
    (he : e ∈ (E.assembledSupport hbudget).edgeSet)
    (hnotBlue : e ∉ E.blueSupport.edgeSet) :
    (∃ x : Fin h, E.RedCarrier hbudget e.out.1 x) ∧
      ∃ y : Fin h, E.RedCarrier hbudget e.out.2 y := by
  have hadj :
      (E.assembledSupport hbudget).Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using he
  rcases hadj with hred | hblue
  · obtain ⟨x, hx, hy⟩ :=
      E.redSupport_adj_has_carrier hbudget hred
    exact ⟨⟨x, hx⟩, ⟨x, hy⟩⟩
  · exfalso
    apply hnotBlue
    rw [← _root_.SimpleGraph.mem_edgeSet] at hblue
    simpa [Sym2.mk, e.out_eq] using hblue

/-- The two red endpoints of a suppressed blue transition have the same
segment owners as the two endpoints of its owner-changing representative
edge, up to swapping. -/
theorem blueSegmentTransition_endpoint_owner
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {v : V}
    (hv : v ∈ E.blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e) :
    E.segmentOwner hbudget hrecords B hB fallback v =
        E.segmentOwner hbudget hrecords B hB fallback e.1.out.1 ∨
      E.segmentOwner hbudget hrecords B hB fallback v =
        E.segmentOwner hbudget hrecords B hB fallback e.1.out.2 := by
  classical
  let z :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let hu :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).1
  let hw :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).2
  let p := E.precedingRedVertex hbudget z e.1.out.1 hu
  let q := E.precedingRedVertex hbudget z e.1.out.2 hw
  have hvpq : v = p ∨ v = q := by
    simpa [blueSegmentTransitionEndpoints, z, he, hu, hw, p, q]
      using hv
  rcases hvpq with rfl | rfl
  · left
    exact E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.1 hu
  · right
    exact E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.2 hw

/-- The source of the complete suppressed link has the owner of the first
endpoint of its representative edge. -/
theorem blueSegmentTransitionPath_source_owner
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    E.segmentOwner hbudget hrecords B hB fallback
        (E.blueSegmentTransitionPath
          hbudget hrecords B hB fallback e).source =
      E.segmentOwner hbudget hrecords B hB fallback e.1.out.1 := by
  classical
  let z :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let hu :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).1
  let hw :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).2
  have howner :=
    E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.1 hu
  change
    E.segmentOwner hbudget hrecords B hB fallback
        (E.predecessorArc hbudget z hu hw).source =
      E.segmentOwner hbudget hrecords B hB fallback e.1.out.1
  rw [E.predecessorArc_source]
  exact howner

/-- The target of the complete suppressed link has the owner of the second
endpoint of its representative edge. -/
theorem blueSegmentTransitionPath_target_owner
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    E.segmentOwner hbudget hrecords B hB fallback
        (E.blueSegmentTransitionPath
          hbudget hrecords B hB fallback e).target =
      E.segmentOwner hbudget hrecords B hB fallback e.1.out.2 := by
  classical
  let z :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let hu :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).1
  let hw :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).2
  have howner :=
    E.segmentOwner_precedingRedVertex
      hbudget hrecords B hB fallback z e.1.out.2 hw
  change
    E.segmentOwner hbudget hrecords B hB fallback
        (E.predecessorArc hbudget z hu hw).target =
      E.segmentOwner hbudget hrecords B hB fallback e.1.out.2
  rw [E.predecessorArc_target]
  exact howner

/-- Both endpoints of a complete transition path lie in their owner
segments. -/
theorem blueSegmentTransitionPath_endpoints_mem_ownerSegments
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    let Q := E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e
    Q.source ∈
        (E.exactRailSegmentPathAt hbudget hrecords B hB
          (E.segmentOwner hbudget hrecords B hB fallback Q.source)).vertexSet ∧
      Q.target ∈
        (E.exactRailSegmentPathAt hbudget hrecords B hB
          (E.segmentOwner hbudget hrecords B hB fallback Q.target)).vertexSet := by
  classical
  dsimp only
  have hsourceEndpoint :
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).source ∈
        E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e := by
    rw [← E.blueSegmentTransitionPath_endpoints
      hbudget hrecords B hB fallback e]
    simp
  have htargetEndpoint :
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).target ∈
        E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e := by
    rw [← E.blueSegmentTransitionPath_endpoints
      hbudget hrecords B hB fallback e]
    simp
  obtain ⟨xs, hs⟩ :=
    (E.mem_redCarrierVertices hbudget _).mp
      ((E.mem_blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e hsourceEndpoint).2)
  obtain ⟨xt, ht⟩ :=
    (E.mem_redCarrierVertices hbudget _).mp
      ((E.mem_blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e htargetEndpoint).2)
  exact ⟨E.redCarrier_mem_segmentOwner
      hbudget hrecords B hB fallback hs,
    E.redCarrier_mem_segmentOwner
      hbudget hrecords B hB fallback ht⟩

/-- The owner segments at the two ends of a transition path are distinct. -/
theorem blueSegmentTransitionPath_endpoint_owners_ne
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    let Q := E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e
    E.segmentOwner hbudget hrecords B hB fallback Q.source ≠
      E.segmentOwner hbudget hrecords B hB fallback Q.target := by
  dsimp only
  rw [E.blueSegmentTransitionPath_source_owner
    hbudget hrecords B hB fallback e,
    E.blueSegmentTransitionPath_target_owner
      hbudget hrecords B hB fallback e]
  exact (Finset.mem_filter.mp e.2.1).2

/-- Each end of a suppressed link is an external-incidence vertex of its
owner red segment. -/
theorem blueSegmentTransitionPath_endpoint_mem_externalVertices
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    (v : V)
    (hvEndpoint :
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).IsEndpoint v) :
    v ∈ GraphPath.externalVertices
      (E.exactRailSegmentPathInAssembled hbudget hrecords B hB
        (E.segmentOwner hbudget hrecords B hB fallback v)) := by
  classical
  let Q :=
    E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
  let i :=
    E.segmentOwner hbudget hrecords B hB fallback v
  have hvPair :
      v ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
    rw [← E.blueSegmentTransitionPath_endpoints
      hbudget hrecords B hB fallback e]
    rcases hvEndpoint with rfl | rfl <;> simp
  obtain ⟨x, hvCarrier⟩ :=
    (E.mem_redCarrierVertices hbudget v).mp
      ((E.mem_blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e hvPair).2)
  have hvSegment :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet :=
    E.redCarrier_mem_segmentOwner
      hbudget hrecords B hB fallback hvCarrier
  have hQne : Q.source ≠ Q.target :=
    E.blueSegmentTransitionPath_source_ne_target
      hbudget hrecords B hB fallback e
  have hvQ : v ∈ Q.vertexSet := by
    rcases hvEndpoint with hvSource | hvTarget
    · rw [hvSource]
      exact GraphPath.source_mem_vertexSet Q
    · rw [hvTarget]
      exact GraphPath.target_mem_vertexSet Q
  obtain ⟨g, hgQ, hvg⟩ :=
    Q.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hQne hvQ
  rcases Sym2.mem_iff_exists.mp hvg with ⟨w, hgw⟩
  have hgwQ : s(v, w) ∈ Q.edgeSet := by
    rw [← hgw]
    exact hgQ
  have hvw : (E.assembledSupport hbudget).Adj v w :=
    GraphPath.edgeSet_subset_edgeSet Q hgwQ
  have hwNot :
      w ∉ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet := by
    intro hwSegment
    have hwRail :
        w ∈ (E.exactRailPath hbudget hrecords i.1).vertexSet :=
      E.exactRailSegmentPathAt_vertexSet_subset_rail
        hbudget hrecords B hB i hwSegment
    have hwCarrier :
        w ∈ E.redCarrierVertices hbudget := by
      exact (E.mem_redCarrierVertices hbudget w).mpr
        ⟨i.1, E.exactRailPath_vertex_has_carrier
          hbudget hrecords hwRail⟩
    have hwQ :
        w ∈ Q.vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hgwQ).2
    have hwEndpoint :
        Q.IsEndpoint w :=
      E.blueSegmentTransitionPath_internally_carrier_clean
        hbudget hrecords B hB fallback e hwQ hwCarrier
    have hvwNe : v ≠ w := hvw.ne
    have hownerW :
        E.segmentOwner hbudget hrecords B hB fallback w = i :=
      E.segmentOwner_eq_of_mem
        hbudget hrecords B hB fallback i hwSegment
    have hownersNe :=
      E.blueSegmentTransitionPath_endpoint_owners_ne
        hbudget hrecords B hB fallback e
    rcases hvEndpoint with hvSource | hvTarget
    · rcases hwEndpoint with hwSource | hwTarget
      · exact hvwNe (hvSource.trans hwSource.symm)
      · exact hownersNe (by
          rw [← hvSource, ← hwTarget, hownerW])
    · rcases hwEndpoint with hwSource | hwTarget
      · exact hownersNe (by
          rw [← hwSource, ← hvTarget, hownerW])
      · exact hvwNe (hvTarget.trans hwTarget.symm)
  exact (GraphPath.mem_externalVertices
    (E.exactRailSegmentPathInAssembled hbudget hrecords B hB i) v).mpr
      ⟨by simpa [i] using hvSegment, w, hvw, by simpa [i] using hwNot⟩

/-- Blue transitions incident with a fixed physical segment. -/
noncomputable def blueTransitionsIncidentSegment
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Finset (E.BlueSegmentTransition hbudget hrecords B hB fallback) :=
  Finset.univ.filter fun e =>
    E.segmentOwner hbudget hrecords B hB fallback
        (E.blueSegmentTransitionPath
          hbudget hrecords B hB fallback e).source = i ∨
    E.segmentOwner hbudget hrecords B hB fallback
        (E.blueSegmentTransitionPath
          hbudget hrecords B hB fallback e).target = i

/-- The named-edge index of the endpoint pair of a blue transition. -/
noncomputable def blueTransitionEdgeIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    (simpleEdgeIndexedGraph
      (E.blueSegmentTransitionGraph
        hbudget hrecords B hB fallback)).Edge := by
  classical
  exact
    (E.blueSegmentTransitionGraph
      hbudget hrecords B hB fallback).edgeFinset.equivFin
    ⟨E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e,
      _root_.SimpleGraph.mem_edgeFinset.mpr
        (E.blueSegmentTransitionEndpoints_mem_graph_edgeSet
          hbudget hrecords B hB fallback e)⟩

theorem blueTransitionEdgeIndex_edgeAt
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback) :
    simpleEdgeIndexedGraph.edgeAt
      (E.blueSegmentTransitionGraph hbudget hrecords B hB fallback)
      (E.blueTransitionEdgeIndex
        hbudget hrecords B hB fallback e) =
      E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
  classical
  let K :=
    E.blueSegmentTransitionGraph hbudget hrecords B hB fallback
  simp [blueTransitionEdgeIndex,
    simpleEdgeIndexedGraph.edgeAt, K]

theorem blueTransitionEdgeIndex_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Function.Injective
      (E.blueTransitionEdgeIndex hbudget hrecords B hB fallback) := by
  intro e f hef
  apply E.blueSegmentTransitionEndpoints_injective
    hbudget hrecords B hB fallback
  rw [← E.blueTransitionEdgeIndex_edgeAt
      hbudget hrecords B hB fallback e,
    ← E.blueTransitionEdgeIndex_edgeAt
      hbudget hrecords B hB fallback f,
    hef]

theorem blueTransitionEdgeIndex_mem_incident
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    (he : e ∈ E.blueTransitionsIncidentSegment
      hbudget hrecords B hB fallback i) :
    E.blueTransitionEdgeIndex hbudget hrecords B hB fallback e ∈
      incidentEdgeIndices
        (E.blueSegmentTransitionGraph hbudget hrecords B hB fallback)
        (GraphPath.externalVertices
          (E.exactRailSegmentPathInAssembled
            hbudget hrecords B hB i)) := by
  classical
  let Q :=
    E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
  have heData := (Finset.mem_filter.mp he).2
  rcases heData with hsource | htarget
  · have hvExternal :
        Q.source ∈ GraphPath.externalVertices
          (E.exactRailSegmentPathInAssembled
            hbudget hrecords B hB i) := by
      have hbase :=
        E.blueSegmentTransitionPath_endpoint_mem_externalVertices
          hbudget hrecords B hB fallback e Q.source (Or.inl rfl)
      simpa [Q, hsource] using hbase
    apply Finset.mem_biUnion.mpr
    refine ⟨Q.source, hvExternal, ?_⟩
    apply
      (simpleEdgeIndexedGraph.mem_edgeAt_iff_mem_incidentEdges
        (E.blueSegmentTransitionGraph
          hbudget hrecords B hB fallback) Q.source _).mp
    rw [E.blueTransitionEdgeIndex_edgeAt
      hbudget hrecords B hB fallback e,
      ← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback e]
    simp [Q]
  · have hvExternal :
        Q.target ∈ GraphPath.externalVertices
          (E.exactRailSegmentPathInAssembled
            hbudget hrecords B hB i) := by
      have hbase :=
        E.blueSegmentTransitionPath_endpoint_mem_externalVertices
          hbudget hrecords B hB fallback e Q.target (Or.inr rfl)
      simpa [Q, htarget] using hbase
    apply Finset.mem_biUnion.mpr
    refine ⟨Q.target, hvExternal, ?_⟩
    apply
      (simpleEdgeIndexedGraph.mem_edgeAt_iff_mem_incidentEdges
        (E.blueSegmentTransitionGraph
          hbudget hrecords B hB fallback) Q.target _).mp
    rw [E.blueTransitionEdgeIndex_edgeAt
      hbudget hrecords B hB fallback e,
      ← E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback e]
    simp [Q]

theorem blueTransitionsIncidentSegment_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.blueTransitionsIncidentSegment
      hbudget hrecords B hB fallback i).card ≤
      2 * (E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2) := by
  classical
  let T :=
    E.blueTransitionsIncidentSegment
      hbudget hrecords B hB fallback i
  let K :=
    E.blueSegmentTransitionGraph hbudget hrecords B hB fallback
  let U :=
    GraphPath.externalVertices
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i)
  let f :
      {e : E.BlueSegmentTransition hbudget hrecords B hB fallback //
        e ∈ T} →
      {q : (simpleEdgeIndexedGraph K).Edge //
        q ∈ incidentEdgeIndices K U} :=
    fun e =>
      ⟨E.blueTransitionEdgeIndex
          hbudget hrecords B hB fallback e.1,
        E.blueTransitionEdgeIndex_mem_incident
          hbudget hrecords B hB fallback i e.1 e.2⟩
  have hf : Function.Injective f := by
    intro e q heq
    apply Subtype.ext
    exact E.blueTransitionEdgeIndex_injective
      hbudget hrecords B hB fallback
      (congrArg Subtype.val heq)
  have hcard :
      T.card ≤ (incidentEdgeIndices K U).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  have hdegree :
      (incidentEdgeIndices K U).card ≤ 2 * U.card :=
    incidentEdgeIndices_card_le K U
      (E.blueSegmentTransitionGraph_maxDegreeAtMost_two
        hbudget hrecords B hB fallback)
  have hU :
      U.card ≤ E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2 := by
    exact
      (GraphPath.externalVertices_card_le_branch_add_two
        (E.exactRailSegmentPathInAssembled
          hbudget hrecords B hB i)).trans
        (Nat.add_le_add_right
          (E.segmentAmbientBranchVertices_card_le
            hbudget hrecords B hB i) 2)
  exact hcard.trans (hdegree.trans (Nat.mul_le_mul_left 2 hU))

/-- Owner-changing nonblue edges incident with a fixed red segment. -/
noncomputable def nonBlueEdgesIncidentSegment
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Finset (Sym2 V) := by
  classical
  exact
    (E.segmentCrossingEdges hbudget hrecords B hB fallback).filter fun e =>
      e ∉ E.blueSupport.edgeSet ∧
        (E.segmentOwner hbudget hrecords B hB fallback e.out.1 = i ∨
          E.segmentOwner hbudget hrecords B hB fallback e.out.2 = i)

/-- Named assembled-support edge corresponding to a nonblue incident edge. -/
noncomputable def nonBlueIncidentEdgeIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : {e : Sym2 V //
      e ∈ E.nonBlueEdgesIncidentSegment
        hbudget hrecords B hB fallback i}) :
    (simpleEdgeIndexedGraph (E.assembledSupport hbudget)).Edge := by
  classical
  have heSupport :
      e.1 ∈ (E.assembledSupport hbudget).edgeFinset := by
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp e.2).1).1
  exact (E.assembledSupport hbudget).edgeFinset.equivFin
    ⟨e.1, heSupport⟩

theorem nonBlueIncidentEdgeIndex_edgeAt
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : {e : Sym2 V //
      e ∈ E.nonBlueEdgesIncidentSegment
        hbudget hrecords B hB fallback i}) :
    simpleEdgeIndexedGraph.edgeAt (E.assembledSupport hbudget)
      (E.nonBlueIncidentEdgeIndex
        hbudget hrecords B hB fallback i e) = e.1 := by
  classical
  simp [nonBlueIncidentEdgeIndex, simpleEdgeIndexedGraph.edgeAt]

theorem nonBlueIncidentEdgeIndex_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Function.Injective
      (E.nonBlueIncidentEdgeIndex
        hbudget hrecords B hB fallback i) := by
  intro e f hef
  apply Subtype.ext
  rw [← E.nonBlueIncidentEdgeIndex_edgeAt
      hbudget hrecords B hB fallback i e,
    ← E.nonBlueIncidentEdgeIndex_edgeAt
      hbudget hrecords B hB fallback i f,
    hef]

theorem nonBlueIncidentEdgeIndex_mem_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : {e : Sym2 V //
      e ∈ E.nonBlueEdgesIncidentSegment
        hbudget hrecords B hB fallback i}) :
    E.nonBlueIncidentEdgeIndex hbudget hrecords B hB fallback i e ∈
      (simpleEdgeIndexedGraph (E.assembledSupport hbudget)).boundary
        (E.exactRailSegmentPathInAssembled
          hbudget hrecords B hB i).vertexSet := by
  classical
  let owner :=
    E.segmentOwner hbudget hrecords B hB fallback
  let U :=
    (E.exactRailSegmentPathInAssembled
      hbudget hrecords B hB i).vertexSet
  have heData := (Finset.mem_filter.mp e.2).2
  have heCross :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp e.2).1).2
  have heSupport :
      e.1 ∈ (E.assembledSupport hbudget).edgeSet := by
    exact _root_.SimpleGraph.mem_edgeFinset.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp e.2).1).1
  have hcarriers :=
    E.nonBlue_assembled_edge_endpoints_redCarrier
      hbudget heSupport heData.1
  have hleftMem :
      e.1.out.1 ∈
        (E.exactRailSegmentPathAt hbudget hrecords B hB
          (owner e.1.out.1)).vertexSet :=
    E.redCarrier_mem_segmentOwner
      hbudget hrecords B hB fallback hcarriers.1.choose_spec
  have hrightMem :
      e.1.out.2 ∈
        (E.exactRailSegmentPathAt hbudget hrecords B hB
          (owner e.1.out.2)).vertexSet :=
    E.redCarrier_mem_segmentOwner
      hbudget hrecords B hB fallback hcarriers.2.choose_spec
  have hcrossPhysical :
      (e.1.out.1 ∈ U ∧ e.1.out.2 ∉ U) ∨
        (e.1.out.2 ∈ U ∧ e.1.out.1 ∉ U) := by
    rcases heData.2 with hleft | hright
    · left
      have hleftU : e.1.out.1 ∈ U := by
        simpa [U, owner, hleft] using hleftMem
      refine ⟨hleftU, ?_⟩
      intro hrightU
      have hownerRight :
          owner e.1.out.2 = i :=
        E.segmentOwner_eq_of_mem hbudget hrecords B hB fallback i
          (by simpa [U] using hrightU)
      exact heCross (hleft.trans hownerRight.symm)
    · right
      have hrightU : e.1.out.2 ∈ U := by
        simpa [U, owner, hright] using hrightMem
      refine ⟨hrightU, ?_⟩
      intro hleftU
      have hownerLeft :
          owner e.1.out.1 = i :=
        E.segmentOwner_eq_of_mem hbudget hrecords B hB fallback i
          (by simpa [U] using hleftU)
      exact heCross (hownerLeft.trans hright.symm)
  apply
    ((simpleEdgeIndexedGraph (E.assembledSupport hbudget)).mem_boundary
      U _).mpr
  change
    (((simpleEdgeIndexedGraph (E.assembledSupport hbudget)).left
          (E.nonBlueIncidentEdgeIndex
            hbudget hrecords B hB fallback i e) ∈ U ∧
        (simpleEdgeIndexedGraph (E.assembledSupport hbudget)).right
          (E.nonBlueIncidentEdgeIndex
            hbudget hrecords B hB fallback i e) ∉ U) ∨
      ((simpleEdgeIndexedGraph (E.assembledSupport hbudget)).right
          (E.nonBlueIncidentEdgeIndex
            hbudget hrecords B hB fallback i e) ∈ U ∧
        (simpleEdgeIndexedGraph (E.assembledSupport hbudget)).left
          (E.nonBlueIncidentEdgeIndex
            hbudget hrecords B hB fallback i e) ∉ U))
  rw [simpleEdgeIndexedGraph.left_eq_edgeAt_out_fst,
    simpleEdgeIndexedGraph.right_eq_edgeAt_out_snd,
    E.nonBlueIncidentEdgeIndex_edgeAt
      hbudget hrecords B hB fallback i e]
  exact hcrossPhysical

theorem nonBlueEdgesIncidentSegment_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.nonBlueEdgesIncidentSegment
      hbudget hrecords B hB fallback i).card ≤
      4 * (E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2) := by
  classical
  let R :=
    E.nonBlueEdgesIncidentSegment
      hbudget hrecords B hB fallback i
  let D :=
    (simpleEdgeIndexedGraph (E.assembledSupport hbudget)).boundary
      (E.exactRailSegmentPathInAssembled
        hbudget hrecords B hB i).vertexSet
  let f :
      {e : Sym2 V // e ∈ R} → {q // q ∈ D} :=
    fun e =>
      ⟨E.nonBlueIncidentEdgeIndex
          hbudget hrecords B hB fallback i e,
        E.nonBlueIncidentEdgeIndex_mem_boundary
          hbudget hrecords B hB fallback i e⟩
  have hf : Function.Injective f := by
    intro e q heq
    exact E.nonBlueIncidentEdgeIndex_injective
      hbudget hrecords B hB fallback i
      (congrArg Subtype.val heq)
  have hcard : R.card ≤ D.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  exact hcard.trans
    (E.exactRailSegment_boundary_card_le
      hbudget hrecords B hB i)

private theorem segmentBetween_vertexIndex_bounds
    {K : _root_.SimpleGraph V} (Q : GraphPath K)
    {x y v : V} (hx : x ∈ Q.vertexSet) (hy : y ∈ Q.vertexSet)
    (hv : v ∈ (GraphPath.segmentBetween Q hx hy).vertexSet) :
    min (Q.vertexIndex x) (Q.vertexIndex y) ≤ Q.vertexIndex v ∧
      Q.vertexIndex v ≤ max (Q.vertexIndex x) (Q.vertexIndex y) := by
  classical
  by_cases hxy : Q.vertexIndex x ≤ Q.vertexIndex y
  · let hbefore : Q.Before x y :=
      (Q.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have hv' : v ∈ (Q.segmentOfBefore hbefore).vertexSet := by
      simpa [GraphPath.segmentBetween, hxy, hbefore] using hv
    have hleft :=
      (Q.before_iff_vertexIndex_le).1
        (Q.before_of_mem_segmentOfBefore_left hbefore hv')
    have hright :=
      (Q.before_iff_vertexIndex_le).1
        (Q.before_of_mem_segmentOfBefore_right hbefore hv')
    simpa [Nat.min_eq_left hxy, Nat.max_eq_right hxy] using
      And.intro hleft.2.2 hright.2.2
  · have hyx : Q.vertexIndex y ≤ Q.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : Q.Before y x :=
      (Q.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have hv' : v ∈ (Q.segmentOfBefore hbefore).vertexSet := by
      simpa [GraphPath.segmentBetween, hxy, hbefore] using hv
    have hleft :=
      (Q.before_iff_vertexIndex_le).1
        (Q.before_of_mem_segmentOfBefore_left hbefore hv')
    have hright :=
      (Q.before_iff_vertexIndex_le).1
        (Q.before_of_mem_segmentOfBefore_right hbefore hv')
    simpa [Nat.min_eq_right hyx, Nat.max_eq_left hyx] using
      And.intro hleft.2.2 hright.2.2

private theorem mem_segmentBetween_of_vertexIndex_bounds
    {K : _root_.SimpleGraph V} (Q : GraphPath K)
    {x y v : V} (hx : x ∈ Q.vertexSet) (hy : y ∈ Q.vertexSet)
    (hv : v ∈ Q.vertexSet)
    (hlow : min (Q.vertexIndex x) (Q.vertexIndex y) ≤ Q.vertexIndex v)
    (hhigh : Q.vertexIndex v ≤
      max (Q.vertexIndex x) (Q.vertexIndex y)) :
    v ∈ (GraphPath.segmentBetween Q hx hy).vertexSet := by
  classical
  by_cases hxy : Q.vertexIndex x ≤ Q.vertexIndex y
  · let hbefore : Q.Before x y :=
      (Q.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    have hxv : Q.Before x v :=
      (Q.before_iff_vertexIndex_le).2
        ⟨hx, hv, by simpa [Nat.min_eq_left hxy] using hlow⟩
    have hvy : Q.Before v y :=
      (Q.before_iff_vertexIndex_le).2
        ⟨hv, hy, by simpa [Nat.max_eq_right hxy] using hhigh⟩
    have hv' :=
      Q.mem_segmentOfBefore_of_before_of_before hbefore hxv hvy
    simpa [GraphPath.segmentBetween, hxy, hbefore] using hv'
  · have hyx : Q.vertexIndex y ≤ Q.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : Q.Before y x :=
      (Q.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    have hyv : Q.Before y v :=
      (Q.before_iff_vertexIndex_le).2
        ⟨hy, hv, by simpa [Nat.min_eq_right hyx] using hlow⟩
    have hvx : Q.Before v x :=
      (Q.before_iff_vertexIndex_le).2
        ⟨hv, hx, by simpa [Nat.max_eq_left hyx] using hhigh⟩
    have hv' :=
      Q.mem_segmentOfBefore_of_before_of_before hbefore hyv hvx
    simpa [GraphPath.segmentBetween, hxy, hbefore] using hv'

/-- No red-carried vertex lies strictly between the two red endpoints of one
complete blue transition in the ambient local-blue-path order. -/
theorem blueSegmentTransition_no_carrier_strict_between
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {v : V}
    (hv :
      v ∈ (E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2).vertexSet)
    (hvCarrier : v ∈ E.redCarrierVertices hbudget)
    (hlow :
      min
          ((E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).2).vertexIndex
                (E.blueSegmentTransitionPath
                  hbudget hrecords B hB fallback e).source)
          ((E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).2).vertexIndex
                (E.blueSegmentTransitionPath
                  hbudget hrecords B hB fallback e).target) <
        (E.localBluePath
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).1
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).2).vertexIndex v)
    (hhigh :
      (E.localBluePath
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).1
          (E.blueSegmentTransitionIndex
            hbudget hrecords B hB fallback e).2).vertexIndex v <
        max
          ((E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).2).vertexIndex
                (E.blueSegmentTransitionPath
                  hbudget hrecords B hB fallback e).source)
          ((E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback e).2).vertexIndex
                (E.blueSegmentTransitionPath
                  hbudget hrecords B hB fallback e).target)) :
    False := by
  classical
  let Q :=
    E.localBluePath
      (E.blueSegmentTransitionIndex
        hbudget hrecords B hB fallback e).1
      (E.blueSegmentTransitionIndex
        hbudget hrecords B hB fallback e).2
  let R :=
    E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
  have hpair :
      E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e =
        s(R.source, R.target) := by
    exact (E.blueSegmentTransitionPath_endpoints
      hbudget hrecords B hB fallback e).symm
  have hsourcePair :
      R.source ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
    rw [hpair]
    simp
  have htargetPair :
      R.target ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
    rw [hpair]
    simp
  have hsourceQ :
      R.source ∈ Q.vertexSet :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hsourcePair).1
  have htargetQ :
      R.target ∈ Q.vertexSet :=
    (E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e htargetPair).1
  have hvR : v ∈ R.vertexSet := by
    by_cases hst : Q.vertexIndex R.source ≤ Q.vertexIndex R.target
    · apply E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback e
        (x := R.source) (y := v) (z := R.target) hpair
      · exact (Q.before_iff_vertexIndex_le).2
          ⟨hsourceQ, hv, by
            simpa [Q, R, Nat.min_eq_left hst] using Nat.le_of_lt hlow⟩
      · exact (Q.before_iff_vertexIndex_le).2
          ⟨hv, htargetQ, by
            simpa [Q, R, Nat.max_eq_right hst] using Nat.le_of_lt hhigh⟩
    · have hts : Q.vertexIndex R.target ≤ Q.vertexIndex R.source :=
        Nat.le_of_lt (Nat.lt_of_not_ge hst)
      apply E.mem_blueSegmentTransitionPath_of_between
        hbudget hrecords B hB fallback e
        (x := R.target) (y := v) (z := R.source)
        (by simpa [Sym2.eq_swap] using hpair)
      · exact (Q.before_iff_vertexIndex_le).2
          ⟨htargetQ, hv, by
            simpa [Q, R, Nat.min_eq_right hts] using Nat.le_of_lt hlow⟩
      · exact (Q.before_iff_vertexIndex_le).2
          ⟨hv, hsourceQ, by
            simpa [Q, R, Nat.max_eq_left hts] using Nat.le_of_lt hhigh⟩
  have hvEndpoint : R.IsEndpoint v :=
    E.blueSegmentTransitionPath_internally_carrier_clean
      hbudget hrecords B hB fallback e hvR hvCarrier
  rcases hvEndpoint with rfl | rfl
  · have :
        min (Q.vertexIndex R.source) (Q.vertexIndex R.target) <
          Q.vertexIndex R.source := by
      simpa [Q, R] using hlow
    have :
        Q.vertexIndex R.source <
          max (Q.vertexIndex R.source) (Q.vertexIndex R.target) := by
      simpa [Q, R] using hhigh
    omega
  · have :
        min (Q.vertexIndex R.source) (Q.vertexIndex R.target) <
          Q.vertexIndex R.target := by
      simpa [Q, R] using hlow
    have :
        Q.vertexIndex R.target <
          max (Q.vertexIndex R.source) (Q.vertexIndex R.target) := by
      simpa [Q, R] using hhigh
    omega

/-- Vertices of a complete transition path lie between its red endpoints in
the ambient local-blue-path order. -/
theorem blueSegmentTransitionPath_vertexIndex_bounds
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    {v : V}
    (hv : v ∈ (E.blueSegmentTransitionPath
      hbudget hrecords B hB fallback e).vertexSet) :
    let Q :=
      E.localBluePath
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).1
        (E.blueSegmentTransitionIndex
          hbudget hrecords B hB fallback e).2
    let R :=
      E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
    min (Q.vertexIndex R.source) (Q.vertexIndex R.target) ≤
        Q.vertexIndex v ∧
      Q.vertexIndex v ≤
        max (Q.vertexIndex R.source) (Q.vertexIndex R.target) := by
  classical
  dsimp only
  let z :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e
  let he : s(e.1.out.1, e.1.out.2) ∈
      (E.localBluePath z.1 z.2).edgeSet := by
    rw [Sym2.mk, e.1.out_eq]
    exact E.blueSegmentTransition_mem_path
      hbudget hrecords B hB fallback e
  let hu :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).1
  let hw :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1 z.2) he).2
  let p := E.precedingRedVertex hbudget z e.1.out.1 hu
  let q := E.precedingRedVertex hbudget z e.1.out.2 hw
  have hp :
      p ∈ (E.localBluePath z.1 z.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z e.1.out.1 hu)).1
  have hq :
      q ∈ (E.localBluePath z.1 z.2).vertexSet :=
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z e.1.out.2 hw)).1
  have hv' :
      v ∈ (GraphPath.segmentBetween
        (E.localBluePath z.1 z.2) hp hq).vertexSet := by
    simpa [blueSegmentTransitionPath, predecessorArc, z, he, hu, hw,
      p, q] using hv
  have hbounds :=
    segmentBetween_vertexIndex_bounds
      (E.localBluePath z.1 z.2) hp hq hv'
  have hsource :
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).source = p := by
    simp [blueSegmentTransitionPath, GraphPath.mapLe,
      predecessorArc, z, p]
  have htarget :
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).target = q := by
    simp [blueSegmentTransitionPath, GraphPath.mapLe,
      predecessorArc, z, q]
  rw [hsource, htarget]
  simpa [z] using hbounds

/-- Distinct suppressed transition links are physically edge-disjoint.  They
may meet at a red endpoint, but the carrier-clean consecutive arcs on a local
blue path cannot overlap in an edge. -/
theorem blueSegmentTransitionPath_edgeDisjoint_of_ne
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (e f : E.BlueSegmentTransition hbudget hrecords B hB fallback)
    (hef : e ≠ f) :
    Disjoint
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback e).edgeSet
      (E.blueSegmentTransitionPath
        hbudget hrecords B hB fallback f).edgeSet := by
  classical
  rw [Finset.disjoint_left]
  intro g hge hgf
  let Re :=
    E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
  let Rf :=
    E.blueSegmentTransitionPath hbudget hrecords B hB fallback f
  let ze :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e
  let zf :=
    E.blueSegmentTransitionIndex hbudget hrecords B hB fallback f
  let Qe := E.localBluePath ze.1 ze.2
  let Qf := E.localBluePath zf.1 zf.2
  have hge' : s(g.out.1, g.out.2) ∈ Re.edgeSet := by
    simpa [Sym2.mk, g.out_eq, Re] using hge
  have hgf' : s(g.out.1, g.out.2) ∈ Rf.edgeSet := by
    simpa [Sym2.mk, g.out_eq, Rf] using hgf
  have hxRe := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Re hge').1
  have hyRe := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Re hge').2
  have hxRf := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Rf hgf').1
  have hyRf := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Rf hgf').2
  have hgQe : g ∈ Qe.edgeSet := by
    let he : s(e.1.out.1, e.1.out.2) ∈ Qe.edgeSet := by
      simpa [Qe, ze, Sym2.mk, e.1.out_eq] using
        E.blueSegmentTransition_mem_path
          hbudget hrecords B hB fallback e
    exact E.predecessorArc_edgeSet_subset hbudget ze _ _
      (by simpa [Re, Qe, blueSegmentTransitionPath, ze, he] using hge)
  have hgQf : g ∈ Qf.edgeSet := by
    let hf : s(f.1.out.1, f.1.out.2) ∈ Qf.edgeSet := by
      simpa [Qf, zf, Sym2.mk, f.1.out_eq] using
        E.blueSegmentTransition_mem_path
          hbudget hrecords B hB fallback f
    exact E.predecessorArc_edgeSet_subset hbudget zf _ _
      (by simpa [Rf, Qf, blueSegmentTransitionPath, zf, hf] using hgf)
  have hxQe :
      g.out.1 ∈ Qe.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Qe (by
      rw [Sym2.mk, g.out_eq]
      exact hgQe)).1
  have hyQe :
      g.out.2 ∈ Qe.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Qe (by
      rw [Sym2.mk, g.out_eq]
      exact hgQe)).2
  have hxQf :
      g.out.1 ∈ Qf.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Qf (by
      rw [Sym2.mk, g.out_eq]
      exact hgQf)).1
  have hz : ze = zf :=
    E.localBlueIndex_unique hbudget
      (by simpa [Qe] using hxQe) (by simpa [Qf] using hxQf)
  have hz' :
      E.blueSegmentTransitionIndex hbudget hrecords B hB fallback e =
        E.blueSegmentTransitionIndex hbudget hrecords B hB fallback f := by
    simpa [ze, zf] using hz
  have hpairE :
      E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback e =
        s(Re.source, Re.target) := by
    simpa [Re] using
      (E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback e).symm
  have hpairF :
      E.blueSegmentTransitionEndpoints
          hbudget hrecords B hB fallback f =
        s(Rf.source, Rf.target) := by
    simpa [Rf] using
      (E.blueSegmentTransitionPath_endpoints
        hbudget hrecords B hB fallback f).symm
  have haPair :
      Re.source ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
    rw [hpairE]
    simp
  have hbPair :
      Re.target ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback e := by
    rw [hpairE]
    simp
  have hcPair :
      Rf.source ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback f := by
    rw [hpairF]
    simp
  have hdPair :
      Rf.target ∈ E.blueSegmentTransitionEndpoints
        hbudget hrecords B hB fallback f := by
    rw [hpairF]
    simp
  have haData :=
    E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e haPair
  have hbData :=
    E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback e hbPair
  have hcDataRaw :=
    E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hcPair
  have hdDataRaw :=
    E.mem_blueSegmentTransitionEndpoints
      hbudget hrecords B hB fallback f hdPair
  rw [← hz'] at hcDataRaw hdDataRaw
  have hcQe : Rf.source ∈ Qe.vertexSet := by
    simpa [Qe, ze] using hcDataRaw.1
  have hdQe : Rf.target ∈ Qe.vertexSet := by
    simpa [Qe, ze] using hdDataRaw.1
  have haQe : Re.source ∈ Qe.vertexSet := by
    simpa [Qe, ze] using haData.1
  have hbQe : Re.target ∈ Qe.vertexSet := by
    simpa [Qe, ze] using hbData.1
  have hboundsEx :=
    E.blueSegmentTransitionPath_vertexIndex_bounds
      hbudget hrecords B hB fallback e hxRe
  have hboundsEy :=
    E.blueSegmentTransitionPath_vertexIndex_bounds
      hbudget hrecords B hB fallback e hyRe
  have hboundsFxRaw :=
    E.blueSegmentTransitionPath_vertexIndex_bounds
      hbudget hrecords B hB fallback f hxRf
  have hboundsFyRaw :=
    E.blueSegmentTransitionPath_vertexIndex_bounds
      hbudget hrecords B hB fallback f hyRf
  dsimp only at hboundsFxRaw hboundsFyRaw
  rw [← hz'] at hboundsFxRaw hboundsFyRaw
  have hboundsFx :
      min (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target) ≤
          Qe.vertexIndex g.out.1 ∧
        Qe.vertexIndex g.out.1 ≤
          max (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target) := by
    simpa [Qe, Rf, ze] using hboundsFxRaw
  have hboundsFy :
      min (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target) ≤
          Qe.vertexIndex g.out.2 ∧
        Qe.vertexIndex g.out.2 ≤
          max (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target) := by
    simpa [Qe, Rf, ze] using hboundsFyRaw
  have hboundsEx' :
      min (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target) ≤
          Qe.vertexIndex g.out.1 ∧
        Qe.vertexIndex g.out.1 ≤
          max (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target) := by
    simpa [Qe, Re, ze] using hboundsEx
  have hboundsEy' :
      min (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target) ≤
          Qe.vertexIndex g.out.2 ∧
        Qe.vertexIndex g.out.2 ≤
          max (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target) := by
    simpa [Qe, Re, ze] using hboundsEy
  have hxyNe : g.out.1 ≠ g.out.2 := by
    have hadj : (E.assembledSupport hbudget).Adj g.out.1 g.out.2 := by
      have hgSupport :
          g ∈ (E.assembledSupport hbudget).edgeSet :=
        GraphPath.edgeSet_subset_edgeSet Re hge
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa [Sym2.mk, g.out_eq] using hgSupport
    exact hadj.ne
  have hidxNe :
      Qe.vertexIndex g.out.1 ≠ Qe.vertexIndex g.out.2 := by
    intro hidx
    exact hxyNe (GraphPath.eq_of_vertexIndex_eq Qe hxQe hyQe hidx)
  let kLo :=
    min (Qe.vertexIndex g.out.1) (Qe.vertexIndex g.out.2)
  let kHi :=
    max (Qe.vertexIndex g.out.1) (Qe.vertexIndex g.out.2)
  let eLo :=
    min (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target)
  let eHi :=
    max (Qe.vertexIndex Re.source) (Qe.vertexIndex Re.target)
  let fLo :=
    min (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target)
  let fHi :=
    max (Qe.vertexIndex Rf.source) (Qe.vertexIndex Rf.target)
  have hnoE :
      ∀ {v : V}, v ∈ Qe.vertexSet →
        v ∈ E.redCarrierVertices hbudget →
        eLo < Qe.vertexIndex v →
        Qe.vertexIndex v < eHi → False := by
    intro v hvQ hvCarrier hlow hhigh
    exact E.blueSegmentTransition_no_carrier_strict_between
      hbudget hrecords B hB fallback e
      (by simpa [Qe, ze] using hvQ) hvCarrier
      (by simpa [Qe, Re, ze, eLo] using hlow)
      (by simpa [Qe, Re, ze, eHi] using hhigh)
  have hnoF :
      ∀ {v : V}, v ∈ Qe.vertexSet →
        v ∈ E.redCarrierVertices hbudget →
        fLo < Qe.vertexIndex v →
        Qe.vertexIndex v < fHi → False := by
    intro v hvQ hvCarrier hlow hhigh
    have hvQf :
        v ∈
          (E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).2).vertexSet := by
      rw [← hz']
      simpa [Qe, ze] using hvQ
    have hlow' :
        min
            ((E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).2).vertexIndex Rf.source)
            ((E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).2).vertexIndex Rf.target) <
          (E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).2).vertexIndex v := by
      rw [← hz']
      exact hlow
    have hhigh' :
        (E.localBluePath
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).1
            (E.blueSegmentTransitionIndex
              hbudget hrecords B hB fallback f).2).vertexIndex v <
          max
            ((E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).2).vertexIndex Rf.source)
            ((E.localBluePath
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).1
              (E.blueSegmentTransitionIndex
                hbudget hrecords B hB fallback f).2).vertexIndex Rf.target) := by
      rw [← hz']
      exact hhigh
    exact E.blueSegmentTransition_no_carrier_strict_between
      hbudget hrecords B hB fallback f
      hvQf hvCarrier
      (by simpa [Rf] using hlow')
      (by simpa [Rf] using hhigh')
  have hkLt : kLo < kHi := by
    exact min_lt_max.mpr hidxNe
  have heLoK : eLo ≤ kLo := by
    exact le_min hboundsEx'.1 hboundsEy'.1
  have hkEHi : kHi ≤ eHi := by
    exact max_le hboundsEx'.2 hboundsEy'.2
  have hfLoK : fLo ≤ kLo := by
    exact le_min hboundsFx.1 hboundsFy.1
  have hkFHi : kHi ≤ fHi := by
    exact max_le hboundsFx.2 hboundsFy.2
  have heNonempty : eLo < eHi := heLoK.trans_lt (hkLt.trans_le hkEHi)
  have hfNonempty : fLo < fHi := hfLoK.trans_lt (hkLt.trans_le hkFHi)
  have hlowEq : eLo = fLo := by
    rcases le_total eLo fLo with hEF | hFE
    · have hfLoEHi : fLo < eHi :=
        hfLoK.trans_lt (hkLt.trans_le hkEHi)
      by_cases hEq : eLo = fLo
      · exact hEq
      · have hstrict : eLo < fLo := lt_of_le_of_ne hEF hEq
        by_cases hcd :
            Qe.vertexIndex Rf.source ≤ Qe.vertexIndex Rf.target
        · exact False.elim
            (hnoE hcQe hcDataRaw.2
              (by simpa [eLo, fLo, Nat.min_eq_left hcd] using hstrict)
              (by simpa [eHi, fLo, Nat.min_eq_left hcd] using hfLoEHi))
        · have hdc :
              Qe.vertexIndex Rf.target ≤ Qe.vertexIndex Rf.source :=
            Nat.le_of_lt (Nat.lt_of_not_ge hcd)
          exact False.elim
            (hnoE hdQe hdDataRaw.2
              (by simpa [eLo, fLo, Nat.min_eq_right hdc] using hstrict)
              (by simpa [eHi, fLo, Nat.min_eq_right hdc] using hfLoEHi))
    · have heLoFHi : eLo < fHi :=
        heLoK.trans_lt (hkLt.trans_le hkFHi)
      by_cases hEq : eLo = fLo
      · exact hEq
      · have hstrict : fLo < eLo := lt_of_le_of_ne hFE (Ne.symm hEq)
        by_cases hab :
            Qe.vertexIndex Re.source ≤ Qe.vertexIndex Re.target
        · exact False.elim
            (hnoF haQe haData.2
              (by simpa [eLo, fLo, Nat.min_eq_left hab] using hstrict)
              (by simpa [fHi, eLo, Nat.min_eq_left hab] using heLoFHi))
        · have hba :
              Qe.vertexIndex Re.target ≤ Qe.vertexIndex Re.source :=
            Nat.le_of_lt (Nat.lt_of_not_ge hab)
          exact False.elim
            (hnoF hbQe hbData.2
              (by simpa [eLo, fLo, Nat.min_eq_right hba] using hstrict)
              (by simpa [fHi, eLo, Nat.min_eq_right hba] using heLoFHi))
  have hhighEq : eHi = fHi := by
    rcases le_total eHi fHi with hEF | hFE
    · by_cases hEq : eHi = fHi
      · exact hEq
      · have hstrict : eHi < fHi := lt_of_le_of_ne hEF hEq
        by_cases hab :
            Qe.vertexIndex Re.source ≤ Qe.vertexIndex Re.target
        · exact False.elim
            (hnoF hbQe hbData.2
              (by
                simpa [eHi, fLo, Nat.max_eq_right hab, hlowEq] using
                  heNonempty)
              (by simpa [eHi, fHi, Nat.max_eq_right hab] using hstrict))
        · have hba :
              Qe.vertexIndex Re.target ≤ Qe.vertexIndex Re.source :=
            Nat.le_of_lt (Nat.lt_of_not_ge hab)
          exact False.elim
            (hnoF haQe haData.2
              (by
                simpa [eHi, fLo, Nat.max_eq_left hba, hlowEq] using
                  heNonempty)
              (by simpa [eHi, fHi, Nat.max_eq_left hba] using hstrict))
    · by_cases hEq : eHi = fHi
      · exact hEq
      · have hstrict : fHi < eHi := lt_of_le_of_ne hFE (Ne.symm hEq)
        by_cases hcd :
            Qe.vertexIndex Rf.source ≤ Qe.vertexIndex Rf.target
        · exact False.elim
            (hnoE hdQe hdDataRaw.2
              (by
                simpa [fHi, eLo, Nat.max_eq_right hcd, hlowEq] using
                  hfNonempty)
              (by simpa [eHi, fHi, Nat.max_eq_right hcd] using hstrict))
        · have hdc :
              Qe.vertexIndex Rf.target ≤ Qe.vertexIndex Rf.source :=
            Nat.le_of_lt (Nat.lt_of_not_ge hcd)
          exact False.elim
            (hnoE hcQe hcDataRaw.2
              (by
                simpa [fHi, eLo, Nat.max_eq_left hdc, hlowEq] using
                  hfNonempty)
              (by simpa [eHi, fHi, Nat.max_eq_left hdc] using hstrict))
  apply hef
  apply E.blueSegmentTransitionEndpoints_injective
    hbudget hrecords B hB fallback
  rw [hpairE, hpairF, Sym2.eq_iff]
  by_cases hab : Qe.vertexIndex Re.source ≤ Qe.vertexIndex Re.target
  · by_cases hcd : Qe.vertexIndex Rf.source ≤ Qe.vertexIndex Rf.target
    · left
      constructor
      · exact GraphPath.eq_of_vertexIndex_eq Qe haQe hcQe (by
          simpa [eLo, fLo, Nat.min_eq_left hab, Nat.min_eq_left hcd] using
            hlowEq)
      · exact GraphPath.eq_of_vertexIndex_eq Qe hbQe hdQe (by
          simpa [eHi, fHi, Nat.max_eq_right hab, Nat.max_eq_right hcd] using
            hhighEq)
    · have hdc : Qe.vertexIndex Rf.target ≤ Qe.vertexIndex Rf.source :=
        Nat.le_of_lt (Nat.lt_of_not_ge hcd)
      right
      constructor
      · exact GraphPath.eq_of_vertexIndex_eq Qe haQe hdQe (by
          simpa [eLo, fLo, Nat.min_eq_left hab, Nat.min_eq_right hdc] using
            hlowEq)
      · exact GraphPath.eq_of_vertexIndex_eq Qe hbQe hcQe (by
          simpa [eHi, fHi, Nat.max_eq_right hab, Nat.max_eq_left hdc] using
            hhighEq)
  · have hba : Qe.vertexIndex Re.target ≤ Qe.vertexIndex Re.source :=
      Nat.le_of_lt (Nat.lt_of_not_ge hab)
    by_cases hcd : Qe.vertexIndex Rf.source ≤ Qe.vertexIndex Rf.target
    · right
      constructor
      · exact GraphPath.eq_of_vertexIndex_eq Qe haQe hdQe (by
          simpa [eHi, fHi, Nat.max_eq_left hba, Nat.max_eq_right hcd] using
            hhighEq)
      · exact GraphPath.eq_of_vertexIndex_eq Qe hbQe hcQe (by
          simpa [eLo, fLo, Nat.min_eq_right hba, Nat.min_eq_left hcd] using
            hlowEq)
    · have hdc : Qe.vertexIndex Rf.target ≤ Qe.vertexIndex Rf.source :=
        Nat.le_of_lt (Nat.lt_of_not_ge hcd)
      left
      constructor
      · exact GraphPath.eq_of_vertexIndex_eq Qe haQe hcQe (by
          simpa [eHi, fHi, Nat.max_eq_left hba, Nat.max_eq_left hdc] using
            hhighEq)
      · exact GraphPath.eq_of_vertexIndex_eq Qe hbQe hdQe (by
          simpa [eLo, fLo, Nat.min_eq_right hba, Nat.min_eq_right hdc] using
            hlowEq)

/-- A usable quotient connection is either a deterministically retained
nonblue edge or a complete surviving blue transition. -/
abbrev SegmentBoundaryConnection
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :=
  Sym2 V ⊕ E.BlueSegmentTransition hbudget hrecords B hB fallback

/-- The finite set whose cardinality is
`usableSegmentBoundaryCount`. -/
noncomputable def usableSegmentBoundaryConnections
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) :
    Finset (E.SegmentBoundaryConnection
      hbudget hrecords B hB fallback) := by
  classical
  exact
    (E.nonBlueSegmentBoundaryEdges
        hbudget hrecords B hB fallback S).image Sum.inl ∪
      ((E.blueSegmentBoundaryTransitions
          hbudget hrecords B hB fallback S).filter fun e =>
        SegmentLinkFamily.Survives
          E hbudget hrecords B hB fallback outcome e).image Sum.inr

theorem usableSegmentBoundaryConnections_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget)) :
    (E.usableSegmentBoundaryConnections
        hbudget hrecords B hB fallback S outcome).card =
      E.usableSegmentBoundaryCount
        hbudget hrecords B hB fallback S outcome := by
  classical
  rw [usableSegmentBoundaryConnections, usableSegmentBoundaryCount,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
    rfl
  · rw [Finset.disjoint_left]
    intro c hcLeft hcRight
    rcases Finset.mem_image.mp hcLeft with ⟨e, _he, rfl⟩
    rcases Finset.mem_image.mp hcRight with ⟨f, _hf, hEq⟩
    simp at hEq

/-- All usable connections incident with one physical segment. -/
noncomputable def segmentConnectionsIncident
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Finset (E.SegmentBoundaryConnection
      hbudget hrecords B hB fallback) := by
  classical
  exact
    (E.nonBlueEdgesIncidentSegment
        hbudget hrecords B hB fallback i).image Sum.inl ∪
      (E.blueTransitionsIncidentSegment
        hbudget hrecords B hB fallback i).image Sum.inr

/-- The local congestion bound: at most `4A` nonblue connections and `2A`
blue connections are incident with a segment. -/
theorem segmentConnectionsIncident_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.segmentConnectionsIncident
      hbudget hrecords B hB fallback i).card ≤
      6 * (E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2) := by
  classical
  let A :=
    E.finalState.records.length * (2 * B) +
      2 * E.finalState.records.length + 2
  calc
    (E.segmentConnectionsIncident
        hbudget hrecords B hB fallback i).card ≤
        ((E.nonBlueEdgesIncidentSegment
          hbudget hrecords B hB fallback i).image Sum.inl).card +
        ((E.blueTransitionsIncidentSegment
          hbudget hrecords B hB fallback i).image Sum.inr).card := by
      simpa [segmentConnectionsIncident] using
        Finset.card_union_le
          ((E.nonBlueEdgesIncidentSegment
              hbudget hrecords B hB fallback i).image Sum.inl)
          ((E.blueTransitionsIncidentSegment
              hbudget hrecords B hB fallback i).image Sum.inr)
    _ =
        (E.nonBlueEdgesIncidentSegment
          hbudget hrecords B hB fallback i).card +
          (E.blueTransitionsIncidentSegment
            hbudget hrecords B hB fallback i).card := by
      rw [Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective]
    _ ≤ 4 * A + 2 * A :=
      Nat.add_le_add
        (E.nonBlueEdgesIncidentSegment_card_le
          hbudget hrecords B hB fallback i)
        (E.blueTransitionsIncidentSegment_card_le
          hbudget hrecords B hB fallback i)
    _ = 6 * (E.finalState.records.length * (2 * B) +
        2 * E.finalState.records.length + 2) := by
      simp [A]
      ring

/-- Usable connections charged to segments which are internally split by the
physical cut. -/
noncomputable def splitIncidentUsableConnections
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (X Y : Finset V) :
    Finset (E.SegmentBoundaryConnection
      hbudget hrecords B hB fallback) := by
  classical
  exact
    (E.usableSegmentBoundaryConnections
        hbudget hrecords B hB fallback S outcome).filter fun c =>
      match c with
      | Sum.inl e =>
          E.segmentOwner hbudget hrecords B hB fallback e.out.1 ∈
              E.splitSegments hbudget hrecords B hB X Y ∨
            E.segmentOwner hbudget hrecords B hB fallback e.out.2 ∈
              E.splitSegments hbudget hrecords B hB X Y
      | Sum.inr e =>
          let Q := E.blueSegmentTransitionPath
            hbudget hrecords B hB fallback e
          E.segmentOwner hbudget hrecords B hB fallback Q.source ∈
              E.splitSegments hbudget hrecords B hB X Y ∨
            E.segmentOwner hbudget hrecords B hB fallback Q.target ∈
              E.splitSegments hbudget hrecords B hB X Y

theorem splitIncidentUsableConnections_subset_biUnion
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (X Y : Finset V) :
    E.splitIncidentUsableConnections
        hbudget hrecords B hB fallback S outcome X Y ⊆
      (E.splitSegments hbudget hrecords B hB X Y).biUnion fun i =>
        E.segmentConnectionsIncident hbudget hrecords B hB fallback i := by
  classical
  intro c hc
  rw [splitIncidentUsableConnections] at hc
  have hcBase := (Finset.mem_filter.mp hc).1
  have hcData := (Finset.mem_filter.mp hc).2
  rcases c with e | e
  · have heNonBlue :
        e ∈ E.nonBlueSegmentBoundaryEdges
          hbudget hrecords B hB fallback S := by
      simpa [usableSegmentBoundaryConnections] using hcBase
    have heCross :
        e ∈ E.segmentCrossingEdges
          hbudget hrecords B hB fallback :=
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp heNonBlue).1).1
    rcases hcData with hleft | hright
    · apply Finset.mem_biUnion.mpr
      refine ⟨_, hleft, ?_⟩
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr
          ⟨heCross,
            (Finset.mem_filter.mp heNonBlue).2,
            Or.inl rfl⟩, rfl⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨_, hright, ?_⟩
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr
          ⟨heCross,
            (Finset.mem_filter.mp heNonBlue).2,
            Or.inr rfl⟩, rfl⟩
  · rcases hcData with hsource | htarget
    · apply Finset.mem_biUnion.mpr
      refine ⟨_, hsource, ?_⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨e, ?_, rfl⟩
      simpa [blueTransitionsIncidentSegment]
    · apply Finset.mem_biUnion.mpr
      refine ⟨_, htarget, ?_⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨e, ?_, rfl⟩
      simpa [blueTransitionsIncidentSegment]

/-- Total congestion charged to all split segments. -/
theorem splitIncidentUsableConnections_card_le
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (X Y : Finset V) :
    (E.splitIncidentUsableConnections
      hbudget hrecords B hB fallback S outcome X Y).card ≤
      (E.splitSegments hbudget hrecords B hB X Y).card *
        (6 * (E.finalState.records.length * (2 * B) +
          2 * E.finalState.records.length + 2)) := by
  classical
  calc
    (E.splitIncidentUsableConnections
        hbudget hrecords B hB fallback S outcome X Y).card ≤
        ((E.splitSegments hbudget hrecords B hB X Y).biUnion fun i =>
          E.segmentConnectionsIncident
            hbudget hrecords B hB fallback i).card :=
      Finset.card_le_card
        (E.splitIncidentUsableConnections_subset_biUnion
          hbudget hrecords B hB fallback S outcome X Y)
    _ ≤ (E.splitSegments hbudget hrecords B hB X Y).card *
          (6 * (E.finalState.records.length * (2 * B) +
            2 * E.finalState.records.length + 2)) := by
      apply Finset.card_biUnion_le_card_mul
      intro i hi
      exact E.segmentConnectionsIncident_card_le
        hbudget hrecords B hB fallback i

/-- Usable connections whose two endpoint segments are not internally split
by the physical cut. -/
noncomputable def unsplitUsableConnections
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (X Y : Finset V) :
    Finset (E.SegmentBoundaryConnection
      hbudget hrecords B hB fallback) :=
  E.usableSegmentBoundaryConnections
      hbudget hrecords B hB fallback S outcome \
    E.splitIncidentUsableConnections
      hbudget hrecords B hB fallback S outcome X Y

theorem usableConnections_card_le_split_add_unsplit
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (X Y : Finset V) :
    (E.usableSegmentBoundaryConnections
        hbudget hrecords B hB fallback S outcome).card ≤
      (E.splitIncidentUsableConnections
        hbudget hrecords B hB fallback S outcome X Y).card +
      (E.unsplitUsableConnections
        hbudget hrecords B hB fallback S outcome X Y).card := by
  classical
  let U :=
    E.usableSegmentBoundaryConnections
      hbudget hrecords B hB fallback S outcome
  let D :=
    E.splitIncidentUsableConnections
      hbudget hrecords B hB fallback S outcome X Y
  have hD : D ⊆ U := by
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  have hpartition : U = D ∪ (U \ D) := by
    ext c
    by_cases hc : c ∈ D
    · simp [hc, hD hc]
    · simp [hc]
  calc
    U.card = (D ∪ (U \ D)).card := congrArg Finset.card hpartition
    _ ≤ D.card + (U \ D).card := Finset.card_union_le _ _
    _ = (E.splitIncidentUsableConnections
          hbudget hrecords B hB fallback S outcome X Y).card +
        (E.unsplitUsableConnections
          hbudget hrecords B hB fallback S outcome X Y).card := by
      rfl

/-- Every unsplit usable quotient connection contains a physical edge of the
corresponding cut in the thinned graph. -/
theorem exists_unsplitUsableConnection_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (c : {c : E.SegmentBoundaryConnection
        hbudget hrecords B hB fallback //
      c ∈ E.unsplitUsableConnections
        hbudget hrecords B hB fallback
          (E.physicalSegmentSide hbudget hrecords B hB X)
          outcome X Y}) :
    ∃ g : Sym2 V,
      g ∈ Section44.edgeBoundary
          ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y ∧
        match c.1 with
        | Sum.inl e => g = e
        | Sum.inr e =>
            g ∈ (E.blueSegmentTransitionPath
              hbudget hrecords B hB fallback e).edgeSet := by
  classical
  let S := E.physicalSegmentSide hbudget hrecords B hB X
  have hcDiff :
      c.1 ∈ E.usableSegmentBoundaryConnections
          hbudget hrecords B hB fallback S outcome ∧
        c.1 ∉ E.splitIncidentUsableConnections
          hbudget hrecords B hB fallback S outcome X Y := by
    simpa [unsplitUsableConnections, S] using Finset.mem_sdiff.mp c.2
  rcases c with ⟨c, hc⟩
  dsimp only at hcDiff
  rcases c with e | e
  · have heUse :
        e ∈ E.nonBlueSegmentBoundaryEdges
          hbudget hrecords B hB fallback S := by
      simpa [usableSegmentBoundaryConnections] using hcDiff.1
    have heBoundary :
        e ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S :=
      (Finset.mem_filter.mp heUse).1
    have heNotBlue : e ∉ E.blueSupport.edgeSet :=
      (Finset.mem_filter.mp heUse).2
    have heCrossOwner := (Finset.mem_filter.mp heBoundary).2
    have heCrossing := (Finset.mem_filter.mp heBoundary).1
    have heSupport :
        e ∈ (E.assembledSupport hbudget).edgeSet :=
      _root_.SimpleGraph.mem_edgeFinset.mp
        (Finset.mem_filter.mp heCrossing).1
    have hcarriers :=
      E.nonBlue_assembled_edge_endpoints_redCarrier
        hbudget heSupport heNotBlue
    have hleftSegment :
        e.out.1 ∈
          (E.exactRailSegmentPathAt hbudget hrecords B hB
            (E.segmentOwner hbudget hrecords B hB fallback e.out.1)).vertexSet :=
      E.redCarrier_mem_segmentOwner
        hbudget hrecords B hB fallback hcarriers.1.choose_spec
    have hrightSegment :
        e.out.2 ∈
          (E.exactRailSegmentPathAt hbudget hrecords B hB
            (E.segmentOwner hbudget hrecords B hB fallback e.out.2)).vertexSet :=
      E.redCarrier_mem_segmentOwner
        hbudget hrecords B hB fallback hcarriers.2.choose_spec
    have hnotSplit :
        E.segmentOwner hbudget hrecords B hB fallback e.out.1 ∉
            E.splitSegments hbudget hrecords B hB X Y ∧
          E.segmentOwner hbudget hrecords B hB fallback e.out.2 ∉
            E.splitSegments hbudget hrecords B hB X Y := by
      constructor
      · intro hs
        apply hcDiff.2
        rw [splitIncidentUsableConnections]
        exact Finset.mem_filter.mpr ⟨hcDiff.1, Or.inl hs⟩
      · intro hs
        apply hcDiff.2
        rw [splitIncidentUsableConnections]
        exact Finset.mem_filter.mpr ⟨hcDiff.1, Or.inr hs⟩
    have heThinned :
        e ∈ ((E.blueThinningInput hbudget).thinnedGraph outcome).edgeSet := by
      let named : (E.assembledSupport hbudget).edgeSet := ⟨e, heSupport⟩
      apply (E.blueThinningInput hbudget).edge_mem_thinned_of_not_blue
        named
      · change
          named ∉ edgesOfSubgraph
            (E.assembledSupport hbudget) E.blueSupport le_sup_right
        rw [mem_edgesOfSubgraph]
        exact heNotBlue
    rcases heCrossOwner with hforward | hbackward
    · have hleftX : e.out.1 ∈ X :=
        (E.mem_physicalSegmentSide
          hbudget hrecords B hB X _).mp hforward.1 hleftSegment
      have hrightY : e.out.2 ∈ Y :=
        E.segment_subset_right_of_not_side_of_not_split
          hbudget hrecords B hB _ hforward.2 hnotSplit.2 hrightSegment
      refine ⟨e, ?_, rfl⟩
      exact (Section44.mem_edgeBoundary
        (G := (E.blueThinningInput hbudget).thinnedGraph outcome)
        X Y e).2
          ⟨heThinned, e.out.1, hleftX, e.out.2, hrightY, e.out_eq.symm⟩
    · have hrightX : e.out.2 ∈ X :=
        (E.mem_physicalSegmentSide
          hbudget hrecords B hB X _).mp hbackward.1 hrightSegment
      have hleftY : e.out.1 ∈ Y :=
        E.segment_subset_right_of_not_side_of_not_split
          hbudget hrecords B hB _ hbackward.2 hnotSplit.1 hleftSegment
      refine ⟨e, ?_, rfl⟩
      exact (Section44.mem_edgeBoundary
        (G := (E.blueThinningInput hbudget).thinnedGraph outcome)
        X Y e).2
          ⟨heThinned, e.out.2, hrightX, e.out.1, hleftY, by
            rw [Sym2.eq_swap]
            exact e.out_eq.symm⟩
  · have heUse :
        e ∈ (E.blueSegmentBoundaryTransitions
            hbudget hrecords B hB fallback S).filter fun e =>
          SegmentLinkFamily.Survives
            E hbudget hrecords B hB fallback outcome e := by
      simpa [usableSegmentBoundaryConnections] using hcDiff.1
    have heBoundary :
        e.1 ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp heUse).1).2
    have hsurvives :
        SegmentLinkFamily.Survives
          E hbudget hrecords B hB fallback outcome e :=
      (Finset.mem_filter.mp heUse).2
    let Q :=
      E.blueSegmentTransitionPath hbudget hrecords B hB fallback e
    have hends :=
      E.blueSegmentTransitionPath_endpoints_mem_ownerSegments
        hbudget hrecords B hB fallback e
    have hcrossRep := (Finset.mem_filter.mp heBoundary).2
    have hcross :
        (E.segmentOwner hbudget hrecords B hB fallback Q.source ∈ S ∧
            E.segmentOwner hbudget hrecords B hB fallback Q.target ∉ S) ∨
          (E.segmentOwner hbudget hrecords B hB fallback Q.target ∈ S ∧
            E.segmentOwner hbudget hrecords B hB fallback Q.source ∉ S) := by
      rw [E.blueSegmentTransitionPath_source_owner
        hbudget hrecords B hB fallback e,
        E.blueSegmentTransitionPath_target_owner
          hbudget hrecords B hB fallback e]
      exact hcrossRep
    have hnotSplit :
        E.segmentOwner hbudget hrecords B hB fallback Q.source ∉
            E.splitSegments hbudget hrecords B hB X Y ∧
          E.segmentOwner hbudget hrecords B hB fallback Q.target ∉
            E.splitSegments hbudget hrecords B hB X Y := by
      constructor
      · intro hs
        apply hcDiff.2
        rw [splitIncidentUsableConnections]
        exact Finset.mem_filter.mpr ⟨hcDiff.1, Or.inl hs⟩
      · intro hs
        apply hcDiff.2
        rw [splitIncidentUsableConnections]
        exact Finset.mem_filter.mpr ⟨hcDiff.1, Or.inr hs⟩
    let Qthin :=
      Q.transfer
        ((E.blueThinningInput hbudget).thinnedGraph outcome)
        (by
          intro g hg
          exact hsurvives g (List.mem_toFinset.mpr hg))
    rcases hcross with hforward | hbackward
    · have hsourceX : Q.source ∈ X :=
        (E.mem_physicalSegmentSide
          hbudget hrecords B hB X _).mp hforward.1 hends.1
      have htargetY : Q.target ∈ Y :=
        E.segment_subset_right_of_not_side_of_not_split
          hbudget hrecords B hB _ hforward.2 hnotSplit.2 hends.2
      obtain ⟨g, hgQ, hgCut⟩ :=
        path_exists_edgeBoundary_of_endpoints_opposite
          Qthin hcover hdisjoint
          (by simpa [Qthin] using hsourceX)
          (by simpa [Qthin] using htargetY)
      exact ⟨g, hgCut, by simpa [Qthin] using hgQ⟩
    · have htargetX : Q.target ∈ X :=
        (E.mem_physicalSegmentSide
          hbudget hrecords B hB X _).mp hbackward.1 hends.2
      have hsourceY : Q.source ∈ Y :=
        E.segment_subset_right_of_not_side_of_not_split
          hbudget hrecords B hB _ hbackward.2 hnotSplit.1 hends.1
      obtain ⟨g, hgQ, hgCut⟩ :=
        path_exists_edgeBoundary_of_endpoints_opposite
          Qthin.reverse hcover hdisjoint
          (by simpa [Qthin] using htargetX)
          (by simpa [Qthin] using hsourceY)
      exact ⟨g, hgCut, by simpa [Qthin] using hgQ⟩

/-- Canonical physical cut edge charged by an unsplit usable connection. -/
noncomputable def unsplitUsableConnectionEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (c : {c : E.SegmentBoundaryConnection
        hbudget hrecords B hB fallback //
      c ∈ E.unsplitUsableConnections
        hbudget hrecords B hB fallback
          (E.physicalSegmentSide hbudget hrecords B hB X)
          outcome X Y}) :
    Sym2 V :=
  Classical.choose
    (E.exists_unsplitUsableConnection_edgeBoundary
      hbudget hrecords B hB fallback outcome hcover hdisjoint c)

theorem unsplitUsableConnectionEdge_mem_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (c : {c : E.SegmentBoundaryConnection
        hbudget hrecords B hB fallback //
      c ∈ E.unsplitUsableConnections
        hbudget hrecords B hB fallback
          (E.physicalSegmentSide hbudget hrecords B hB X)
          outcome X Y}) :
    E.unsplitUsableConnectionEdge
        hbudget hrecords B hB fallback outcome hcover hdisjoint c ∈
      Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y :=
  (Classical.choose_spec
    (E.exists_unsplitUsableConnection_edgeBoundary
      hbudget hrecords B hB fallback outcome hcover hdisjoint c)).1

theorem unsplitUsableConnectionEdge_spec
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (c : {c : E.SegmentBoundaryConnection
        hbudget hrecords B hB fallback //
      c ∈ E.unsplitUsableConnections
        hbudget hrecords B hB fallback
          (E.physicalSegmentSide hbudget hrecords B hB X)
          outcome X Y}) :
    match c.1 with
    | Sum.inl e =>
        E.unsplitUsableConnectionEdge
          hbudget hrecords B hB fallback outcome hcover hdisjoint c = e
    | Sum.inr e =>
        E.unsplitUsableConnectionEdge
            hbudget hrecords B hB fallback outcome hcover hdisjoint c ∈
          (E.blueSegmentTransitionPath
            hbudget hrecords B hB fallback e).edgeSet :=
  (Classical.choose_spec
    (E.exists_unsplitUsableConnection_edgeBoundary
      hbudget hrecords B hB fallback outcome hcover hdisjoint c)).2

theorem unsplitUsableConnectionEdge_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    Function.Injective
      (E.unsplitUsableConnectionEdge
        hbudget hrecords B hB fallback outcome hcover hdisjoint) := by
  classical
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hedge
  apply Subtype.ext
  rcases c with e | e
  · rcases d with f | f
    · apply congrArg Sum.inl
      have he :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inl e, hc⟩
      have hf :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inl f, hd⟩
      exact he.symm.trans (hedge.trans hf)
    · exfalso
      have he :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inl e, hc⟩
      have hf :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inr f, hd⟩
      have heBlue : e ∈ E.blueSupport.edgeSet := by
        apply E.blueSegmentTransitionPath_edgeSet_subset_blue
          hbudget hrecords B hB fallback f e
        rw [← he, hedge]
        exact hf
      have heDiff :=
        Finset.mem_sdiff.mp (by
          simpa [unsplitUsableConnections] using hc)
      have heUse :
          e ∈ E.nonBlueSegmentBoundaryEdges
            hbudget hrecords B hB fallback
              (E.physicalSegmentSide hbudget hrecords B hB X) := by
        simpa [usableSegmentBoundaryConnections] using heDiff.1
      exact (Finset.mem_filter.mp heUse).2 heBlue
  · rcases d with f | f
    · exfalso
      have he :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inr e, hc⟩
      have hf :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inl f, hd⟩
      have hfBlue : f ∈ E.blueSupport.edgeSet := by
        apply E.blueSegmentTransitionPath_edgeSet_subset_blue
          hbudget hrecords B hB fallback e f
        rw [← hf, ← hedge]
        exact he
      have hfDiff :=
        Finset.mem_sdiff.mp (by
          simpa [unsplitUsableConnections] using hd)
      have hfUse :
          f ∈ E.nonBlueSegmentBoundaryEdges
            hbudget hrecords B hB fallback
              (E.physicalSegmentSide hbudget hrecords B hB X) := by
        simpa [usableSegmentBoundaryConnections] using hfDiff.1
      exact (Finset.mem_filter.mp hfUse).2 hfBlue
    · apply congrArg Sum.inr
      by_contra hef
      have he :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inr e, hc⟩
      have hf :=
        E.unsplitUsableConnectionEdge_spec
          hbudget hrecords B hB fallback outcome hcover hdisjoint
            ⟨Sum.inr f, hd⟩
      have hdisj :=
        E.blueSegmentTransitionPath_edgeDisjoint_of_ne
          hbudget hrecords B hB fallback e f hef
      exact Finset.disjoint_left.mp hdisj he (by
        rw [hedge]
        exact hf)

/-- Unsplit usable connections inject into the physical cut. -/
theorem unsplitUsableConnections_card_le_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count * (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    (E.unsplitUsableConnections
      hbudget hrecords B hB fallback
        (E.physicalSegmentSide hbudget hrecords B hB X)
        outcome X Y).card ≤
      (Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card := by
  classical
  let f :
      {c : E.SegmentBoundaryConnection hbudget hrecords B hB fallback //
        c ∈ E.unsplitUsableConnections
          hbudget hrecords B hB fallback
            (E.physicalSegmentSide hbudget hrecords B hB X)
            outcome X Y} →
      {g : Sym2 V //
        g ∈ Section44.edgeBoundary
          ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y} :=
    fun c =>
      ⟨E.unsplitUsableConnectionEdge
          hbudget hrecords B hB fallback outcome hcover hdisjoint c,
        E.unsplitUsableConnectionEdge_mem_boundary
          hbudget hrecords B hB fallback outcome hcover hdisjoint c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    exact E.unsplitUsableConnectionEdge_injective
      hbudget hrecords B hB fallback outcome hcover hdisjoint
      (congrArg Subtype.val hcd)
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Expanding the contracted Claim 5.3 conclusion through the physical red
segments.  Split segments and connections incident with them cost `6A` per
physical cut edge; all remaining usable connections inject into the cut. -/
theorem thinnedGraph_initialTerminals_scaledWellLinked_of_surviving
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (den : ℕ)
    (hsurviving :
      E.SurvivingSegmentWellLinked
        hbudget hrecords B hB fallback outcome den) :
    ScaledWellLinked
      ((E.blueThinningInput hbudget).thinnedGraph outcome)
      (P.left P.firstIndex) 1
      (den *
          (6 * (E.finalState.records.length * (2 * B) +
            2 * E.finalState.records.length + 2) + 1) + 1) := by
  classical
  refine ⟨by omega, by omega, ?_⟩
  intro X Y hcover hdisjoint
  let S := E.physicalSegmentSide hbudget hrecords B hB X
  let D := E.splitSegments hbudget hrecords B hB X Y
  let C :=
    (Section44.edgeBoundary
      ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card
  let A :=
    E.finalState.records.length * (2 * B) +
      2 * E.finalState.records.length + 2
  let U :=
    E.usableSegmentBoundaryConnections
      hbudget hrecords B hB fallback S outcome
  let Bad :=
    E.splitIncidentUsableConnections
      hbudget hrecords B hB fallback S outcome X Y
  let Good :=
    E.unsplitUsableConnections
      hbudget hrecords B hB fallback S outcome X Y
  have hsplit : D.card ≤ C := by
    simpa [D, C] using
      E.splitSegments_card_le_edgeBoundary
        hbudget hrecords B hB outcome hcover
  have hbad : Bad.card ≤ D.card * (6 * A) := by
    simpa [Bad, D, A] using
      E.splitIncidentUsableConnections_card_le
        hbudget hrecords B hB fallback S outcome X Y
  have hgood : Good.card ≤ C := by
    simpa [Good, S, C] using
      E.unsplitUsableConnections_card_le_edgeBoundary
        hbudget hrecords B hB fallback outcome hcover hdisjoint
  have husableSplit : U.card ≤ Bad.card + Good.card := by
    simpa [U, Bad, Good] using
      E.usableConnections_card_le_split_add_unsplit
        hbudget hrecords B hB fallback S outcome X Y
  have husable : U.card ≤ (6 * A + 1) * C := by
    calc
      U.card ≤ Bad.card + Good.card := husableSplit
      _ ≤ D.card * (6 * A) + C := Nat.add_le_add hbad hgood
      _ ≤ C * (6 * A) + C :=
        Nat.add_le_add_right (Nat.mul_le_mul_right (6 * A) hsplit) C
      _ = (6 * A + 1) * C := by ring
  have husableCount :
      E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome ≤
        (6 * A + 1) * C := by
    rw [← E.usableSegmentBoundaryConnections_card
      hbudget hrecords B hB fallback S outcome]
    exact husable
  have hsegment :=
    hsurviving S
  have hterminal :=
    E.terminal_min_le_segment_min_add_split
      hbudget hrecords B hB fallback hcover hdisjoint
  calc
    1 * min (X ∩ P.left P.firstIndex).card
          (Y ∩ P.left P.firstIndex).card =
        min (X ∩ P.left P.firstIndex).card
          (Y ∩ P.left P.firstIndex).card := by simp
    _ ≤
        min
            (S ∩ E.initialTerminalSegments
              hbudget hrecords B hB fallback).card
            (Sᶜ ∩ E.initialTerminalSegments
              hbudget hrecords B hB fallback).card +
          D.card := by
      simpa [S, D] using hterminal
    _ ≤ den *
          E.usableSegmentBoundaryCount
            hbudget hrecords B hB fallback S outcome + D.card :=
      Nat.add_le_add_right hsegment D.card
    _ ≤ den * ((6 * A + 1) * C) + C :=
      Nat.add_le_add
        (Nat.mul_le_mul_left den husableCount) hsplit
    _ =
        (den *
            (6 * (E.finalState.records.length * (2 * B) +
              2 * E.finalState.records.length + 2) + 1) + 1) *
          (Section44.edgeBoundary
            ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card := by
      simp [A, C]
      ring

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
