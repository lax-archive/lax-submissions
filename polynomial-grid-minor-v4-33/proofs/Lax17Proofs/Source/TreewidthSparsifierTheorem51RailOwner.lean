import Lax17Proofs.Source.TreewidthSparsifierTheorem51Support
import Lax17Proofs.Source.TreewidthSparsifierKarger

namespace Lax17Proofs

universe u v w

/-!
# The red-rail quotient for Theorem 5.1

The proof in Step 2 of Chekuri--Chuzhoy partitions every red rail into short
segments because it subsequently lifts a *routing* from the contracted graph.
For the semantic theorem needed here it is enough to lift cut inequalities.
We may therefore contract each whole red rail.  A physical cut that splits
many rails is charged directly to their pairwise edge-disjoint red paths; if
few rails are split, only a logarithmic-degree error is lost when a quotient
cut is lifted.

This file constructs the canonical rail label of every red vertex.  Blue-only
degree-two intervals are assigned to the label at the source of their blue
path.  The resulting finite edge-indexed quotient has vertex type `Fin h`;
every non-loop quotient edge is represented by an actual blue-support edge.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- The red path carrying abstract label `x` in record `j`. -/
noncomputable def localRedPath
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    GraphPath (E.recordAt j).layer.localGraph :=
  let R := E.recordAt j
  R.layer.red.path (R.layer.red.indexOfSource (R.label x))

@[simp] theorem localRedPath_source
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localRedPath j x).source = ((E.recordAt j).label x).1 := by
  exact congrArg Subtype.val
    ((E.recordAt j).layer.red.source_indexOfSource
      ((E.recordAt j).label x))

@[simp] theorem localRedPath_target
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localRedPath j x).target =
      ((E.recordAt j).layer.rightLabel x).1 := by
  rfl

/-- A local red path remains in its recorded cluster. -/
theorem localRedPath_vertex_mem_cluster
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) {v : V}
    (hv : v ∈ (E.localRedPath j x).vertexSet) :
    v ∈ P.cluster (E.recordAt j).index := by
  have hne :
      (E.localRedPath j x).source ≠
        (E.localRedPath j x).target := by
    intro h
    have hleft : ((E.recordAt j).label x).1 ∈
        P.left (E.recordAt j).index :=
      ((E.recordAt j).label x).2
    have hright : ((E.recordAt j).layer.rightLabel x).1 ∈
        P.right (E.recordAt j).index :=
      ((E.recordAt j).layer.rightLabel x).2
    have heq :
        ((E.recordAt j).label x).1 =
          ((E.recordAt j).layer.rightLabel x).1 := by
      simpa using h
    exact Finset.disjoint_left.mp
      (P.left_right_disjoint (E.recordAt j).index) hleft
      (heq ▸ hright)
  rcases
      (E.localRedPath j x)
        |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          hne hv with
    ⟨e, he, hve⟩
  rcases Sym2.mem_iff_exists.mp hve with ⟨w, rfl⟩
  have hadj :
      (E.recordAt j).layer.localGraph.Adj v w := by
    simpa using
      GraphPath.edgeSet_subset_edgeSet (E.localRedPath j x) he
  exact ((E.recordAt j).layer.localGraph_le_induced hadj).2.1

/-- Within one record, distinct rail labels select distinct red paths. -/
theorem localRedPath_index_injective
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length) :
    Function.Injective
      (fun x : Fin h =>
        (E.recordAt j).layer.red.indexOfSource
          ((E.recordAt j).label x)) := by
  intro x y hxy
  apply (E.recordAt j).label.injective
  apply Subtype.ext
  have hs := congrArg
    (fun i => ((E.recordAt j).layer.red.path i).source) hxy
  calc
    ((E.recordAt j).label x).1 =
        ((E.recordAt j).layer.red.path
          ((E.recordAt j).layer.red.indexOfSource
            ((E.recordAt j).label x))).source := by
            symm
            exact congrArg Subtype.val
              ((E.recordAt j).layer.red.source_indexOfSource
                ((E.recordAt j).label x))
    _ = ((E.recordAt j).layer.red.path
          ((E.recordAt j).layer.red.indexOfSource
            ((E.recordAt j).label y))).source := hs
    _ = ((E.recordAt j).label y).1 := by
          exact congrArg Subtype.val
            ((E.recordAt j).layer.red.source_indexOfSource
              ((E.recordAt j).label y))

/-- Red paths in one record carry a unique abstract rail label. -/
theorem localRedPath_label_unique
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    {x y : Fin h} {v : V}
    (hvx : v ∈ (E.localRedPath j x).vertexSet)
    (hvy : v ∈ (E.localRedPath j y).vertexSet) :
    x = y := by
  by_contra hxy
  have hindex :
      (E.recordAt j).layer.red.indexOfSource
          ((E.recordAt j).label x) ≠
        (E.recordAt j).layer.red.indexOfSource
          ((E.recordAt j).label y) :=
    fun h => hxy (E.localRedPath_index_injective j h)
  exact Finset.disjoint_left.mp
    ((E.recordAt j).layer.red.node_disjoint hindex) hvx hvy

/-- Local red paths belonging to different realized records are disjoint. -/
theorem localRedPath_record_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin E.finalState.records.length}
    {x y : Fin h} {v : V}
    (hvx : v ∈ (E.localRedPath j x).vertexSet)
    (hvy : v ∈ (E.localRedPath k y).vertexSet) :
    j = k := by
  have hvj := E.localRedPath_vertex_mem_cluster j x hvx
  have hvk := E.localRedPath_vertex_mem_cluster k y hvy
  have hindex : (E.recordAt j).index = (E.recordAt k).index := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvj hvk
  apply Fin.ext
  rw [← E.recordAt_index_eq hbudget j,
    ← E.recordAt_index_eq hbudget k]
  exact congrArg Fin.val hindex

/-- The record on the left of a realized connector gap. -/
def gapRecord
    (E : ExpanderBlocks P count)
    (j : Fin (E.finalState.records.length - 1)) :
    Fin E.finalState.records.length :=
  ⟨j.1, by omega⟩

/-- The record on the right of a realized connector gap. -/
def nextRecord
    (E : ExpanderBlocks P count)
    (j : Fin (E.finalState.records.length - 1)) :
    Fin E.finalState.records.length :=
  ⟨j.1 + 1, by omega⟩

/-- The left record of gap `j` is physically realized at `gapIndex j`. -/
theorem gapRecord_index_eq_gapIndex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) :
    (E.recordAt (E.gapRecord j)).index = E.gapIndex hbudget j := by
  apply Fin.ext
  simpa [gapRecord, gapIndex] using
    E.recordAt_index_eq hbudget (E.gapRecord j)

/-- The source nail on connector gap `j` carrying abstract rail `x`. -/
noncomputable def connectorSource
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    {v : V // v ∈ P.right (E.gapIndex hbudget j)} :=
  ⟨((E.recordAt (E.gapRecord j)).layer.rightLabel x).1, by
    rw [← E.gapRecord_index_eq_gapIndex hbudget j]
    exact ((E.recordAt (E.gapRecord j)).layer.rightLabel x).2⟩

/-- The connector path carrying abstract rail `x` across gap `j`. -/
noncomputable def connectorPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    GraphPath G :=
  (E.connectorAt hbudget j).path
    ((E.connectorAt hbudget j).indexOfSource
      (E.connectorSource hbudget j x))

/-- A connector gap together with its proof that a successor cluster
exists.  Packaging the proof removes dependent-rewrite noise when two
extensionally equal `Fin` indices describe the same physical gap. -/
abbrev ConnectorGap (P : StrongPathOfSetsSystem G ell h) :=
  {i : Fin ell // i.1 + 1 < ell}

/-- A named source of a connector gap. -/
abbrev NamedConnectorSource (P : StrongPathOfSetsSystem G ell h) :=
  Σ g : ConnectorGap P, {v : V // v ∈ P.right g.1}

/-- The endpoint selected by the connector's source-to-target bijection. -/
noncomputable def namedConnectorTarget
    (P : StrongPathOfSetsSystem G ell h)
    (z : NamedConnectorSource P) : V :=
  ((P.connector z.1.1 z.1.2).path
    ((P.connector z.1.1 z.1.2).indexOfSource z.2)).target

@[simp] theorem connectorPath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    (E.connectorPath hbudget j x).source =
      ((E.recordAt (E.gapRecord j)).layer.rightLabel x).1 := by
  exact congrArg Subtype.val
    ((E.connectorAt hbudget j).source_indexOfSource
      (E.connectorSource hbudget j x))

/-- The connector path for `x` ends at the occurrence of `x` in the
following record. -/
@[simp] theorem connectorPath_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    (x : Fin h) :
    (E.connectorPath hbudget j x).target =
      ((E.recordAt (E.nextRecord j)).label x).1 := by
  rcases E.recordAt_nextLabel hbudget j with ⟨hi, hnext⟩
  change
    (E.connectorPath hbudget j x).target =
      ((E.recordAt ⟨j.1 + 1, by omega⟩).label x).1
  rw [hnext x, Layer.nextLabel_apply_val]
  have hindex := E.gapRecord_index_eq_gapIndex hbudget j
  let a : ConnectorGap P :=
    ⟨E.gapIndex hbudget j, E.gapIndex_succ_lt hbudget j⟩
  let b : ConnectorGap P :=
    ⟨(E.recordAt (E.gapRecord j)).index, hi⟩
  have hab : a = b := by
    apply Subtype.ext
    exact hindex.symm
  let za : NamedConnectorSource P :=
    ⟨a, E.connectorSource hbudget j x⟩
  let zb : NamedConnectorSource P :=
    ⟨b, (E.recordAt (E.gapRecord j)).layer.rightLabel x⟩
  have hz : za = zb := by
    refine Sigma.ext hab ?_
    have hright : P.right a.1 = P.right b.1 := by
      exact congrArg P.right (congrArg Subtype.val hab)
    apply (Subtype.heq_iff_coe_eq (fun v => by rw [hright])).2
    rfl
  exact congrArg (namedConnectorTarget P) hz

/-- Distinct abstract rails use distinct connector paths in one gap. -/
theorem connectorPath_index_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1)) :
    Function.Injective
      (fun x : Fin h =>
        (E.connectorAt hbudget j).indexOfSource
          (E.connectorSource hbudget j x)) := by
  intro x y hxy
  apply (E.recordAt (E.gapRecord j)).layer.rightLabel.injective
  apply Subtype.ext
  have hs := congrArg
    (fun i => ((E.connectorAt hbudget j).path i).source) hxy
  calc
    ((E.recordAt (E.gapRecord j)).layer.rightLabel x).1 =
        ((E.connectorAt hbudget j).path
          ((E.connectorAt hbudget j).indexOfSource
            (E.connectorSource hbudget j x))).source := by
              symm
              exact congrArg Subtype.val
                ((E.connectorAt hbudget j).source_indexOfSource
                  (E.connectorSource hbudget j x))
    _ = ((E.connectorAt hbudget j).path
          ((E.connectorAt hbudget j).indexOfSource
            (E.connectorSource hbudget j y))).source := hs
    _ = ((E.recordAt (E.gapRecord j)).layer.rightLabel y).1 := by
          exact congrArg Subtype.val
            ((E.connectorAt hbudget j).source_indexOfSource
              (E.connectorSource hbudget j y))

/-- Connector paths in one gap carry a unique abstract rail label. -/
theorem connectorPath_label_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    {x y : Fin h} {v : V}
    (hvx : v ∈ (E.connectorPath hbudget j x).vertexSet)
    (hvy : v ∈ (E.connectorPath hbudget j y).vertexSet) :
    x = y := by
  by_contra hxy
  have hindex :
      (E.connectorAt hbudget j).indexOfSource
          (E.connectorSource hbudget j x) ≠
        (E.connectorAt hbudget j).indexOfSource
          (E.connectorSource hbudget j y) :=
    fun h => hxy (E.connectorPath_index_injective hbudget j h)
  exact Finset.disjoint_left.mp
    ((E.connectorAt hbudget j).node_disjoint hindex) hvx hvy

/-- Connector paths belonging to different realized gaps are disjoint. -/
theorem connectorPath_gap_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {j k : Fin (E.finalState.records.length - 1)}
    {x y : Fin h} {v : V}
    (hvx : v ∈ (E.connectorPath hbudget j x).vertexSet)
    (hvy : v ∈ (E.connectorPath hbudget k y).vertexSet) :
    j = k := by
  by_contra hjk
  have hgap :
      E.gapIndex hbudget j ≠ E.gapIndex hbudget k := by
    intro heq
    apply hjk
    apply Fin.ext
    simpa [gapIndex] using congrArg Fin.val heq
  exact Finset.disjoint_left.mp
    (P.connector_mutually_nodeDisjoint
      (E.gapIndex_succ_lt hbudget j)
      (E.gapIndex_succ_lt hbudget k) hgap
      ((E.connectorAt hbudget j).indexOfSource
        (E.connectorSource hbudget j x))
      ((E.connectorAt hbudget k).indexOfSource
        (E.connectorSource hbudget k y))) hvx hvy

/-- If a local red path meets a connector path, both pieces carry the same
abstract rail label. -/
theorem localRedPath_connectorPath_label_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (k : Fin (E.finalState.records.length - 1))
    {x y : Fin h} {v : V}
    (hvLocal : v ∈ (E.localRedPath j x).vertexSet)
    (hvConnector : v ∈ (E.connectorPath hbudget k y).vertexSet) :
    x = y := by
  have hvCluster :=
    E.localRedPath_vertex_mem_cluster j x hvLocal
  have hendpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget k) (E.gapIndex_succ_lt hbudget k)
      (E.recordAt j).index
      ((E.connectorAt hbudget k).indexOfSource
        (E.connectorSource hbudget k y))
      hvConnector hvCluster
  rcases hendpoint with hsource | htarget
  · have hvGap :
        v ∈ P.cluster (E.gapIndex hbudget k) := by
      apply P.right_subset_cluster (E.gapIndex hbudget k)
      simpa [hsource] using
        (E.connectorAt hbudget k).source_mem
          ((E.connectorAt hbudget k).indexOfSource
            (E.connectorSource hbudget k y))
    have hindex :
        (E.recordAt j).index = E.gapIndex hbudget k := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hvCluster hvGap
    have hj : j = E.gapRecord k := by
      apply Fin.ext
      have hjval := E.recordAt_index_eq hbudget j
      have hkval := congrArg Fin.val hindex
      simpa [gapRecord, gapIndex] using hjval.symm.trans hkval
    have hvY :
        v ∈ (E.localRedPath (E.gapRecord k) y).vertexSet := by
      have hvTarget :
          ((E.recordAt (E.gapRecord k)).layer.rightLabel y).1 ∈
            (E.localRedPath (E.gapRecord k) y).vertexSet := by
        rw [← E.localRedPath_target (E.gapRecord k) y]
        exact GraphPath.target_mem_vertexSet _
      have hvEq :
          v =
            ((E.recordAt (E.gapRecord k)).layer.rightLabel y).1 :=
        hsource.trans (E.connectorPath_source hbudget k y)
      simpa [hvEq] using hvTarget
    subst j
    exact E.localRedPath_label_unique (E.gapRecord k) hvLocal hvY
  · let next : Fin ell :=
      ⟨(E.gapIndex hbudget k).1 + 1,
        E.gapIndex_succ_lt hbudget k⟩
    have hvNext : v ∈ P.cluster next := by
      apply P.left_subset_cluster next
      simpa [next, htarget] using
        (E.connectorAt hbudget k).target_mem
          ((E.connectorAt hbudget k).indexOfSource
            (E.connectorSource hbudget k y))
    have hindex :
        (E.recordAt j).index = next := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hvCluster hvNext
    have hj : j = E.nextRecord k := by
      apply Fin.ext
      have hjval := E.recordAt_index_eq hbudget j
      have hkval := congrArg Fin.val hindex
      simpa [nextRecord, next, gapIndex] using hjval.symm.trans hkval
    have hvY :
        v ∈ (E.localRedPath (E.nextRecord k) y).vertexSet := by
      have hvSource :
          ((E.recordAt (E.nextRecord k)).label y).1 ∈
            (E.localRedPath (E.nextRecord k) y).vertexSet := by
        rw [← E.localRedPath_source (E.nextRecord k) y]
        exact GraphPath.source_mem_vertexSet _
      have hvEq :
          v = ((E.recordAt (E.nextRecord k)).label y).1 :=
        htarget.trans (E.connectorPath_target hbudget k y)
      simpa [hvEq] using hvSource
    subst j
    exact E.localRedPath_label_unique (E.nextRecord k) hvLocal hvY

/-- A vertex is carried by rail `x` when it lies on one of its local red
pieces or one of its connector pieces. -/
def RedCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (v : V) (x : Fin h) : Prop :=
  (∃ j : Fin E.finalState.records.length,
      v ∈ (E.localRedPath j x).vertexSet) ∨
    (∃ j : Fin (E.finalState.records.length - 1),
      v ∈ (E.connectorPath hbudget j x).vertexSet)

/-- Every physical red vertex has at most one abstract rail label. -/
theorem redCarrier_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v : V} {x y : Fin h}
    (hx : E.RedCarrier hbudget v x)
    (hy : E.RedCarrier hbudget v y) :
    x = y := by
  rcases hx with ⟨j, hx⟩ | ⟨j, hx⟩
  · rcases hy with ⟨k, hy⟩ | ⟨k, hy⟩
    · have hjk := E.localRedPath_record_unique hbudget hx hy
      subst k
      exact E.localRedPath_label_unique j hx hy
    · exact E.localRedPath_connectorPath_label_unique hbudget j k hx hy
  · rcases hy with ⟨k, hy⟩ | ⟨k, hy⟩
    · exact
        (E.localRedPath_connectorPath_label_unique
          hbudget k j hy hx).symm
    · have hjk := E.connectorPath_gap_unique hbudget hx hy
      subst k
      exact E.connectorPath_label_unique hbudget j hx hy

/-- Both endpoints of a local-red support edge lie on one labelled rail. -/
theorem localRedSupport_adj_has_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v w : V} (hvw : E.localRedSupport.Adj v w) :
    ∃ x : Fin h,
      E.RedCarrier hbudget v x ∧ E.RedCarrier hbudget w x := by
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
  have hv :
      v ∈ (E.localRedPath j x).vertexSet := by
    rw [localRedPath, hindex]
    exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.recordAt j).layer.red.path a) he).1
  have hw :
      w ∈ (E.localRedPath j x).vertexSet := by
    rw [localRedPath, hindex]
    exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.recordAt j).layer.red.path a) he).2
  exact ⟨x, Or.inl ⟨j, hv⟩, Or.inl ⟨j, hw⟩⟩

/-- Both endpoints of a connector-support edge lie on one labelled rail. -/
theorem connectorSupport_adj_has_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v w : V} (hvw : (E.connectorSupport hbudget).Adj v w) :
    ∃ x : Fin h,
      E.RedCarrier hbudget v x ∧ E.RedCarrier hbudget w x := by
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
      {z : V // z ∈
        P.right (E.recordAt (E.gapRecord j)).index} :=
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
  have hv :
      v ∈ (E.connectorPath hbudget j x).vertexSet := by
    rw [connectorPath, hindex]
    exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.connectorAt hbudget j).path a) he).1
  have hw :
      w ∈ (E.connectorPath hbudget j x).vertexSet := by
    rw [connectorPath, hindex]
    exact (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.connectorAt hbudget j).path a) he).2
  exact ⟨x, Or.inr ⟨j, hv⟩, Or.inr ⟨j, hw⟩⟩

/-- Every red-support edge has one common abstract rail label at both
endpoints. -/
theorem redSupport_adj_has_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v w : V} (hvw : (E.redSupport hbudget).Adj v w) :
    ∃ x : Fin h,
      E.RedCarrier hbudget v x ∧ E.RedCarrier hbudget w x := by
  rcases hvw with hvw | hvw
  · exact E.localRedSupport_adj_has_carrier hbudget hvw
  · exact E.connectorSupport_adj_has_carrier hbudget hvw

/-- Every vertex at which the assembled support has degree four lies on a
unique red rail. Blue-only internal path vertices have degree at most two and
therefore never carry a thinning choice. -/
theorem degreeFour_has_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {v : V}
    (hv : v ∈ degreeFourVertices (E.assembledSupport hbudget)) :
    ∃ x : Fin h, E.RedCarrier hbudget v x := by
  classical
  by_contra hcarrier
  have hnored : ¬ ∃ w : V, (E.redSupport hbudget).Adj v w := by
    rintro ⟨w, hvw⟩
    rcases E.redSupport_adj_has_carrier hbudget hvw with
      ⟨x, hvx, _⟩
    exact hcarrier ⟨x, hvx⟩
  have hdegree :
      DegreeAtMost (E.assembledSupport hbudget) v 2 := by
    rcases E.blueSupport_maxDegreeAtMost_two hbudget v with
      ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro w
    constructor
    · intro hw
      exact Or.inr ((hN w).1 hw)
    · intro hvw
      rcases hvw with hvw | hvw
      · exact False.elim (hnored ⟨w, hvw⟩)
      · exact (hN w).2 hvw
  have hv' := hv
  change
    v ∈ Finset.univ.filter
      (fun z => ¬ DegreeAtMost (E.assembledSupport hbudget) z 3) at hv'
  have hnot :
      ¬ DegreeAtMost (E.assembledSupport hbudget) v 3 :=
    (Finset.mem_filter.mp hv').2
  exact hnot (DegreeAtMost.mono hdegree (by omega))

/-- Assign every host vertex a rail.  Vertices outside the red support receive
the caller-supplied fallback; this choice is irrelevant to red edges and to
the labelled blue endpoints used below. -/
noncomputable def railOwner
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (v : V) : Fin h :=
  by
    classical
    exact if hv : ∃ x : Fin h, E.RedCarrier hbudget v x
      then Classical.choose hv
      else fallback

/-- The owner of a red-carried vertex is its unique carrier. -/
theorem railOwner_eq_of_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) {v : V} {x : Fin h}
    (hx : E.RedCarrier hbudget v x) :
    E.railOwner hbudget fallback v = x := by
  classical
  rw [railOwner, dif_pos ⟨x, hx⟩]
  exact E.redCarrier_unique hbudget (Classical.choose_spec ⟨x, hx⟩) hx

/-- Red-support edges become loops under the rail-owner map. -/
theorem railOwner_eq_of_redSupport_adj
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) {v w : V}
    (hvw : (E.redSupport hbudget).Adj v w) :
    E.railOwner hbudget fallback v =
      E.railOwner hbudget fallback w := by
  rcases E.redSupport_adj_has_carrier hbudget hvw with
    ⟨x, hv, hw⟩
  rw [E.railOwner_eq_of_redCarrier hbudget fallback hv,
    E.railOwner_eq_of_redCarrier hbudget fallback hw]

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
