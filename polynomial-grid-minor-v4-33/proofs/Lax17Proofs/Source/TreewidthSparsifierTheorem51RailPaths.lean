import Lax17Proofs.Source.TreewidthSparsifierTheorem51Rails

namespace Lax17Proofs

universe u v w

/-!
# Concatenated red rails for Theorem 5.1

Step 2 of `treewidth-sparsifier.pdf`, Theorem 5.1 partitions the global red
paths.  The transcript modules previously proved only reachability along a
rail.  This module retains the actual concatenated path, built from the local
red path in each recorded layer and the connector between consecutive
layers.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- Every branch vertex of one unsuppressed local layer lies on a red path.
This lets the Step-2 segmentation count branch vertices instead of first
performing the paper's degree-two suppression. -/
theorem localBranchVertex_mem_localRedPath
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    {v : V}
    (hv :
      v ∈ branchVertexFinset (E.recordAt j).layer.localGraph) :
    ∃ x : Fin h, v ∈ (E.localRedPath j x).vertexSet := by
  classical
  let L := (E.recordAt j).layer
  have hvUnion :
      v ∈ branchVertexFinset
        (twoPackingUnionGraph L.red L.blue) := by
    simpa [L, ← (E.recordAt j).layer.support_eq] using hv
  have hvRed :
      v ∈ L.red.toPathPacking.vertexSet :=
    TwoPairBranchCarrier.red_vertexSet_mem_of_branchVertex hvUnion
  rcases L.red.toPathPacking.mem_vertexSet.mp hvRed with
    ⟨i, hvi⟩
  let named :
      {z : V // z ∈ P.left (E.recordAt j).index} :=
    ⟨(L.red.path i).source, L.red.source_mem i⟩
  let x : Fin h := (E.recordAt j).label.symm named
  have hlabel : (E.recordAt j).label x = named :=
    (E.recordAt j).label.apply_symm_apply named
  have hindex :
      L.red.indexOfSource ((E.recordAt j).label x) = i := by
    rw [hlabel]
    exact L.red.indexOfSource_source i
  refine ⟨x, ?_⟩
  simpa [localRedPath, L, hindex] using hvi

/-- Branch vertices encountered by one labelled local red path, in path
order.  Working with branch vertices is equivalent to the source's prior
degree-two suppression for all later cardinality estimates. -/
noncomputable def localBranchTrace
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) : List V :=
  (E.localRedPath j x).walk.support.filter fun v =>
    v ∈ branchVertexFinset (E.recordAt j).layer.localGraph

@[simp] theorem mem_localBranchTrace
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) (v : V) :
    v ∈ E.localBranchTrace j x ↔
      v ∈ (E.localRedPath j x).vertexSet ∧
        v ∈ branchVertexFinset (E.recordAt j).layer.localGraph := by
  classical
  simp [localBranchTrace, GraphPath.vertexSet]

theorem localBranchTrace_nodup
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localBranchTrace j x).Nodup := by
  classical
  exact (E.localRedPath j x).isPath.support_nodup.filter _

/-- A single rail sees at most all branch vertices in its local layer. -/
theorem localBranchTrace_length_le
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localBranchTrace j x).length ≤
      branchVertexCount (E.recordAt j).layer.localGraph := by
  classical
  have hnodup := E.localBranchTrace_nodup j x
  rw [← List.toFinset_card_of_nodup hnodup,
    ← branchVertexFinset_card]
  apply Finset.card_le_card
  intro v hv
  have hv' : v ∈ E.localBranchTrace j x := by
    simpa using hv
  exact (E.mem_localBranchTrace j x v).mp hv' |>.2

theorem localBranchTrace_length_le_theorem13
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (x : Fin h) :
    (E.localBranchTrace j x).length ≤ 8 * h ^ 4 + 8 * h := by
  have hbound := (E.recordAt j).layer.branch_bound
  rw [← (E.recordAt j).layer.support_eq] at hbound
  exact (E.localBranchTrace_length_le j x).trans hbound

/-- Branch events on one complete rail, tagged by their recorded layer. -/
noncomputable def railBranchEvents
    (E : ExpanderBlocks P count)
    (x : Fin h) :
    List (Fin E.finalState.records.length × V) :=
  (List.ofFn fun j : Fin E.finalState.records.length =>
    (E.localBranchTrace j x).map fun v => (j, v)).flatten

theorem railBranchEvents_length_le
    (E : ExpanderBlocks P count)
    (x : Fin h) :
    (E.railBranchEvents x).length ≤
      E.finalState.records.length * (8 * h ^ 4 + 8 * h) := by
  rw [railBranchEvents, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    ∑ j : Fin E.finalState.records.length,
        ((E.localBranchTrace j x).map fun v => (j, v)).length =
        ∑ j : Fin E.finalState.records.length,
          (E.localBranchTrace j x).length := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp
    _ ≤ ∑ _j : Fin E.finalState.records.length,
          (8 * h ^ 4 + 8 * h) :=
      Finset.sum_le_sum fun j _hj =>
        E.localBranchTrace_length_le_theorem13 j x
    _ = E.finalState.records.length * (8 * h ^ 4 + 8 * h) := by
      simp

/-- A red path from the first recorded layer through record `n`, together
with its exact endpoints. -/
structure RailPrefix
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (n : ℕ) (hn : n < E.finalState.records.length) where
  path : GraphPath (E.redSupport hbudget)
  source_eq :
    path.source = E.initialTerminal hrecords x
  target_eq :
    path.target = (E.localRedPath ⟨n, hn⟩ x).target

/-- Concatenate the local red pieces and intervening connectors up to a
specified record. -/
noncomputable def railPrefix
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    (n : ℕ) → (hn : n < E.finalState.records.length) →
      RailPrefix E hbudget hrecords x n hn
  | 0, hn => by
      let j : Fin E.finalState.records.length := ⟨0, hn⟩
      refine {
        path := E.localRedPathInRedSupport hbudget j x
        source_eq := ?_
        target_eq := ?_
      }
      · rw [E.localRedPathInRedSupport_source,
          E.localRedPath_source]
        apply congrArg Subtype.val
        change
          (E.recordAt j).label x =
            (E.recordAt (E.firstRecord hrecords)).label x
        congr 2
      · exact E.localRedPathInRedSupport_target hbudget j x
  | n + 1, hn => by
      let prevIndex : Fin E.finalState.records.length :=
        ⟨n, by omega⟩
      let gapIndex : Fin (E.finalState.records.length - 1) :=
        ⟨n, by omega⟩
      let nextIndex : Fin E.finalState.records.length := ⟨n + 1, hn⟩
      let previous := E.railPrefix hbudget hrecords x n (by omega)
      let connector :=
        E.connectorPathInRedSupport hbudget gapIndex x
      let localPiece :=
        E.localRedPathInRedSupport hbudget nextIndex x
      have hPreviousConnector :
          previous.path.target = connector.source := by
        rw [previous.target_eq]
        simp only [connector,
          E.connectorPathInRedSupport_source,
          E.connectorPath_source]
        change
          (E.localRedPath prevIndex x).target =
            (E.localRedPath (E.gapRecord gapIndex) x).target
        congr 2
      have hConnectorLocal :
          connector.target = localPiece.source := by
        simp only [connector, localPiece,
          E.connectorPathInRedSupport_target,
          E.localRedPathInRedSupport_source,
          E.connectorPath_target]
        rw [← E.localRedPath_source (E.nextRecord gapIndex) x]
        congr 2
      refine {
        path :=
          previous.path.append3WithEqToPath connector localPiece
            hPreviousConnector hConnectorLocal
        source_eq := ?_
        target_eq := ?_
      }
      · simpa using previous.source_eq
      · change localPiece.target =
          (E.localRedPath ⟨n + 1, hn⟩ x).target
        rw [E.localRedPathInRedSupport_target]
termination_by n _ => n

/-- The last recorded layer. -/
def lastRecord
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length) :
    Fin E.finalState.records.length :=
  ⟨E.finalState.records.length - 1, by omega⟩

/-- The complete red rail carrying label `x`. -/
noncomputable def railPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    GraphPath (E.redSupport hbudget) :=
  (E.railPrefix hbudget hrecords x
    (E.finalState.records.length - 1) (by omega)).path

@[simp] theorem railPath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    (E.railPath hbudget hrecords x).source =
      E.initialTerminal hrecords x :=
  (E.railPrefix hbudget hrecords x
    (E.finalState.records.length - 1) (by omega)).source_eq

@[simp] theorem railPath_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    (E.railPath hbudget hrecords x).target =
      (E.localRedPath (E.lastRecord hrecords) x).target := by
  exact
    (E.railPrefix hbudget hrecords x
      (E.finalState.records.length - 1) (by omega)).target_eq

/-- A local red piece and a connector piece of the same rail can meet only
at one of the two physical glue endpoints of that connector. -/
theorem localRedPath_connectorPath_intersection
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (k : Fin (E.finalState.records.length - 1))
    (x : Fin h) {v : V}
    (hvLocal : v ∈ (E.localRedPath j x).vertexSet)
    (hvConnector :
      v ∈ (E.connectorPath hbudget k x).vertexSet) :
    (j = E.gapRecord k ∧
      v = (E.localRedPath (E.gapRecord k) x).target ∧
      v = (E.connectorPath hbudget k x).source) ∨
    (j = E.nextRecord k ∧
      v = (E.localRedPath (E.nextRecord k) x).source ∧
      v = (E.connectorPath hbudget k x).target) := by
  have hvCluster :=
    E.localRedPath_vertex_mem_cluster j x hvLocal
  have hendpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget k) (E.gapIndex_succ_lt hbudget k)
      (E.recordAt j).index
      ((E.connectorAt hbudget k).indexOfSource
        (E.connectorSource hbudget k x))
      hvConnector hvCluster
  rcases hendpoint with hsource | htarget
  · have hvGap :
        v ∈ P.cluster (E.gapIndex hbudget k) := by
      apply P.right_subset_cluster (E.gapIndex hbudget k)
      simpa [hsource] using
        (E.connectorAt hbudget k).source_mem
          ((E.connectorAt hbudget k).indexOfSource
            (E.connectorSource hbudget k x))
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
    left
    refine ⟨hj, ?_, hsource⟩
    subst j
    calc
      v = (E.connectorPath hbudget k x).source := hsource
      _ = (E.localRedPath (E.gapRecord k) x).target := by
        rw [E.connectorPath_source, E.localRedPath_target]
  · let next : Fin ell :=
      ⟨(E.gapIndex hbudget k).1 + 1,
        E.gapIndex_succ_lt hbudget k⟩
    have hvNext : v ∈ P.cluster next := by
      apply P.left_subset_cluster next
      simpa [next, htarget] using
        (E.connectorAt hbudget k).target_mem
          ((E.connectorAt hbudget k).indexOfSource
            (E.connectorSource hbudget k x))
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
    right
    refine ⟨hj, ?_, htarget⟩
    subst j
    calc
      v = (E.connectorPath hbudget k x).target := htarget
      _ = (E.localRedPath (E.nextRecord k) x).source := by
        rw [E.connectorPath_target, E.localRedPath_source]

private theorem lazyRound_edgeBoundary_compl
    (R : LazyRound (Fin h)) (S : Finset (Fin h)) :
    R.edgeBoundary Sᶜ = R.edgeBoundary S := by
  classical
  ext x
  simp only [LazyRound.mem_edgeBoundary, LazyRound.edgeCrosses,
    Finset.mem_compl]
  tauto

private theorem edgeBoundaryCount_compl
    (rounds : List (LazyRound (Fin h))) (S : Finset (Fin h)) :
    edgeBoundaryCount rounds Sᶜ = edgeBoundaryCount rounds S := by
  induction rounds with
  | nil => rfl
  | cons R rounds ih =>
      simp only [edgeBoundaryCount_cons, lazyRound_edgeBoundary_compl, ih]

/-- Every independently restarted half-expander contributes at least one
matching edge to every nontrivial label cut.  This is the first case in the
proof of source Claim 5.4, where two complete red rails lie on opposite sides
of the proposed contracted cut. -/
theorem count_le_recordBoundary_card_of_nontrivial
    (E : ExpanderBlocks P count)
    (S : Finset (Fin h))
    (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    count ≤ Fintype.card (E.RecordBoundary S) := by
  classical
  have hScard : S.card ≤ h := by
    simpa using Finset.card_le_univ S
  have hcomp : (Sᶜ : Finset (Fin h)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hc
    apply hproper
    have hc' := congrArg (fun T : Finset (Fin h) => Tᶜ) hc
    simpa using hc'
  have hcompCard :
      (Sᶜ : Finset (Fin h)).card = h - S.card := by
    simpa using Finset.card_compl S
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hcompPos : 0 < (Sᶜ : Finset (Fin h)).card :=
    Finset.card_pos.mpr hcomp
  have heach :
      ∀ i : Fin count, 1 ≤ edgeBoundaryCount (E.rounds i) S := by
    intro i
    by_cases hhalf : 2 * S.card ≤ h
    · have hbound :=
        (CutMatchingGame.isHalfEdgeExpander_iff (E.rounds i)).mp
          (E.each_halfExpander i) S
          hSpos (by simpa using hhalf)
      omega
    · have hcompHalf :
          2 * (Sᶜ : Finset (Fin h)).card ≤ h := by
        rw [hcompCard]
        omega
      have hbound :=
        (CutMatchingGame.isHalfEdgeExpander_iff (E.rounds i)).mp
          (E.each_halfExpander i) Sᶜ
          hcompPos (by simpa using hcompHalf)
      rw [edgeBoundaryCount_compl] at hbound
      omega
  rw [E.recordBoundary_card_eq_edgeBoundaryCount,
    E.edgeBoundaryCount_flatten_eq_sum]
  calc
    count = ∑ _i : Fin count, 1 := by simp
    _ ≤ ∑ i : Fin count, edgeBoundaryCount (E.rounds i) S :=
      Finset.sum_le_sum fun i _hi => heach i

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
