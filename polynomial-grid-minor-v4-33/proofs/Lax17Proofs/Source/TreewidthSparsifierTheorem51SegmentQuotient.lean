import Lax17Proofs.Source.TreewidthSparsifierTheorem51PhysicalSegments

namespace Lax17Proofs

universe u v w

/-!
# The physical-segment quotient

The graph `F` in Step 2 of `treewidth-sparsifier.pdf`, Theorem 5.1 contracts
every segment of every red rail.  The Lean layer graphs retain degree-two
subdivision vertices, so this module assigns every vertex lying on a red rail
to its unique physical segment and assigns the remaining subdivision vertices
to a fixed fallback segment.  Applying this owner map to every physical edge
produces the required finite edge-indexed multigraph.  In particular, no
ambient isolated vertex becomes a spurious quotient vertex.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open ChekuriChuzhoySection5TerminalSkeleton


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- Every red-carried vertex lies on the corresponding complete exact rail. -/
theorem redCarrier_mem_exactRailPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {v : V} {x : Fin h}
    (hv : E.RedCarrier hbudget v x) :
    v ∈ (E.exactRailPath hbudget hrecords x).vertexSet := by
  rcases hv with ⟨j, hv⟩ | ⟨k, hv⟩
  · exact
      E.localRedPath_vertexSet_subset_exactRailPath
        hbudget hrecords j x (by simpa using hv)
  · exact
      E.connectorPath_vertexSet_subset_exactRailPath
        hbudget hrecords k x (by simpa using hv)

/-- Conversely, every vertex of an exact rail is carried by that rail. -/
theorem exactRailPath_vertex_has_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {v : V} {x : Fin h}
    (hv : v ∈ (E.exactRailPath hbudget hrecords x).vertexSet) :
    E.RedCarrier hbudget v x := by
  rcases
      (E.exactRailPrefix hbudget hrecords x
        (E.finalState.records.length - 1) (by omega)).vertex_mem hv with
    ⟨j, _hj, hvj⟩ | ⟨k, _hk, hvk⟩
  · exact Or.inl ⟨j, hvj⟩
  · exact Or.inr ⟨k, hvk⟩

/-- Every red-carried vertex belongs to one physical segment. -/
theorem exists_exactRailSegmentIndex_of_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    {v : V} {x : Fin h}
    (hv : E.RedCarrier hbudget v x) :
    ∃ i : ExactRailSegmentIndex E hbudget hrecords B hB,
      i.1 = x ∧
        v ∈ (E.exactRailSegmentPathAt
          hbudget hrecords B hB i).vertexSet := by
  classical
  have hvRail :
      v ∈ (E.exactRailPath hbudget hrecords x).walk.support := by
    simpa [GraphPath.vertexSet] using
      E.redCarrier_mem_exactRailPath hbudget hrecords hv
  have hvFlat :
      v ∈
        (E.exactRailSegmentation hbudget hrecords x B hB
          |>.segments.flatten) := by
    rw [E.exactRailSegmentation_flatten hbudget hrecords x B hB]
    exact hvRail
  rcases List.mem_flatten.mp hvFlat with ⟨s, hs, hvs⟩
  rcases List.get_of_mem hs with ⟨i, hi⟩
  let q : ExactRailSegmentIndex E hbudget hrecords B hB := ⟨x, i⟩
  refine ⟨q, rfl, ?_⟩
  rw [E.exactRailSegmentPathAt_vertexSet]
  have hlist :
      E.exactRailSegmentList hbudget hrecords B hB q = s := by
    exact hi
  simpa [hlist] using hvs

/-- Distinct segment indices have disjoint physical branch sets, hence a
physical vertex belongs to at most one segment. -/
theorem exactRailSegmentIndex_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    {i j : ExactRailSegmentIndex E hbudget hrecords B hB}
    {v : V}
    (hvi :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet)
    (hvj :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB j).vertexSet) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp
    (E.exactRailSegmentPathAt_nodeDisjoint
      hbudget hrecords B hB hij) hvi hvj

/-- A path index for one local blue routing path. -/
abbrev LocalBlueIndex (E : ExpanderBlocks P count) :=
  Σ j : Fin E.finalState.records.length,
    {x : Fin h // x ∈ (E.recordAt j).cut.left}

/-- A physical vertex belongs to at most one of the local blue paths stored
in the transcript.  Paths in one routing are node-disjoint, and different
records occupy disjoint path-of-sets clusters. -/
theorem localBlueIndex_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    {z w : E.LocalBlueIndex} {v : V}
    (hvz : v ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hvw : v ∈ (E.localBluePath w.1 w.2).vertexSet) :
    z = w := by
  rcases z with ⟨j, x⟩
  rcases w with ⟨k, y⟩
  have hjk : j = k :=
    E.localBluePath_record_unique hbudget hvz hvw
  subst k
  have hxy : x = y :=
    E.localBluePath_label_unique j hvz hvw
  subst y
  rfl

/-- Both endpoints of every blue-support edge lie on one canonical local
blue path. -/
theorem blueSupport_adj_has_localBlueIndex
    (E : ExpanderBlocks P count)
    {v w : V} (hvw : E.blueSupport.Adj v w) :
    ∃ z : E.LocalBlueIndex,
      v ∈ (E.localBluePath z.1 z.2).vertexSet ∧
        w ∈ (E.localBluePath z.1 z.2).vertexSet := by
  classical
  simp only [blueSupport, _root_.SimpleGraph.iSup_adj] at hvw
  rcases hvw with ⟨j, hvw⟩
  rcases
      ((E.recordAt j).layer.blue.toPathPacking
        |>.spanningGraph_adj_iff_exists_path_edge).mp hvw with
    ⟨⟨a, he⟩, _hne⟩
  let source :
      {z : V //
        z ∈ labelledImage
          (E.recordAt j).label (E.recordAt j).cut.left} :=
    ⟨((E.recordAt j).layer.blue.path a).source,
      (E.recordAt j).layer.blue.source_mem a⟩
  let x : {x : Fin h // x ∈ (E.recordAt j).cut.left} :=
    (labelledImageEquiv
      (E.recordAt j).label (E.recordAt j).cut.left).symm source
  have hindex :
      (E.recordAt j).layer.blue.indexOfSource
          (labelledImageEquiv
            (E.recordAt j).label (E.recordAt j).cut.left x) = a := by
    rw [show
      labelledImageEquiv
          (E.recordAt j).label (E.recordAt j).cut.left x =
        source by
      exact
        (labelledImageEquiv
          (E.recordAt j).label (E.recordAt j).cut.left)
          |>.apply_symm_apply source]
    exact (E.recordAt j).layer.blue.indexOfSource_source a
  refine ⟨⟨j, x⟩, ?_, ?_⟩
  · rw [localBluePath, hindex]
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        ((E.recordAt j).layer.blue.path a) he).1
  · rw [localBluePath, hindex]
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet
        ((E.recordAt j).layer.blue.path a) he).2

/-- Every blue-support edge occurs on one canonical local blue path.  This is
the edge-level strengthening of `blueSupport_adj_has_localBlueIndex` needed
when a quotient edge is expanded back to its complete carrier-clean arc. -/
theorem blueSupport_edge_has_localBlueIndex
    (E : ExpanderBlocks P count)
    {e : Sym2 V} (he : e ∈ E.blueSupport.edgeSet) :
    ∃ z : E.LocalBlueIndex,
      e ∈ (E.localBluePath z.1 z.2).edgeSet := by
  classical
  have hadj : E.blueSupport.Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using he
  simp only [blueSupport, _root_.SimpleGraph.iSup_adj] at hadj
  rcases hadj with ⟨j, hadj⟩
  rcases
      ((E.recordAt j).layer.blue.toPathPacking
        |>.spanningGraph_adj_iff_exists_path_edge).mp hadj with
    ⟨⟨a, hea⟩, _hne⟩
  let source :
      {v : V //
        v ∈ labelledImage
          (E.recordAt j).label (E.recordAt j).cut.left} :=
    ⟨((E.recordAt j).layer.blue.path a).source,
      (E.recordAt j).layer.blue.source_mem a⟩
  let x : {x : Fin h // x ∈ (E.recordAt j).cut.left} :=
    (labelledImageEquiv
      (E.recordAt j).label (E.recordAt j).cut.left).symm source
  have hindex :
      (E.recordAt j).layer.blue.indexOfSource
          (labelledImageEquiv
            (E.recordAt j).label (E.recordAt j).cut.left x) = a := by
    rw [show
      labelledImageEquiv
          (E.recordAt j).label (E.recordAt j).cut.left x =
        source by
      exact
        (labelledImageEquiv
          (E.recordAt j).label (E.recordAt j).cut.left)
          |>.apply_symm_apply source]
    exact (E.recordAt j).layer.blue.indexOfSource_source a
  refine ⟨⟨j, x⟩, ?_⟩
  rw [localBluePath, hindex]
  simpa [Sym2.mk, e.out_eq] using hea

/-- The red-carried vertices on a local blue path which occur no later than
`v`.  The path source always belongs to this set. -/
noncomputable def precedingRedCandidates
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V) :
    Finset V := by
  classical
  let Q := E.localBluePath z.1 z.2
  exact Q.vertexSet.filter fun w =>
    Q.vertexIndex w ≤ Q.vertexIndex v ∧
      ∃ x : Fin h, E.RedCarrier hbudget w x

theorem precedingRedCandidates_nonempty
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) {v : V}
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    (E.precedingRedCandidates hbudget z v).Nonempty := by
  classical
  let Q := E.localBluePath z.1 z.2
  refine ⟨Q.source, ?_⟩
  simp only [precedingRedCandidates, Finset.mem_filter]
  refine ⟨GraphPath.source_mem_vertexSet Q, ?_, ?_⟩
  · rw [GraphPath.source_vertexIndex]
    exact Nat.zero_le _
  · exact
      ⟨z.2.1, Or.inl ⟨z.1, by
        rw [E.localBluePath_source]
        simpa [E.localRedPath_source] using
          GraphPath.source_mem_vertexSet
            (E.localRedPath z.1 z.2.1)⟩⟩

/-- The last red-carried vertex weakly preceding `v` on its local blue path. -/
noncomputable def precedingRedVertex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) : V :=
  Classical.choose
    (Finset.exists_max_image
      (E.precedingRedCandidates hbudget z v)
      (E.localBluePath z.1 z.2).vertexIndex
      (E.precedingRedCandidates_nonempty hbudget z hv))

theorem precedingRedVertex_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    E.precedingRedVertex hbudget z v hv ∈
      E.precedingRedCandidates hbudget z v :=
  (Classical.choose_spec
    (Finset.exists_max_image
      (E.precedingRedCandidates hbudget z v)
      (E.localBluePath z.1 z.2).vertexIndex
      (E.precedingRedCandidates_nonempty hbudget z hv))).1

/-- The selected red predecessor is maximal among all red-carried vertices
weakly preceding `v` on the same blue path. -/
theorem precedingRedVertex_maximal
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet)
    {w : V}
    (hw : w ∈ E.precedingRedCandidates hbudget z v) :
    (E.localBluePath z.1 z.2).vertexIndex w ≤
      (E.localBluePath z.1 z.2).vertexIndex
        (E.precedingRedVertex hbudget z v hv) :=
  (Classical.choose_spec
    (Finset.exists_max_image
      (E.precedingRedCandidates hbudget z v)
      (E.localBluePath z.1 z.2).vertexIndex
      (E.precedingRedCandidates_nonempty hbudget z hv))).2 w hw

/-- If `v` itself is red-carried, its last red predecessor is `v`. -/
theorem precedingRedVertex_eq_self_of_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet)
    {x : Fin h} (hcarrier : E.RedCarrier hbudget v x) :
    E.precedingRedVertex hbudget z v hv = v := by
  classical
  let Q := E.localBluePath z.1 z.2
  have hvCandidate :
      v ∈ E.precedingRedCandidates hbudget z v := by
    simp only [precedingRedCandidates, Finset.mem_filter]
    exact ⟨hv, Nat.le_refl _, ⟨x, hcarrier⟩⟩
  have hchosen :=
    E.precedingRedVertex_mem hbudget z v hv
  have hchosenData := Finset.mem_filter.mp hchosen
  apply Q.before_antisymm
  · exact (Q.before_iff_vertexIndex_le).2
      ⟨hchosenData.1, hv,
        hchosenData.2.1⟩
  · exact (Q.before_iff_vertexIndex_le).2
      ⟨hv, hchosenData.1,
        E.precedingRedVertex_maximal
          hbudget z v hv hvCandidate⟩

theorem precedingRedVertex_has_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    ∃ x : Fin h,
      E.RedCarrier hbudget
        (E.precedingRedVertex hbudget z v hv) x := by
  classical
  exact
    (Finset.mem_filter.mp
      (E.precedingRedVertex_mem hbudget z v hv)).2.2

/-- The physical red segment reached most recently before a blue-path
subdivision vertex. -/
noncomputable def precedingRedSegment
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    ExactRailSegmentIndex E hbudget hrecords B hB := by
  classical
  let hc :=
    E.precedingRedVertex_has_carrier hbudget z v hv
  let x := Classical.choose hc
  exact Classical.choose
    (E.exists_exactRailSegmentIndex_of_redCarrier
      hbudget hrecords B hB (Classical.choose_spec hc))

/-- At a red intersection, the preceding segment is exactly the unique
physical segment containing that vertex. -/
theorem precedingRedSegment_eq_of_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (hvi :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet) :
    E.precedingRedSegment hbudget hrecords B hB z v hv = i := by
  have hvRail :=
    E.exactRailSegmentPathAt_vertexSet_subset_rail
      hbudget hrecords B hB i hvi
  have hcarrier :
      E.RedCarrier hbudget v i.1 :=
    E.exactRailPath_vertex_has_carrier hbudget hrecords hvRail
  have hpred :
      E.precedingRedVertex hbudget z v hv = v :=
    E.precedingRedVertex_eq_self_of_carrier
      hbudget z v hv hcarrier
  unfold precedingRedSegment
  apply E.exactRailSegmentIndex_unique hbudget hrecords B hB
    (i :=
      Classical.choose
        (E.exists_exactRailSegmentIndex_of_redCarrier
          hbudget hrecords B hB
          (Classical.choose_spec
            (E.precedingRedVertex_has_carrier hbudget z v hv))))
    (j := i)
  · have hchosenMem :=
      (Classical.choose_spec
        (E.exists_exactRailSegmentIndex_of_redCarrier
          hbudget hrecords B hB
          (Classical.choose_spec
            (E.precedingRedVertex_has_carrier hbudget z v hv)))).2
    simpa [hpred] using hchosenMem
  · exact hvi

/-- The selected red predecessor belongs to the segment named by
`precedingRedSegment`. -/
theorem precedingRedVertex_mem_precedingRedSegment
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    E.precedingRedVertex hbudget z v hv ∈
      (E.exactRailSegmentPathAt hbudget hrecords B hB
        (E.precedingRedSegment
          hbudget hrecords B hB z v hv)).vertexSet := by
  unfold precedingRedSegment
  exact
    (Classical.choose_spec
      (E.exists_exactRailSegmentIndex_of_redCarrier
        hbudget hrecords B hB
        (Classical.choose_spec
          (E.precedingRedVertex_has_carrier hbudget z v hv)))).2

/-- The contracted segment owning a physical vertex.  Red vertices retain
their unique physical segment.  A blue-only subdivision vertex is assigned to
the segment containing the last red intersection preceding it on its unique
local blue path.  Only vertices outside the assembled support use the fallback
segment.  Consequently quotient fibres are assembled from a red segment and
initial pieces of incident blue chunks, rather than by identifying unrelated
blue paths. -/
noncomputable def segmentOwner
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (v : V) :
    ExactRailSegmentIndex E hbudget hrecords B hB := by
  classical
  exact
    if hex :
        ∃ i : ExactRailSegmentIndex E hbudget hrecords B hB,
          v ∈ (E.exactRailSegmentPathAt
            hbudget hrecords B hB i).vertexSet
    then Classical.choose hex
    else
      if hblue :
          ∃ z : E.LocalBlueIndex,
            v ∈ (E.localBluePath z.1 z.2).vertexSet
      then
        let z := Classical.choose hblue
        E.precedingRedSegment hbudget hrecords B hB z v
          (Classical.choose_spec hblue)
      else fallback

theorem segmentOwner_eq_of_mem
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    {v : V}
    (hv :
      v ∈ (E.exactRailSegmentPathAt
        hbudget hrecords B hB i).vertexSet) :
    E.segmentOwner hbudget hrecords B hB fallback v = i := by
  classical
  let hex :
      ∃ j : ExactRailSegmentIndex E hbudget hrecords B hB,
        v ∈ (E.exactRailSegmentPathAt
          hbudget hrecords B hB j).vertexSet :=
    ⟨i, hv⟩
  rw [segmentOwner]
  simp only [dif_pos hex]
  exact E.exactRailSegmentIndex_unique hbudget hrecords B hB
    (Classical.choose_spec hex) hv

/-- On a blue-only vertex, ownership is the segment at its last red
intersection.  Uniqueness of the local blue path makes this independent of
the existential witness selected in `segmentOwner`. -/
theorem segmentOwner_eq_precedingRedSegment_of_blue_only
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet)
    (hnored : ¬ ∃ x : Fin h, E.RedCarrier hbudget v x) :
    E.segmentOwner hbudget hrecords B hB fallback v =
      E.precedingRedSegment hbudget hrecords B hB z v hv := by
  classical
  have hnosegment :
      ¬ ∃ i : ExactRailSegmentIndex E hbudget hrecords B hB,
          v ∈ (E.exactRailSegmentPathAt
            hbudget hrecords B hB i).vertexSet := by
    rintro ⟨i, hvi⟩
    apply hnored
    exact ⟨i.1,
      E.exactRailPath_vertex_has_carrier hbudget hrecords
        (E.exactRailSegmentPathAt_vertexSet_subset_rail
          hbudget hrecords B hB i hvi)⟩
  rw [segmentOwner, dif_neg hnosegment]
  let hblue :
      ∃ w : E.LocalBlueIndex,
        v ∈ (E.localBluePath w.1 w.2).vertexSet := ⟨z, hv⟩
  rw [dif_pos hblue]
  have hstable :
      ∀ (w : E.LocalBlueIndex)
        (hw : v ∈ (E.localBluePath w.1 w.2).vertexSet),
        E.precedingRedSegment hbudget hrecords B hB w v hw =
          E.precedingRedSegment hbudget hrecords B hB z v hv := by
    intro w hw
    have hwz : w = z :=
      E.localBlueIndex_unique hbudget hw hv
    cases hwz
    rfl
  exact hstable (Classical.choose hblue) (Classical.choose_spec hblue)

/-- Along a local blue path, a vertex and its last red predecessor have the
same segment owner.  This is the contraction invariant used to replace each
degree-two blue arc by one suppressed edge. -/
theorem segmentOwner_precedingRedVertex
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (z : E.LocalBlueIndex) (v : V)
    (hv : v ∈ (E.localBluePath z.1 z.2).vertexSet) :
    E.segmentOwner hbudget hrecords B hB fallback
        (E.precedingRedVertex hbudget z v hv) =
      E.segmentOwner hbudget hrecords B hB fallback v := by
  classical
  let p := E.precedingRedVertex hbudget z v hv
  let i := E.precedingRedSegment hbudget hrecords B hB z v hv
  have hp : p ∈
      (E.exactRailSegmentPathAt hbudget hrecords B hB i).vertexSet := by
    simpa [p, i] using
      E.precedingRedVertex_mem_precedingRedSegment
        hbudget hrecords B hB z v hv
  have hownerP :
      E.segmentOwner hbudget hrecords B hB fallback p = i :=
    E.segmentOwner_eq_of_mem
      hbudget hrecords B hB fallback i hp
  by_cases hcarrier :
      ∃ x : Fin h, E.RedCarrier hbudget v x
  · rcases hcarrier with ⟨x, hx⟩
    have hpv :
        E.precedingRedVertex hbudget z v hv = v :=
      E.precedingRedVertex_eq_self_of_carrier
        hbudget z v hv hx
    simpa [p, hpv]
  · have hownerV :
        E.segmentOwner hbudget hrecords B hB fallback v = i := by
      simpa [i] using
        E.segmentOwner_eq_precedingRedSegment_of_blue_only
          hbudget hrecords B hB fallback z v hv hcarrier
    exact hownerP.trans hownerV.symm

theorem segmentOwner_rail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    {v : V} {x : Fin h}
    (hv : E.RedCarrier hbudget v x) :
    (E.segmentOwner hbudget hrecords B hB fallback v).1 = x := by
  rcases
      E.exists_exactRailSegmentIndex_of_redCarrier
        hbudget hrecords B hB hv with
    ⟨i, hiRail, hvi⟩
  rw [E.segmentOwner_eq_of_mem hbudget hrecords B hB fallback i hvi]
  exact hiRail

/-- Physical edges whose endpoint segment owners differ. -/
noncomputable def segmentCrossingEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Finset (Sym2 V) := by
  classical
  let owner := E.segmentOwner hbudget hrecords B hB fallback
  exact (E.assembledSupport hbudget).edgeFinset.filter fun e =>
    owner e.out.1 ≠ owner e.out.2

/-- The finite multigraph obtained by contracting all physical red
segments.  Its named edges are the actual physical edges crossing owner
fibres. -/
noncomputable def segmentQuotient
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    FiniteEdgeIndexedGraph
      (ExactRailSegmentIndex E hbudget hrecords B hB) := by
  classical
  let owner := E.segmentOwner hbudget hrecords B hB fallback
  let edges := E.segmentCrossingEdges
    hbudget hrecords B hB fallback
  exact {
    Edge := Fin edges.card
    left := fun q => owner ((edges.equivFin.symm q).1).out.1
    right := fun q => owner ((edges.equivFin.symm q).1).out.2
    end_ne := by
      intro q
      exact Finset.mem_filter.mp (edges.equivFin.symm q).2 |>.2
  }

/-- Physical vertices on one side of a segment-quotient cut. -/
noncomputable def segmentOwnerSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    E.segmentOwner hbudget hrecords B hB fallback v ∈ S

@[simp] theorem mem_segmentOwnerSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (v : V) :
    v ∈ E.segmentOwnerSide hbudget hrecords B hB fallback S ↔
      E.segmentOwner hbudget hrecords B hB fallback v ∈ S := by
  classical
  simp [segmentOwnerSide]

/-- Physical quotient edges whose segment endpoints cross `S`. -/
noncomputable def segmentBoundaryEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (Sym2 V) := by
  classical
  let owner := E.segmentOwner hbudget hrecords B hB fallback
  exact
    (E.segmentCrossingEdges hbudget hrecords B hB fallback).filter fun e =>
      (owner e.out.1 ∈ S ∧ owner e.out.2 ∉ S) ∨
        (owner e.out.2 ∈ S ∧ owner e.out.1 ∉ S)

/-- Quotient boundary indices and their represented physical edges are in
canonical bijection. -/
noncomputable def segmentBoundaryEquiv
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    {q : (E.segmentQuotient hbudget hrecords B hB fallback).Edge //
      q ∈
        (E.segmentQuotient hbudget hrecords B hB fallback).boundary S} ≃
      {e : Sym2 V //
        e ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S} := by
  classical
  let owner := E.segmentOwner hbudget hrecords B hB fallback
  let edges := E.segmentCrossingEdges hbudget hrecords B hB fallback
  let Q := E.segmentQuotient hbudget hrecords B hB fallback
  let edgeAt : Q.Edge → Sym2 V :=
    fun q => (edges.equivFin.symm q).1
  refine {
    toFun := fun q => ⟨edgeAt q.1, ?_⟩
    invFun := fun e => ⟨edges.equivFin ⟨e.1, ?_⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · have hcross :=
      (FiniteEdgeIndexedGraph.mem_boundary Q S q.1).mp q.2
    exact Finset.mem_filter.mpr
      ⟨(edges.equivFin.symm q.1).2, by
        simpa [Q, segmentQuotient, edgeAt, edges, owner,
          FiniteEdgeIndexedGraph.Crosses] using hcross⟩
  · exact (Finset.mem_filter.mp e.2).1
  · exact
      (FiniteEdgeIndexedGraph.mem_boundary Q S _).mpr
        (by
          simpa [Q, segmentQuotient, edges, owner,
            FiniteEdgeIndexedGraph.Crosses] using
              (Finset.mem_filter.mp e.2).2)
  · intro q
    apply Subtype.ext
    change edges.equivFin (edges.equivFin.symm q.1) = q.1
    exact edges.equivFin.apply_symm_apply q.1
  · intro e
    apply Subtype.ext
    change
      (edges.equivFin.symm
        (edges.equivFin
          ⟨e.1, (Finset.mem_filter.mp e.2).1⟩)).1 = e.1
    exact congrArg Subtype.val
      (edges.equivFin.symm_apply_apply
        ⟨e.1, (Finset.mem_filter.mp e.2).1⟩)

theorem segmentQuotient_boundary_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    ((E.segmentQuotient hbudget hrecords B hB fallback).boundary S).card =
      (E.segmentBoundaryEdges hbudget hrecords B hB fallback S).card := by
  classical
  calc
    ((E.segmentQuotient hbudget hrecords B hB fallback).boundary S).card =
        Fintype.card
          {q :
              (E.segmentQuotient hbudget hrecords B hB fallback).Edge //
            q ∈
              (E.segmentQuotient hbudget hrecords B hB fallback).boundary S} := by
      rw [Fintype.card_coe]
    _ = Fintype.card
          {e : Sym2 V //
            e ∈ E.segmentBoundaryEdges
              hbudget hrecords B hB fallback S} :=
      Fintype.card_congr
        (E.segmentBoundaryEquiv hbudget hrecords B hB fallback S)
    _ = (E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S).card := by
      rw [Fintype.card_coe]

/-- The physical edges represented by a quotient cut are exactly the
assembled-support edges crossing the corresponding owner fibres. -/
theorem segmentBoundaryEdges_eq_edgeBoundary_ownerSides
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    E.segmentBoundaryEdges hbudget hrecords B hB fallback S =
      Section44.edgeBoundary
        (E.assembledSupport hbudget)
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)
        (E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ) := by
  classical
  let owner := E.segmentOwner hbudget hrecords B hB fallback
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let Y := E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ
  ext e
  rw [Section44.mem_edgeBoundary]
  simp only [segmentBoundaryEdges, Finset.mem_filter,
    segmentCrossingEdges, _root_.SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨⟨heH, _hne⟩, hcross⟩
    refine ⟨heH, ?_⟩
    rcases hcross with hcross | hcross
    · refine ⟨e.out.1, ?_, e.out.2, ?_, ?_⟩
      · exact (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback S e.out.1).2 hcross.1
      · exact (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ e.out.2).2
          (by simpa using hcross.2)
      · rw [Sym2.mk, e.out_eq]
    · refine ⟨e.out.2, ?_, e.out.1, ?_, ?_⟩
      · exact (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback S e.out.2).2 hcross.1
      · exact (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ e.out.1).2
          (by simpa using hcross.2)
      · rw [Sym2.eq_swap, Sym2.mk, e.out_eq]
  · rintro ⟨heH, x, hx, y, hy, hxy⟩
    have hxS :
        owner x ∈ S := by
      exact (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback S x).1 (by simpa [X] using hx)
    have hyS :
        owner y ∉ S := by
      have hyc :=
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ y).1
          (by simpa [Y] using hy)
      simpa using hyc
    have hout :
        s(e.out.1, e.out.2) = s(x, y) := by
      rw [Sym2.mk, e.out_eq, hxy]
    rw [Sym2.eq_iff] at hout
    rcases hout with hout | hout
    · have he1S : owner e.out.1 ∈ S := by
        simpa [hout.1] using hxS
      have he2S : owner e.out.2 ∉ S := by
        simpa [hout.2] using hyS
      exact ⟨⟨heH, fun heq => by
          change owner e.out.1 = owner e.out.2 at heq
          exact he2S (heq ▸ he1S)⟩,
        Or.inl ⟨he1S, he2S⟩⟩
    · have he2S : owner e.out.2 ∈ S := by
        simpa [hout.2] using hxS
      have he1S : owner e.out.1 ∉ S := by
        simpa [hout.1] using hyS
      exact ⟨⟨heH, fun heq => by
          change owner e.out.1 = owner e.out.2 at heq
          exact he1S (heq.symm ▸ he2S)⟩,
        Or.inr ⟨he2S, he1S⟩⟩

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
