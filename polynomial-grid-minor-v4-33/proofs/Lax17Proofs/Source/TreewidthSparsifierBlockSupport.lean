import Lax17Proofs.Source.TreewidthSparsifierTheorem51Rails

namespace Lax17Proofs

universe u v w

/-!
# One cut-matching block as a connected simple graph

The first case of Claim 5.4 uses one physical path from every independently
restarted expander block.  This file begins that construction with the exact
abstract fact: the union of the matching edges of a half-edge-expander is
connected.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The simple support graph of all matching edges occurring in a list of
cut-matching rounds. -/
def roundListSupport (rounds : List (LazyRound X)) :
    _root_.SimpleGraph X where
  Adj x y :=
    x ≠ y ∧
      ∃ R ∈ rounds, ∃ a : {z : X // z ∈ R.cut.left},
        (x = a.1 ∧ y = R.matching.rightEndpoint a) ∨
          (y = a.1 ∧ x = R.matching.rightEndpoint a)
  symm := by
    intro x y h
    exact ⟨Ne.symm h.1, by
      rcases h.2 with ⟨R, hR, a, ha⟩
      exact ⟨R, hR, a, ha.elim Or.inr Or.inl⟩⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

theorem roundListSupport_adj_of_mem_edgeBoundary
    (rounds : List (LazyRound X)) (S : Finset X)
    {R : LazyRound X} (hR : R ∈ rounds)
    {a : {z : X // z ∈ R.cut.left}}
    (ha : a ∈ R.edgeBoundary S) :
    (roundListSupport rounds).Adj a.1
      (R.matching.rightEndpoint a) := by
  refine
    ⟨by
      intro heq
      exact
        R.cut.not_mem_left_of_mem_right
          (R.matching.rightEndpoint_mem a) (heq ▸ a.2),
      ⟨R, hR, a, Or.inl ⟨rfl, rfl⟩⟩⟩

private theorem exists_round_boundary_of_edgeBoundaryCount_pos
    (rounds : List (LazyRound X)) (S : Finset X)
    (hpos : 0 < edgeBoundaryCount rounds S) :
    ∃ R ∈ rounds, (R.edgeBoundary S).Nonempty := by
  induction rounds with
  | nil => simp [edgeBoundaryCount] at hpos
  | cons R rest ih =>
      simp only [edgeBoundaryCount_cons] at hpos
      by_cases hRzero : (R.edgeBoundary S).card = 0
      · have hrest : 0 < edgeBoundaryCount rest S := by omega
        rcases ih hrest with ⟨Q, hQ, hQnonempty⟩
        exact ⟨Q, by simp [hQ], hQnonempty⟩
      · exact
          ⟨R, by simp, Finset.card_ne_zero.mp hRzero⟩

/-- A half-edge-expander on at least two vertices has connected matching
support. -/
theorem roundListSupport_reachable_of_halfExpander
    {rounds : List (LazyRound X)}
    (hexp : IsHalfEdgeExpander rounds)
    (hX : 2 ≤ Fintype.card X)
    (x y : X) :
    (roundListSupport rounds).Reachable x y := by
  classical
  by_contra hnot
  let S : Finset X :=
    Finset.univ.filter fun z =>
      (roundListSupport rounds).Reachable x z
  have hxS : x ∈ S := by
    simp [S]
  have hyS : y ∉ S := by
    simpa [S] using hnot
  have hSnonempty : S.Nonempty := ⟨x, hxS⟩
  have hSproper : S ≠ Finset.univ := by
    intro h
    have : y ∈ S := by rw [h]; simp
    exact hyS this
  let T : Finset X :=
    if 2 * S.card ≤ Fintype.card X then S else Sᶜ
  have hTnonempty : T.Nonempty := by
    dsimp [T]
    split
    · exact hSnonempty
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hc
      apply hSproper
      have := congrArg (fun U : Finset X => Uᶜ) hc
      simpa using this
  have hThalf : 2 * T.card ≤ Fintype.card X := by
    dsimp [T]
    split
    · assumption
    · have hcard : (Sᶜ : Finset X).card =
          Fintype.card X - S.card := by
        simpa using Finset.card_compl S
      omega
  have hbound :=
    (isHalfEdgeExpander_iff rounds).mp hexp T
      (Finset.card_pos.mpr hTnonempty) hThalf
  have hboundaryPos : 0 < edgeBoundaryCount rounds T := by
    have hTpos := Finset.card_pos.mpr hTnonempty
    omega
  obtain ⟨R, hR, hRnonempty⟩ :=
    exists_round_boundary_of_edgeBoundaryCount_pos
      rounds T hboundaryPos
  obtain ⟨a, ha⟩ := hRnonempty
  have hadj :
      (roundListSupport rounds).Adj a.1
        (R.matching.rightEndpoint a) :=
    roundListSupport_adj_of_mem_edgeBoundary rounds T hR ha
  have hcross := LazyRound.mem_edgeBoundary.mp ha
  have hcrossS :
      (a.1 ∈ S ∧ R.matching.rightEndpoint a ∉ S) ∨
        (R.matching.rightEndpoint a ∈ S ∧ a.1 ∉ S) := by
    unfold LazyRound.edgeCrosses at hcross
    dsimp [T] at hcross
    split at hcross
    · exact hcross
    · simp only [Finset.mem_compl, not_not] at hcross
      tauto
  rcases hcrossS with hcrossS | hcrossS
  · have hreachA :
        (roundListSupport rounds).Reachable x a.1 := by
      simpa [S] using hcrossS.1
    have hreachTarget :
        (roundListSupport rounds).Reachable x
          (R.matching.rightEndpoint a) :=
      hreachA.trans hadj.reachable
    exact hcrossS.2 (by simpa [S] using hreachTarget)
  · have hreachTarget :
        (roundListSupport rounds).Reachable x
          (R.matching.rightEndpoint a) := by
      simpa [S] using hcrossS.1
    have hreachA :
        (roundListSupport rounds).Reachable x a.1 :=
      hreachTarget.trans hadj.symm.reachable
    exact hcrossS.2 (by simpa [S] using hreachA)

/-- Transport a matching source across equality of lazy rounds. -/
def transportRoundLeft
    {R Q : LazyRound X} (hRQ : R = Q)
    (a : {z : X // z ∈ R.cut.left}) :
    {z : X // z ∈ Q.cut.left} :=
  ⟨a.1, by simpa [hRQ] using a.2⟩

@[simp] theorem transportRoundLeft_val
    {R Q : LazyRound X} (hRQ : R = Q)
    (a : {z : X // z ∈ R.cut.left}) :
    (transportRoundLeft hRQ a).1 = a.1 := by
  rfl

@[simp] theorem rightEndpoint_transportRoundLeft
    {R Q : LazyRound X} (hRQ : R = Q)
    (a : {z : X // z ∈ R.cut.left}) :
    Q.matching.rightEndpoint (transportRoundLeft hRQ a) =
      R.matching.rightEndpoint a := by
  subst Q
  rfl

private theorem flatten_block_index_lt
    {α : Type*} (blocks : List (List α))
    (i : Fin blocks.length)
    (r : Fin (blocks.get i).length) :
    (blocks.take i.1).flatten.length + r.1 < blocks.flatten.length := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons block rest ih =>
      rcases i with ⟨i, hi⟩
      cases i with
      | zero =>
        have hr := r.2
        change r.1 < block.length at hr
        simp only [List.take_zero, List.flatten_nil, List.length_nil,
          zero_add, List.flatten_cons, List.length_append]
        omega
      | succ i =>
        let j : Fin rest.length := ⟨i, by simpa using hi⟩
        have hr : r.1 < (rest.get j).length := by
          simpa [j] using r.2
        have hrec :=
          ih j (⟨r.1, hr⟩ : Fin (rest.get j).length)
        simpa [j, List.flatten_cons, Nat.add_assoc] using
          Nat.add_lt_add_left hrec block.length

private theorem flatten_get_block
    {α : Type*} (blocks : List (List α))
    (i : Fin blocks.length)
    (r : Fin (blocks.get i).length) :
    blocks.flatten.get
        ⟨(blocks.take i.1).flatten.length + r.1,
          flatten_block_index_lt blocks i r⟩ =
      (blocks.get i).get r := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons block rest ih =>
      rcases i with ⟨i, hi⟩
      cases i with
      | zero =>
        simpa [List.flatten_cons] using
          (List.getElem_append_left
            (l₂ := rest.flatten) r.2)
      | succ i =>
        let j : Fin rest.length := ⟨i, by simpa using hi⟩
        have hr : r.1 < (rest.get j).length := by
          simpa [j] using r.2
        have hrec :=
          ih j (⟨r.1, hr⟩ : Fin (rest.get j).length)
        simpa [j, List.flatten_cons, Nat.add_assoc] using hrec

private theorem flatten_block_interval_unique
    {α : Type*} (blocks : List (List α))
    (hne : ∀ i : Fin blocks.length, 0 < (blocks.get i).length)
    (i k : Fin blocks.length)
    (r : Fin (blocks.get i).length)
    (s : Fin (blocks.get k).length)
    (heq :
      (blocks.take i.1).flatten.length + r.1 =
        (blocks.take k.1).flatten.length + s.1) :
    i = k := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons block rest ih =>
      rcases i with ⟨i, hi⟩
      rcases k with ⟨k, hk⟩
      cases i with
      | zero =>
        cases k with
        | zero => rfl
        | succ k =>
          have hr : r.1 < block.length := by
            simpa using r.2
          simp only [List.take_zero, List.flatten_nil, List.length_nil,
            zero_add, List.take_succ_cons, List.flatten_cons,
            List.length_append] at heq
          omega
      | succ i =>
        cases k with
        | zero =>
          have hs : s.1 < block.length := by
            simpa using s.2
          simp only [List.take_zero, List.flatten_nil, List.length_nil,
            zero_add, List.take_succ_cons, List.flatten_cons,
            List.length_append] at heq
          omega
        | succ k =>
          let i' : Fin rest.length := ⟨i, by simpa using hi⟩
          let k' : Fin rest.length := ⟨k, by simpa using hk⟩
          have hr : r.1 < (rest.get i').length := by
            simpa [i'] using r.2
          have hs : s.1 < (rest.get k').length := by
            simpa [k'] using s.2
          have hrest :
              (rest.take i).flatten.length + r.1 =
                (rest.take k).flatten.length + s.1 := by
            simp only [Fin.val_mk, List.take_succ_cons,
              List.flatten_cons, List.length_append] at heq
            omega
          have hneRest :
              ∀ z : Fin rest.length, 0 < (rest.get z).length := by
            intro z
            have :=
              hne
                (⟨z.1 + 1, by simpa using z.2⟩ :
                  Fin (block :: rest).length)
            simpa using this
          have hik :=
            ih hneRest i' k' ⟨r.1, hr⟩ ⟨s.1, hs⟩ hrest
          apply Fin.ext
          simpa [i', k'] using congrArg Fin.val hik

namespace BuildState.ExpanderBlocks


variable {V : Type v} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- Number of physical transcript records preceding block `i`. -/
def blockOffset (E : ExpanderBlocks P count) (i : Fin count) : ℕ :=
  ((List.ofFn E.rounds).take i.1).flatten.length

/-- The global physical-record index of local round `r` in block `i`. -/
def blockRecordIndex
    (E : ExpanderBlocks P count)
    (i : Fin count) (r : Fin (E.rounds i).length) :
    Fin E.finalState.records.length := by
  let blocks := List.ofFn E.rounds
  have hi : i.1 < blocks.length := by simp [blocks]
  let i' : Fin blocks.length := ⟨i.1, hi⟩
  have hblock : blocks.get i' = E.rounds i := by
    simp [blocks, i']
  let r' : Fin (blocks.get i').length :=
    ⟨r.1, by rw [hblock]; exact r.2⟩
  refine
    ⟨E.blockOffset i + r.1, ?_⟩
  rw [E.records_length_eq_flattened_length]
  simpa [blockOffset, blocks, i'] using
    flatten_block_index_lt blocks i' r'

@[simp] theorem blockRecordIndex_val
    (E : ExpanderBlocks P count)
    (i : Fin count) (r : Fin (E.rounds i).length) :
    (E.blockRecordIndex i r).1 = E.blockOffset i + r.1 := by
  simp [blockRecordIndex]

/-- A physical record belongs to a unique nonempty expander block. -/
theorem blockRecordIndex_block_unique
    (E : ExpanderBlocks P count)
    (hheight : 2 ≤ h)
    {i k : Fin count}
    {r : Fin (E.rounds i).length}
    {s : Fin (E.rounds k).length}
    (heq : E.blockRecordIndex i r = E.blockRecordIndex k s) :
    i = k := by
  let blocks := List.ofFn E.rounds
  have hne :
      ∀ z : Fin blocks.length, 0 < (blocks.get z).length := by
    intro z
    let z' : Fin count := ⟨z.1, by simpa [blocks] using z.2⟩
    simpa [blocks, z'] using E.rounds_nonempty hheight z'
  have hi : i.1 < blocks.length := by simp [blocks]
  have hk : k.1 < blocks.length := by simp [blocks]
  let i' : Fin blocks.length := ⟨i.1, hi⟩
  let k' : Fin blocks.length := ⟨k.1, hk⟩
  have hblockI : blocks.get i' = E.rounds i := by
    simp [blocks, i']
  have hblockK : blocks.get k' = E.rounds k := by
    simp [blocks, k']
  let r' : Fin (blocks.get i').length :=
    ⟨r.1, by rw [hblockI]; exact r.2⟩
  let s' : Fin (blocks.get k').length :=
    ⟨s.1, by rw [hblockK]; exact s.2⟩
  have hval := congrArg Fin.val heq
  have hik :=
    flatten_block_interval_unique blocks hne i' k' r' s'
      (by simpa [blockOffset, blocks, i', k', r', s'] using hval)
  apply Fin.ext
  simpa [i', k'] using congrArg Fin.val hik

/-- The record selected by `blockRecordIndex` is exactly the corresponding
lazy round of that block. -/
theorem blockRecordIndex_round
    (E : ExpanderBlocks P count)
    (i : Fin count) (r : Fin (E.rounds i).length) :
    (E.recordAt (E.blockRecordIndex i r)).round =
      (E.rounds i).get r := by
  let blocks := List.ofFn E.rounds
  have hi : i.1 < blocks.length := by simp [blocks]
  let i' : Fin blocks.length := ⟨i.1, hi⟩
  have hblock : blocks.get i' = E.rounds i := by
    simp [blocks, i']
  let r' : Fin (blocks.get i').length :=
    ⟨r.1, by rw [hblock]; exact r.2⟩
  have htrace := E.trace_eq
  change
    (E.finalState.records.get (E.blockRecordIndex i r)).round =
      (E.rounds i).get r
  have hget :=
    congrArg
      (fun xs : List (LazyRound (Fin h)) =>
        xs[E.blockOffset i + r.1]?)
      htrace
  have hflat :=
    flatten_get_block blocks i' r'
  have hleft :
      (BuildState.trace P E.finalState)[E.blockOffset i + r.1]? =
        some (E.recordAt (E.blockRecordIndex i r)).round := by
    rw [List.getElem?_eq_getElem]
    · simp [BuildState.trace, recordAt, E.blockRecordIndex_val]
    · simpa [BuildState.trace, E.blockRecordIndex_val] using
        (E.blockRecordIndex i r).2
  have hright :
      ((List.ofFn E.rounds).flatten)[E.blockOffset i + r.1]? =
        some ((E.rounds i).get r) := by
    rw [List.getElem?_eq_getElem]
    · simpa [blockOffset, blocks, i', hblock] using congrArg some hflat
    · simpa [blockOffset, blocks, i'] using
        flatten_block_index_lt blocks i' r'
  exact Option.some.inj (hleft.symm.trans (hget.trans hright))

/-- The global connector-gap index between local rounds `r` and `r+1` of
block `i`. -/
def blockGapIndex
    (E : ExpanderBlocks P count)
    (i : Fin count)
    (r : Fin ((E.rounds i).length - 1)) :
    Fin (E.finalState.records.length - 1) := by
  refine ⟨E.blockOffset i + r.1, ?_⟩
  have hnext :
      E.blockOffset i + (r.1 + 1) <
        E.finalState.records.length :=
    (E.blockRecordIndex i
      ⟨r.1 + 1, by omega⟩).2
  omega

@[simp] theorem blockGapIndex_val
    (E : ExpanderBlocks P count)
    (i : Fin count)
    (r : Fin ((E.rounds i).length - 1)) :
    (E.blockGapIndex i r).1 = E.blockOffset i + r.1 := by
  rfl

/-- An internal physical connector gap belongs to a unique nonempty block. -/
theorem blockGapIndex_block_unique
    (E : ExpanderBlocks P count)
    (hheight : 2 ≤ h)
    {i k : Fin count}
    {r : Fin ((E.rounds i).length - 1)}
    {s : Fin ((E.rounds k).length - 1)}
    (heq : E.blockGapIndex i r = E.blockGapIndex k s) :
    i = k := by
  let r' : Fin (E.rounds i).length := ⟨r.1, by omega⟩
  let s' : Fin (E.rounds k).length := ⟨s.1, by omega⟩
  apply E.blockRecordIndex_block_unique hheight
    (r := r') (s := s')
  apply Fin.ext
  simpa [r', s'] using congrArg Fin.val heq

@[simp] theorem gapRecord_blockGapIndex
    (E : ExpanderBlocks P count)
    (i : Fin count)
    (r : Fin ((E.rounds i).length - 1)) :
    E.gapRecord (E.blockGapIndex i r) =
      E.blockRecordIndex i ⟨r.1, by omega⟩ := by
  apply Fin.ext
  simp [gapRecord]

@[simp] theorem nextRecord_blockGapIndex
    (E : ExpanderBlocks P count)
    (i : Fin count)
    (r : Fin ((E.rounds i).length - 1)) :
    E.nextRecord (E.blockGapIndex i r) =
      E.blockRecordIndex i ⟨r.1 + 1, by omega⟩ := by
  apply Fin.ext
  simp [nextRecord, Nat.add_assoc]

/-- The physical support occupied by one independently restarted
cut-matching block.  It contains the local red/blue graph of every round in
the block and only the connector gaps internal to that block. -/
noncomputable def blockSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (i : Fin count) :
    _root_.SimpleGraph V :=
  (⨆ r : Fin (E.rounds i).length,
      (E.recordAt (E.blockRecordIndex i r)).layer.localGraph) ⊔
    (⨆ r : Fin ((E.rounds i).length - 1),
      (E.connectorAt hbudget
        (E.blockGapIndex i r)).toPathPacking.spanningGraph)

theorem record_localGraph_le_blockSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (i : Fin count) (r : Fin (E.rounds i).length) :
    (E.recordAt (E.blockRecordIndex i r)).layer.localGraph ≤
      E.blockSupport hbudget i :=
  (le_iSup
    (fun s : Fin (E.rounds i).length =>
      (E.recordAt (E.blockRecordIndex i s)).layer.localGraph) r).trans
    le_sup_left

theorem connector_le_blockSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (i : Fin count) (r : Fin ((E.rounds i).length - 1)) :
    (E.connectorAt hbudget
      (E.blockGapIndex i r)).toPathPacking.spanningGraph ≤
        E.blockSupport hbudget i :=
  (le_iSup
    (fun s : Fin ((E.rounds i).length - 1) =>
      (E.connectorAt hbudget
        (E.blockGapIndex i s)).toPathPacking.spanningGraph) r).trans
    le_sup_right

theorem blockSupport_le_assembledSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (i : Fin count) :
    E.blockSupport hbudget i ≤ E.assembledSupport hbudget := by
  classical
  apply sup_le
  · apply iSup_le
    intro r
    exact E.recordAt_localGraph_le_assembledSupport
      hbudget (E.blockRecordIndex i r)
  · apply iSup_le
    intro r
    exact
      (le_iSup
        (fun g : Fin (E.finalState.records.length - 1) =>
          (E.connectorAt hbudget g).toPathPacking.spanningGraph)
        (E.blockGapIndex i r)).trans
        (le_sup_right.trans le_sup_left)

private theorem localGraphs_common_adj_block_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    {i k : Fin count}
    {r : Fin (E.rounds i).length}
    {s : Fin (E.rounds k).length}
    {v w : V}
    (hri :
      (E.recordAt (E.blockRecordIndex i r)).layer.localGraph.Adj v w)
    (hsk :
      (E.recordAt (E.blockRecordIndex k s)).layer.localGraph.Adj v w) :
    i = k := by
  have hvI :
      v ∈ P.cluster
        (E.recordAt (E.blockRecordIndex i r)).index :=
    ((E.recordAt
      (E.blockRecordIndex i r)).layer.localGraph_le_induced hri).2.1
  have hvK :
      v ∈ P.cluster
        (E.recordAt (E.blockRecordIndex k s)).index :=
    ((E.recordAt
      (E.blockRecordIndex k s)).layer.localGraph_le_induced hsk).2.1
  have hindex :
      (E.recordAt (E.blockRecordIndex i r)).index =
        (E.recordAt (E.blockRecordIndex k s)).index := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvI hvK
  apply E.blockRecordIndex_block_unique hheight (r := r) (s := s)
  apply Fin.ext
  have hiOrdinal :=
    E.recordAt_index_eq hbudget (E.blockRecordIndex i r)
  have hkOrdinal :=
    E.recordAt_index_eq hbudget (E.blockRecordIndex k s)
  rw [← hiOrdinal, ← hkOrdinal]
  exact congrArg Fin.val hindex

private theorem connectorGraph_adj_has_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin (E.finalState.records.length - 1))
    {v w : V}
    (hvw :
      (E.connectorAt hbudget j).toPathPacking.spanningGraph.Adj v w) :
    ∃ a : (E.connectorAt hbudget j).Index,
      v ∈ ((E.connectorAt hbudget j).path a).vertexSet ∧
        w ∈ ((E.connectorAt hbudget j).path a).vertexSet := by
  rcases
      (PathPacking.spanningGraph_adj_iff_exists_path_edge
        (E.connectorAt hbudget j).toPathPacking).1 hvw with
    ⟨⟨a, he⟩, _hne⟩
  have hendpoints :=
    GraphPath.endpoints_mem_vertexSet_of_edgeSet
      ((E.connectorAt hbudget j).path a) he
  exact ⟨a, hendpoints.1, hendpoints.2⟩

private theorem connectorGraphs_common_adj_block_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    {i k : Fin count}
    {r : Fin ((E.rounds i).length - 1)}
    {s : Fin ((E.rounds k).length - 1)}
    {v w : V}
    (hri :
      (E.connectorAt hbudget
        (E.blockGapIndex i r)).toPathPacking.spanningGraph.Adj v w)
    (hsk :
      (E.connectorAt hbudget
        (E.blockGapIndex k s)).toPathPacking.spanningGraph.Adj v w) :
    i = k := by
  rcases E.connectorGraph_adj_has_path
      hbudget (E.blockGapIndex i r) hri with
    ⟨a, hva, _hwa⟩
  rcases E.connectorGraph_adj_has_path
      hbudget (E.blockGapIndex k s) hsk with
    ⟨b, hvb, _hwb⟩
  have hgap :
      E.blockGapIndex i r = E.blockGapIndex k s := by
    by_contra hne
    have hphysicalGap :
        E.gapIndex hbudget (E.blockGapIndex i r) ≠
          E.gapIndex hbudget (E.blockGapIndex k s) := by
      intro heq
      apply hne
      apply Fin.ext
      simpa [gapIndex] using congrArg Fin.val heq
    exact Finset.disjoint_left.mp
      (P.connector_mutually_nodeDisjoint
        (E.gapIndex_succ_lt hbudget (E.blockGapIndex i r))
        (E.gapIndex_succ_lt hbudget (E.blockGapIndex k s))
        hphysicalGap a b) hva hvb
  exact E.blockGapIndex_block_unique hheight hgap

private theorem localGraph_connectorGraph_not_common_adj
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (g : Fin (E.finalState.records.length - 1))
    {v w : V}
    (hlocal : (E.recordAt j).layer.localGraph.Adj v w)
    (hconnector :
      (E.connectorAt hbudget g).toPathPacking.spanningGraph.Adj v w) :
    False := by
  rcases E.connectorGraph_adj_has_path hbudget g hconnector with
    ⟨a, hva, hwa⟩
  have hvCluster :
      v ∈ P.cluster (E.recordAt j).index :=
    ((E.recordAt j).layer.localGraph_le_induced hlocal).2.1
  have hwCluster :
      w ∈ P.cluster (E.recordAt j).index :=
    ((E.recordAt j).layer.localGraph_le_induced hlocal).2.2
  have hvEndpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget g) (E.gapIndex_succ_lt hbudget g)
      (E.recordAt j).index a hva hvCluster
  have hwEndpoint :=
    P.connector_internally_disjoint_clusters
      (E.gapIndex hbudget g) (E.gapIndex_succ_lt hbudget g)
      (E.recordAt j).index a hwa hwCluster
  rcases hvEndpoint with hvSource | hvTarget <;>
    rcases hwEndpoint with hwSource | hwTarget
  · exact hlocal.ne (hvSource.trans hwSource.symm)
  · let next : Fin ell :=
      ⟨(E.gapIndex hbudget g).1 + 1,
        E.gapIndex_succ_lt hbudget g⟩
    have hvGap :
        v ∈ P.cluster (E.gapIndex hbudget g) := by
      apply P.right_subset_cluster
      simpa [hvSource] using (E.connectorAt hbudget g).source_mem a
    have hwNext : w ∈ P.cluster next := by
      apply P.left_subset_cluster
      simpa [next, hwTarget] using
        (E.connectorAt hbudget g).target_mem a
    have hjGap :
        (E.recordAt j).index = E.gapIndex hbudget g := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hvCluster hvGap
    have hjNext : (E.recordAt j).index = next := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hwCluster hwNext
    have := congrArg Fin.val (hjGap.symm.trans hjNext)
    simp [next] at this
  · let next : Fin ell :=
      ⟨(E.gapIndex hbudget g).1 + 1,
        E.gapIndex_succ_lt hbudget g⟩
    have hvNext : v ∈ P.cluster next := by
      apply P.left_subset_cluster
      simpa [next, hvTarget] using
        (E.connectorAt hbudget g).target_mem a
    have hwGap :
        w ∈ P.cluster (E.gapIndex hbudget g) := by
      apply P.right_subset_cluster
      simpa [hwSource] using (E.connectorAt hbudget g).source_mem a
    have hjNext : (E.recordAt j).index = next := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hvCluster hvNext
    have hjGap :
        (E.recordAt j).index = E.gapIndex hbudget g := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
        hwCluster hwGap
    have := congrArg Fin.val (hjGap.symm.trans hjNext)
    simp [next] at this
  · exact hlocal.ne (hvTarget.trans hwTarget.symm)

/-- The physical supports assigned to distinct independently restarted
blocks are edge-disjoint. -/
theorem blockSupport_common_adj_block_unique
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    {i k : Fin count} {v w : V}
    (hi : (E.blockSupport hbudget i).Adj v w)
    (hk : (E.blockSupport hbudget k).Adj v w) :
    i = k := by
  classical
  simp only [blockSupport, _root_.SimpleGraph.sup_adj,
    _root_.SimpleGraph.iSup_adj] at hi hk
  rcases hi with ⟨r, hir⟩ | ⟨r, hir⟩ <;>
    rcases hk with ⟨s, hks⟩ | ⟨s, hks⟩
  · exact E.localGraphs_common_adj_block_unique
      hbudget hheight hir hks
  · exact False.elim
      (E.localGraph_connectorGraph_not_common_adj
        hbudget (E.blockRecordIndex i r)
          (E.blockGapIndex k s) hir hks)
  · exact False.elim
      (E.localGraph_connectorGraph_not_common_adj
        hbudget (E.blockRecordIndex k s)
          (E.blockGapIndex i r) hks hir)
  · exact E.connectorGraphs_common_adj_block_unique
      hbudget hheight hir hks

/-- The occurrence of rail `x` at the first round of block `i`. -/
noncomputable def blockRailVertex
    (E : ExpanderBlocks P count)
    (hheight : 2 ≤ h)
    (i : Fin count) (x : Fin h) : V :=
  (E.localRedPath
    (E.blockRecordIndex i
      ⟨0, E.rounds_nonempty hheight i⟩) x).source

/-- Within one block, its first occurrence of a rail reaches that rail's
source in every later local round. -/
theorem blockRailVertex_reachable_recordSource
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    (i : Fin count) (x : Fin h)
    (r : Fin (E.rounds i).length) :
    (E.blockSupport hbudget i).Reachable
      (E.blockRailVertex hheight i x)
      (E.localRedPath (E.blockRecordIndex i r) x).source := by
  induction hn : r.1 using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hnzero : n = 0
    · have hrzero : r =
          ⟨0, E.rounds_nonempty hheight i⟩ := by
        apply Fin.ext
        simpa [hn] using hnzero
      subst r
      simp only [blockRailVertex]
      exact _root_.SimpleGraph.Reachable.refl _
    · let prev : Fin (E.rounds i).length :=
        ⟨n - 1, by omega⟩
      have hprev : prev.1 < n := by
        simp [prev]
        omega
      have ihprev :=
        ih prev.1 hprev prev (by simp [prev])
      let curr : Fin (E.rounds i).length :=
        ⟨prev.1 + 1, by omega⟩
      have hrPrevSucc : r = curr := by
        apply Fin.ext
        simp [curr, prev, hn]
        omega
      have hprevGap : prev.1 < (E.rounds i).length - 1 := by
        simp [prev]
        omega
      let gap : Fin ((E.rounds i).length - 1) :=
        ⟨prev.1, hprevGap⟩
      let localPath :=
        (E.localRedPath (E.blockRecordIndex i prev) x).mapLe
          (E.record_localGraph_le_blockSupport hbudget i prev)
      let connector :=
        ((E.connectorAt hbudget
              (E.blockGapIndex i gap)).toPathPacking.inSpanningGraph.path
            ((E.connectorAt hbudget (E.blockGapIndex i gap)).indexOfSource
              (E.connectorSource hbudget (E.blockGapIndex i gap) x))).mapLe
          (E.connector_le_blockSupport hbudget i gap)
      have hlocal :
          (E.blockSupport hbudget i).Reachable
            (E.localRedPath (E.blockRecordIndex i prev) x).source
            (E.localRedPath (E.blockRecordIndex i prev) x).target := by
        change
          (E.blockSupport hbudget i).Reachable
            localPath.source localPath.target
        exact localPath.walk.reachable
      have hconnector :
          (E.blockSupport hbudget i).Reachable
            (E.connectorPath hbudget (E.blockGapIndex i gap) x).source
            (E.connectorPath hbudget (E.blockGapIndex i gap) x).target := by
        simpa [connector, connectorPath, PathPacking.inSpanningGraph,
          PathPacking.transfer, GraphPath.mapLe, GraphPath.transfer] using
          connector.walk.reachable
      have hsource :
          (E.connectorPath hbudget
              (E.blockGapIndex i gap) x).source =
            (E.localRedPath
              (E.blockRecordIndex i prev) x).target := by
        rw [E.connectorPath_source, E.localRedPath_target,
          E.gapRecord_blockGapIndex]
      have htarget :
          (E.connectorPath hbudget
              (E.blockGapIndex i gap) x).target =
            (E.localRedPath
              (E.blockRecordIndex i curr) x).source := by
        rw [E.connectorPath_target, E.localRedPath_source,
          E.nextRecord_blockGapIndex]
      rw [hsource, htarget] at hconnector
      rw [hrPrevSucc]
      exact ihprev.trans (hlocal.trans hconnector)

/-- An abstract matching edge of a block is realized by a physical
connection between the corresponding first rail occurrences of that block. -/
theorem blockRailVertex_reachable_matchingEndpoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    (i : Fin count)
    (r : Fin (E.rounds i).length)
    (a :
      {z : Fin h //
        z ∈ (E.recordAt (E.blockRecordIndex i r)).cut.left}) :
    (E.blockSupport hbudget i).Reachable
      (E.blockRailVertex hheight i a.1)
      (E.blockRailVertex hheight i
        ((E.recordAt
          (E.blockRecordIndex i r)).round.matching.rightEndpoint a)) := by
  let j := E.blockRecordIndex i r
  let blue :=
    (E.localBluePath j a).mapLe
      (E.record_localGraph_le_blockSupport hbudget i r)
  have hblue :
      (E.blockSupport hbudget i).Reachable
        (E.localBluePath j a).source
        (E.localBluePath j a).target := by
    change
      (E.blockSupport hbudget i).Reachable blue.source blue.target
    exact blue.walk.reachable
  have hleft :=
    E.blockRailVertex_reachable_recordSource
      hbudget hheight i a.1 r
  have hright :=
    E.blockRailVertex_reachable_recordSource
      hbudget hheight i
        ((E.recordAt j).round.matching.rightEndpoint a) r
  have hblueSource :
      (E.localBluePath j a).source =
        (E.localRedPath j a.1).source := by
    rw [E.localBluePath_source, E.localRedPath_source]
  have hblueTarget :
      (E.localBluePath j a).target =
        (E.localRedPath j
          ((E.recordAt j).round.matching.rightEndpoint a)).source := by
    rw [E.localBluePath_target, E.localRedPath_source]
  rw [hblueSource, hblueTarget] at hblue
  exact hleft.trans (hblue.trans hright.symm)

/-- Abstract connectivity of a half-expander block lifts to connectivity of
its physical local-and-connector support. -/
theorem blockRailVertex_reachable
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    (i : Fin count) (x y : Fin h) :
    (E.blockSupport hbudget i).Reachable
      (E.blockRailVertex hheight i x)
      (E.blockRailVertex hheight i y) := by
  have habstract :=
    roundListSupport_reachable_of_halfExpander
      (E.each_halfExpander i) (by simpa using hheight) x y
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at habstract
  induction habstract with
  | refl =>
      exact _root_.SimpleGraph.Reachable.refl _
  | @tail u v huv hvw ih =>
      rcases hvw.2 with ⟨R, hR, a, hxy⟩
      obtain ⟨r, hr⟩ := List.get_of_mem hR
      subst R
      let hround :
          (E.recordAt (E.blockRecordIndex i r)).round =
            (E.rounds i).get r :=
        E.blockRecordIndex_round i r
      let a' :=
        transportRoundLeft hround.symm a
      have hphysical :=
        E.blockRailVertex_reachable_matchingEndpoint
          hbudget hheight i r a'
      change
        (E.blockSupport hbudget i).Reachable
          (E.blockRailVertex hheight i
            (transportRoundLeft hround.symm a).1)
          (E.blockRailVertex hheight i
            ((E.recordAt
              (E.blockRecordIndex i r)).round.matching.rightEndpoint
                (transportRoundLeft hround.symm a))) at hphysical
      rw [transportRoundLeft_val,
        rightEndpoint_transportRoundLeft] at hphysical
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans hphysical
      · exact ih.trans hphysical.symm

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
