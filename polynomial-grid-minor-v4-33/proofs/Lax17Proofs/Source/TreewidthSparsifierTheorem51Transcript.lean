import Lax17Proofs.Source.StatefulCutMatchingTranscript
import Lax17Proofs.Source.TreewidthSparsifierTheorem51Layers

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: the physical cut-matching transcript

This is the adaptive part of Step 1 in Theorem 5.1.  The state remembers the
current physical labelling of the abstract rail set.  A reply selects the
Theorem 1.3 layer in the current cluster, records its abstract round, and
transports the labelling through the red paths and the next connector.

The state saturates only after the last cluster.  Consequently every recorded
round whose ordinal is below the path-of-sets length is realized in the cluster
with exactly that ordinal.  Under the eventual width bound, all rounds have
that form.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h : ℕ}

/-- One realized round of Step 1, retaining its physical red and blue
routings. -/
structure RecordedLayer
    (P : StrongPathOfSetsSystem G ell h) where
  ordinal : ℕ
  index : Fin ell
  index_eq_ordinal : ordinal < ell → index.1 = ordinal
  label : Fin h ≃ {v : V // v ∈ P.left index}
  cut : Bisection (Fin h)
  layer : Layer P index label cut

namespace RecordedLayer

variable {P : StrongPathOfSetsSystem G ell h}

/-- The abstract cut-matching round represented by a physical layer. -/
noncomputable def round (R : RecordedLayer P) : LazyRound (Fin h) where
  cut := R.cut
  matching := R.layer.matching

@[simp] theorem round_cut (R : RecordedLayer P) :
    R.round.cut = R.cut := rfl

@[simp] theorem round_matching (R : RecordedLayer P) :
    R.round.matching = R.layer.matching := rfl

end RecordedLayer

/-- A proof-relevant history of the physical replies used to build a state.

The list of records alone remembers the chosen layers, but not that consecutive
labels are related by the red routing and the intervening path-of-sets
connector.  This inductive invariant records exactly that relation.  The
`stay` constructor is the total-responder fallback at the last cluster; the
cluster-budget lemma later rules it out on the source-relevant prefix. -/
inductive BuildHistory
    (P : StrongPathOfSetsSystem G ell h) :
    (index : Fin ell) →
      (label : Fin h ≃ {v : V // v ∈ P.left index}) →
        List (RecordedLayer P) → Prop
  | initial
      (label : Fin h ≃ {v : V // v ∈ P.left P.firstIndex}) :
      BuildHistory P P.firstIndex label []
  | advance
      {index : Fin ell}
      {label : Fin h ≃ {v : V // v ∈ P.left index}}
      {records : List (RecordedLayer P)}
      (history : BuildHistory P index label records)
      (B : Bisection (Fin h))
      (L : Layer P index label B)
      (hindex : records.length < ell → index.1 = records.length)
      (hi : index.1 + 1 < ell) :
      BuildHistory P
        ⟨index.1 + 1, hi⟩
        (L.nextLabel hi)
        (records ++ [{
          ordinal := records.length
          index := index
          index_eq_ordinal := hindex
          label := label
          cut := B
          layer := L
        }])
  | stay
      {index : Fin ell}
      {label : Fin h ≃ {v : V // v ∈ P.left index}}
      {records : List (RecordedLayer P)}
      (history : BuildHistory P index label records)
      (B : Bisection (Fin h))
      (L : Layer P index label B)
      (hindex : records.length < ell → index.1 = records.length)
      (hi : ¬ index.1 + 1 < ell) :
      BuildHistory P index label
        (records ++ [{
          ordinal := records.length
          index := index
          index_eq_ordinal := hindex
          label := label
          cut := B
          layer := L
        }])

/-- The current labelling either advances through the red paths and connector
of the last record, or is the total-responder fallback at the final cluster. -/
def LabelContinues
    {P : StrongPathOfSetsSystem G ell h}
    (R : RecordedLayer P)
    (index : Fin ell)
    (label : Fin h ≃ {v : V // v ∈ P.left index}) : Prop :=
  (∃ hi : R.index.1 + 1 < ell,
      index.1 = R.index.1 + 1 ∧
        ∀ x : Fin h,
          (label x).1 = (R.layer.nextLabel hi x).1) ∨
    (index = R.index ∧
      ∀ x : Fin h, (label x).1 = (R.label x).1)

/-- Consecutive physical records have compatible rail labels. -/
def RecordFollows
    {P : StrongPathOfSetsSystem G ell h}
    (R S : RecordedLayer P) : Prop :=
  LabelContinues R S.index S.label

/-- State threaded through the physical cut-matching game.  The cluster index
is the smaller of the number of completed rounds and the last cluster index. -/
structure BuildState
    (P : StrongPathOfSetsSystem G ell h) where
  index : Fin ell
  label : Fin h ≃ {v : V // v ∈ P.left index}
  records : List (RecordedLayer P)
  record_ordinals :
    records.map RecordedLayer.ordinal = List.range records.length
  index_eq_min :
    index.1 = min records.length (ell - 1)
  history :
    BuildHistory P index label records
  records_follow :
    List.IsChain RecordFollows records
  current_continues_last :
    ∀ R ∈ records.getLast?,
      LabelContinues R index label

namespace BuildState

variable (P : StrongPathOfSetsSystem G ell h)

/-- A canonical initial labelling of the first left nail set. -/
noncomputable def initialLabel :
    Fin h ≃ {v : V // v ∈ P.left P.firstIndex} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, P.left_card])

/-- Initial state before any cluster has been used. -/
noncomputable def initial : BuildState P where
  index := P.firstIndex
  label := initialLabel P
  records := []
  record_ordinals := by simp
  index_eq_min := by simp
  history := BuildHistory.initial (initialLabel P)
  records_follow := List.IsChain.nil
  current_continues_last := by simp

/-- The abstract transcript stored in the construction state. -/
noncomputable def trace (state : BuildState P) :
    List (LazyRound (Fin h)) :=
  state.records.map RecordedLayer.round

variable {P}

private theorem index_eq_records_length_of_lt
    (state : BuildState P) (hlt : state.records.length < ell) :
    state.index.1 = state.records.length := by
  rw [state.index_eq_min]
  have hle : state.records.length ≤ ell - 1 := by omega
  exact Nat.min_eq_left hle

private theorem next_index_eq_min
    (state : BuildState P) (hi : state.index.1 + 1 < ell) :
    state.index.1 + 1 =
      min (state.records.length + 1) (ell - 1) := by
  have hindex_lt_last : state.index.1 < ell - 1 := by omega
  have hrecords_eq : state.records.length = state.index.1 := by
    have hmin_lt :
        min state.records.length (ell - 1) < ell - 1 := by
      simpa [← state.index_eq_min] using hindex_lt_last
    have hrecords_lt : state.records.length < ell - 1 := by
      by_contra hnot
      have hlast_le : ell - 1 ≤ state.records.length :=
        Nat.le_of_not_gt hnot
      rw [Nat.min_eq_right hlast_le] at hmin_lt
      omega
    rw [state.index_eq_min, Nat.min_eq_left hrecords_lt.le]
  rw [hrecords_eq]
  exact (Nat.min_eq_left (by omega)).symm

private theorem stay_index_eq_min
    (state : BuildState P) (hi : ¬ state.index.1 + 1 < ell) :
    state.index.1 =
      min (state.records.length + 1) (ell - 1) := by
  have hlast : state.index.1 = ell - 1 := by
    have hle : state.index.1 ≤ ell - 1 := by
      have := state.index.isLt
      omega
    omega
  have hrecords_ge : ell - 1 ≤ state.records.length := by
    by_contra hnot
    have hrecords_lt : state.records.length < ell - 1 :=
      Nat.lt_of_not_ge hnot
    have hmin :
        min state.records.length (ell - 1) = state.records.length :=
      Nat.min_eq_left hrecords_lt.le
    rw [state.index_eq_min, hmin] at hlast
    omega
  rw [Nat.min_eq_right (by omega), hlast]

/-- One physical reply.  When another cluster is available, the red routing
and connector determine the next labelling.  At the final cluster the state is
kept total by retaining the current labelling; the width hypothesis later
shows that this fallback is never used before the returned transcript ends. -/
noncomputable def reply
    (state : BuildState P) (B : Bisection (Fin h)) :
    StatefulReply (BuildState P) B := by
  let L : Layer P state.index state.label B :=
    Classical.choice (Layer.exists_layer P state.index state.label B)
  let R : RecordedLayer P := {
    ordinal := state.records.length
    index := state.index
    index_eq_ordinal := fun hlt =>
      index_eq_records_length_of_lt state hlt
    label := state.label
    cut := B
    layer := L
  }
  by_cases hi : state.index.1 + 1 < ell
  · exact {
      matching := L.matching
      next := {
        index := ⟨state.index.1 + 1, hi⟩
        label := L.nextLabel hi
        records := state.records ++ [R]
        record_ordinals := by
          simp [state.record_ordinals, List.range_succ, R]
        index_eq_min := by
          simpa using next_index_eq_min state hi
        history := by
          simpa [R] using
            BuildHistory.advance state.history B L
              (index_eq_records_length_of_lt state) hi
        records_follow := by
          apply state.records_follow.append (List.IsChain.singleton R)
          intro old hold new hnew
          have hnew_eq : new = R := by simpa using hnew.symm
          subst new
          exact state.current_continues_last old hold
        current_continues_last := by
          intro old hold
          have hold_eq : old = R := by simpa using hold.symm
          subst old
          exact Or.inl ⟨hi, rfl, fun _ => rfl⟩
      }
    }
  · exact {
      matching := L.matching
      next := {
        index := state.index
        label := state.label
        records := state.records ++ [R]
        record_ordinals := by
          simp [state.record_ordinals, List.range_succ, R]
        index_eq_min := by
          simpa using stay_index_eq_min state hi
        history := by
          simpa [R] using
            BuildHistory.stay state.history B L
              (index_eq_records_length_of_lt state) hi
        records_follow := by
          apply state.records_follow.append (List.IsChain.singleton R)
          intro old hold new hnew
          have hnew_eq : new = R := by simpa using hnew.symm
          subst new
          exact state.current_continues_last old hold
        current_continues_last := by
          intro old hold
          have hold_eq : old = R := by simpa using hold.symm
          subst old
          exact Or.inr ⟨rfl, fun _ => rfl⟩
      }
    }

/-- The physical stateful matching responder. -/
noncomputable def responder :
    StatefulResponder (BuildState P) (Fin h) :=
  fun _round state B => reply state B

@[simp] theorem reply_records
    (state : BuildState P) (B : Bisection (Fin h)) :
    (reply state B).next.records =
      state.records ++ [{
        ordinal := state.records.length
        index := state.index
        index_eq_ordinal := fun hlt =>
          index_eq_records_length_of_lt state hlt
        label := state.label
        cut := B
        layer := Classical.choice
          (Layer.exists_layer P state.index state.label B)
      }] := by
  classical
  unfold reply
  dsimp only
  by_cases hi : state.index.1 + 1 < ell <;> simp [hi]

@[simp] theorem reply_matching
    (state : BuildState P) (B : Bisection (Fin h)) :
    (reply state B).matching =
      (Classical.choice
        (Layer.exists_layer P state.index state.label B)).matching := by
  classical
  unfold reply
  dsimp only
  by_cases hi : state.index.1 + 1 < ell <;> simp [hi]

/-- The stored physical records are exactly the abstract rounds generated by
the stateful cut player. -/
theorem responder_tracksRounds :
    TracksRounds (responder (P := P)) (trace P) := by
  classical
  intro round state B
  simp [responder, trace, reply_records, RecordedLayer.round,
    reply_matching]

/-- The universal round constant supplied by the generic stateful
cut-matching theorem.  Naming this witness before specializing to a host
graph keeps every width and well-linkedness constant graph-independent. -/
noncomputable def realizedRoundConstant : ℕ :=
  universalRoundConstant

theorem realizedRoundConstant_pos :
    0 < realizedRoundConstant := by
  exact universalRoundConstant_pos

theorem realizedRoundConstant_spec :
    ∀ {X : Type u} [Fintype X] [DecidableEq X]
      {State : Type v} {k : ℕ},
      1 < k → 0 < Fintype.card X → Even (Fintype.card X) →
        Fintype.card X ≤ k →
          ∀ (responder : StatefulResponder State X)
            (trace : State → List (LazyRound X)),
            TracksRounds responder trace →
              ∀ state : State,
                ∃ (finalState : State) (rounds : List (LazyRound X)),
                  rounds.length ≤
                      realizedRoundConstant * Nat.log 2 k ∧
                    IsHalfEdgeExpander rounds ∧
                      trace finalState = trace state ++ rounds :=
  universalRoundConstant_spec

/-- Execute the logarithmic cut-matching game and retain every realizing
layer. -/
theorem exists_realized_halfExpander_from_state :
    0 < realizedRoundConstant ∧
      ∀ (P : StrongPathOfSetsSystem G ell h),
        1 < h →
          Even h →
            ∀ initialState : BuildState P,
              ∃ (finalState : BuildState P)
                (rounds : List (LazyRound (Fin h))),
                rounds.length ≤
                    realizedRoundConstant * Nat.log 2 h ∧
                  IsHalfEdgeExpander rounds ∧
                    trace P finalState =
                      trace P initialState ++ rounds := by
  refine ⟨realizedRoundConstant_pos, ?_⟩
  intro P hh heven initialState
  have hcardpos : 0 < Fintype.card (Fin h) := by
    simpa using (show 0 < h by omega)
  exact realizedRoundConstant_spec hh hcardpos (by simpa using heven)
    (by simp) (responder (P := P)) (trace P)
    (responder_tracksRounds (P := P)) initialState

/-- Execute the logarithmic cut-matching game from the canonical first
labelling. -/
theorem exists_realized_halfExpander :
    0 < realizedRoundConstant ∧
      ∀ (P : StrongPathOfSetsSystem G ell h),
        1 < h →
          Even h →
            ∃ (finalState : BuildState P)
              (rounds : List (LazyRound (Fin h))),
              rounds.length ≤
                  realizedRoundConstant * Nat.log 2 h ∧
                IsHalfEdgeExpander rounds ∧
                  trace P finalState = rounds := by
  rcases exists_realized_halfExpander_from_state
      (G := G) (ell := ell) (h := h) with
    ⟨hcRound, hgame⟩
  refine ⟨hcRound, ?_⟩
  intro P hh heven
  rcases hgame P hh heven (initial P) with
    ⟨finalState, rounds, hlen, hhalf, htrace⟩
  refine ⟨finalState, rounds, hlen, hhalf, ?_⟩
  simpa [trace, initial] using htrace

/-- A sequence of independently restarted cut-matching games.  The physical
responder state is not restarted: red paths continue transporting the labels
through the next path-of-sets clusters. -/
structure ExpanderBlocks
    (P : StrongPathOfSetsSystem G ell h) (count : ℕ) where
  finalState : BuildState P
  rounds : Fin count → List (LazyRound (Fin h))
  each_halfExpander : ∀ i, IsHalfEdgeExpander (rounds i)
  each_length_le :
    ∀ i, (rounds i).length ≤
      realizedRoundConstant * Nat.log 2 h
  trace_eq :
    trace P finalState =
      (List.ofFn rounds).flatten

namespace ExpanderBlocks

variable (P : StrongPathOfSetsSystem G ell h)

/-- The flattened abstract transcript has the expected sum-of-block-lengths
bound. -/
theorem flattened_length_le
    {count : ℕ} (E : ExpanderBlocks P count) :
    (List.ofFn E.rounds).flatten.length ≤
      count *
        (realizedRoundConstant * Nat.log 2 h) := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    (∑ i : Fin count, (E.rounds i).length) ≤
        ∑ _i : Fin count,
          realizedRoundConstant * Nat.log 2 h :=
      Finset.sum_le_sum fun i _hi => E.each_length_le i
    _ = count *
          (realizedRoundConstant * Nat.log 2 h) := by simp

/-- The physical record list and flattened abstract transcript have the same
length. -/
theorem records_length_eq_flattened_length
    {count : ℕ} (E : ExpanderBlocks P count) :
    E.finalState.records.length =
      (List.ofFn E.rounds).flatten.length := by
  have hlen := congrArg List.length E.trace_eq
  simpa [BuildState.trace] using hlen

/-- A width budget for all restarted games ensures that every stored physical
layer is realized in the cluster with its exact ordinal; the saturating
fallback in `reply` is therefore unreachable. -/
theorem record_index_eq_ordinal_of_budget
    {count : ℕ} (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    {R : RecordedLayer P} (hR : R ∈ E.finalState.records) :
    R.index.1 = R.ordinal := by
  apply R.index_eq_ordinal
  have hord : R.ordinal < E.finalState.records.length := by
    have hmap :
        R.ordinal ∈
          E.finalState.records.map RecordedLayer.ordinal :=
      List.mem_map.mpr ⟨R, hR, rfl⟩
    rw [E.finalState.record_ordinals] at hmap
    simpa using hmap
  calc
    R.ordinal < E.finalState.records.length := hord
    _ = (List.ofFn E.rounds).flatten.length :=
      E.records_length_eq_flattened_length
    _ ≤ count *
          (realizedRoundConstant * Nat.log 2 h) :=
      E.flattened_length_le
    _ ≤ ell := hbudget

/-- Boundary counts add across the independently restarted expander blocks. -/
theorem edgeBoundaryCount_flatten_eq_sum
    {count : ℕ} (E : ExpanderBlocks P count) (S : Finset (Fin h)) :
    edgeBoundaryCount (List.ofFn E.rounds).flatten S =
      ∑ i : Fin count, edgeBoundaryCount (E.rounds i) S := by
  have hlist :
      ∀ blocks : List (List (LazyRound (Fin h))),
        edgeBoundaryCount blocks.flatten S =
          (blocks.map fun rounds => edgeBoundaryCount rounds S).sum := by
    intro blocks
    induction blocks with
    | nil => rfl
    | cons rounds rest ih =>
        simp only [List.flatten_cons, List.map_cons, List.sum_cons]
        rw [edgeBoundaryCount_append, ih]
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def]

/-- `count` half-expanders contribute `count/2` edge expansion in their
flattened multigraph. -/
theorem count_mul_card_le_two_mul_edgeBoundaryCount
    {count : ℕ} (E : ExpanderBlocks P count)
    (S : Finset (Fin h)) (hS : 0 < S.card)
    (hhalf : 2 * S.card ≤ h) :
    count * S.card ≤
      2 * edgeBoundaryCount (List.ofFn E.rounds).flatten S := by
  have heach :
      ∀ i : Fin count,
        S.card ≤ 2 * edgeBoundaryCount (E.rounds i) S := by
    intro i
    apply (CutMatchingGame.isHalfEdgeExpander_iff (E.rounds i)).mp
      (E.each_halfExpander i) S hS
    simpa using hhalf
  rw [E.edgeBoundaryCount_flatten_eq_sum]
  calc
    count * S.card = ∑ _i : Fin count, S.card := by simp
    _ ≤ ∑ i : Fin count,
          2 * edgeBoundaryCount (E.rounds i) S :=
      Finset.sum_le_sum fun i _hi => heach i
    _ = 2 * ∑ i : Fin count,
          edgeBoundaryCount (E.rounds i) S := by
      rw [Finset.mul_sum]

/-- Build any prescribed number of expander blocks while retaining the exact
concatenated physical trace. -/
theorem nonempty
    (hh : 1 < h) (heven : Even h) :
    ∀ count : ℕ, Nonempty (ExpanderBlocks P count) := by
  intro count
  induction count with
  | zero =>
      exact ⟨{
        finalState := initial P
        rounds := fun i => Fin.elim0 i
        each_halfExpander := fun i => Fin.elim0 i
        each_length_le := fun i => Fin.elim0 i
        trace_eq := by simp [trace, initial]
      }⟩
  | succ count ih =>
      rcases ih with ⟨previous⟩
      have hcRoundSpec :=
        exists_realized_halfExpander_from_state
          (G := G) (ell := ell) (h := h)
      have hgame :=
        hcRoundSpec.2 P hh heven previous.finalState
      rcases hgame with
        ⟨nextState, lastRounds, hlastLength, hlastHalf, hlastTrace⟩
      let allRounds : Fin (count + 1) → List (LazyRound (Fin h)) :=
        Fin.snoc previous.rounds lastRounds
      refine ⟨{
        finalState := nextState
        rounds := allRounds
        each_halfExpander := ?_
        each_length_le := ?_
        trace_eq := ?_
      }⟩
      · intro i
        cases i using Fin.lastCases with
        | last =>
            simpa [allRounds] using hlastHalf
        | cast j =>
            simpa [allRounds] using previous.each_halfExpander j
      · intro i
        cases i using Fin.lastCases with
        | last =>
            simpa [allRounds] using hlastLength
        | cast j =>
            simpa [allRounds] using previous.each_length_le j
      · have hlist :
            List.ofFn allRounds =
              List.ofFn previous.rounds ++ [lastRounds] := by
          rw [List.ofFn_succ']
          simp [allRounds]
        rw [hlastTrace, previous.trace_eq, hlist, List.flatten_append]
        simp

end ExpanderBlocks

end BuildState

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
