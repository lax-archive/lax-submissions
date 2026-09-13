import Lax17Proofs.Source.GenericCutMatchingBudget

namespace Lax17Proofs

universe u v w

/-!
# Stateful cut-matching transcripts

The cut player used in Theorem 5.1 of Chekuri--Chuzhoy must interact with a
physical construction whose state changes after every round: the red linkage
in one path-of-sets cluster transports the current labelling to the next
cluster.  A `SequentialResponder` cannot expose that state.  This file proves
the same logarithmic cut-matching guarantee for a responder which returns both
a matching and a new state.

No new cut-matching argument is needed.  For one phase, the stateful play is
definitionally the ordinary sparse-cut play against the responder obtained by
recomputing the state before round `n`.  The existing entropy theorem therefore
applies to every phase.  Sixteen phases and the existing final peeling round
give a half-edge-expander exactly as in `GenericCutMatchingTranscript`.
-/

namespace SimpleGraph
namespace CutMatchingGame


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- One matching-player reply together with the state used by the next
round. -/
structure StatefulReply (State : Type v) (B : Bisection X) where
  matching : MatchingAcross B
  next : State

/-- A matching-player strategy which may carry arbitrary construction data
between rounds. -/
def StatefulResponder (State : Type v) (X : Type u)
    [Fintype X] [DecidableEq X] : Type (max u v) :=
  ∀ _round : ℕ, State → (B : Bisection X) → StatefulReply State B

/-- A state projection records the generated rounds exactly when every reply
appends its own cut and matching. -/
def TracksRounds {State : Type v}
    (responder : StatefulResponder State X)
    (trace : State → List (LazyRound X)) : Prop :=
  ∀ round state B,
    trace (responder round state B).next =
      trace state ++ [{
        cut := B
        matching := (responder round state B).matching
      }]

/-- One sparse-cut phase, threading the responder state.  The `offset`
parameter is the global round number of the first round of this phase. -/
noncomputable def statefulSparseCutPlay
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset : ℕ) :
    ℕ → State → State × List (LazyRound X)
  | 0, state => (state, [])
  | k + 1, state =>
      let previous :=
        statefulSparseCutPlay cNum cDen m hm responder offset k state
      let currentState := previous.1
      let rounds := previous.2
      if h : SparseCutAvailable (X := X) cNum cDen rounds then
        let B := SparseCutAvailable.toBisection (X := X) hm h
        let reply := responder (offset + k) currentState B
        (reply.next, rounds ++ [{ cut := B, matching := reply.matching }])
      else
        let B := arbitraryBisection (X := X) hm
        let reply := responder (offset + k) currentState B
        (reply.next, rounds ++ [{ cut := B, matching := reply.matching }])

@[simp] theorem statefulSparseCutPlay_zero
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset : ℕ) (state : State) :
    statefulSparseCutPlay (X := X) cNum cDen m hm responder offset 0 state =
      (state, []) := rfl

theorem statefulSparseCutPlay_length
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset k : ℕ) (state : State) :
    (statefulSparseCutPlay (X := X) cNum cDen m hm responder offset k state).2.length =
      k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold statefulSparseCutPlay
      by_cases h :
          SparseCutAvailable (X := X) cNum cDen
            (statefulSparseCutPlay (X := X) cNum cDen m hm responder offset k state).2
      · simp [h, ih]
      · simp [h, ih]

/-- Exact trace equation for one stateful phase. -/
theorem statefulSparseCutPlay_trace
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X)
    (trace : State → List (LazyRound X))
    (htrace : TracksRounds responder trace)
    (offset k : ℕ) (state : State) :
    trace (statefulSparseCutPlay (X := X)
      cNum cDen m hm responder offset k state).1 =
      trace state ++
        (statefulSparseCutPlay (X := X)
          cNum cDen m hm responder offset k state).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      unfold statefulSparseCutPlay
      by_cases h :
          SparseCutAvailable (X := X) cNum cDen
            (statefulSparseCutPlay (X := X)
              cNum cDen m hm responder offset k state).2
      · simp only [h, dite_true]
        rw [htrace, ih, List.append_assoc]
      · simp only [h, dite_false]
        rw [htrace, ih, List.append_assoc]

/-- Forget the state update by recomputing the state reached before the
requested local round.  This is the ordinary responder against which the
stateful phase has exactly the same transcript. -/
noncomputable def replayResponder
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset : ℕ) (initial : State) :
    SequentialResponder X :=
  fun round B =>
    (responder (offset + round)
      (statefulSparseCutPlay (X := X)
        cNum cDen m hm responder offset round initial).1 B).matching

/-- A stateful sparse-cut phase erases to the ordinary sparse-cut play against
its replay responder. -/
theorem statefulSparseCutPlay_rounds_eq_sparseCutPlay
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset k : ℕ) (state : State) :
    (statefulSparseCutPlay (X := X)
      cNum cDen m hm responder offset k state).2 =
      sparseCutPlay (X := X) cNum cDen m hm
        (replayResponder (X := X)
          cNum cDen m hm responder offset state) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [statefulSparseCutPlay, sparseCutPlay]
      by_cases h :
          SparseCutAvailable (X := X) cNum cDen
            (sparseCutPlay (X := X) cNum cDen m hm
              (replayResponder (X := X)
                cNum cDen m hm responder offset state) k)
      · simp only [ih, h, dite_true, replayResponder, LazyRound.ofResponder]
        congr
      · simp only [ih, h, dite_false, replayResponder, LazyRound.ofResponder]

/-- One stateful phase inherits the ordinary entropy-based balanced-expander
guarantee. -/
theorem statefulSparseCutPlay_balancedExpander_one_four_of_potential_budget
    {State : Type v} {cNum cDen m : ℕ}
    (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (offset k : ℕ) (state : State)
    (hden : 0 < cDen) (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X cNum cDen * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (statefulSparseCutPlay (X := X)
        cNum cDen m hm responder offset k state).2
      cNum cDen 1 4 := by
  rw [statefulSparseCutPlay_rounds_eq_sparseCutPlay]
  exact sparseCutPlay_balancedExpander_one_four_of_potential_budget
    (X := X) hm
    (replayResponder (X := X)
      cNum cDen m hm responder offset state)
    k hden hn hbudget

/-- Repeat independent sparse-cut phases while retaining the construction
state between phases. -/
noncomputable def statefulSparseCutPlayMany
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (k : ℕ) :
    ℕ → State → State × List (LazyRound X)
  | 0, state => (state, [])
  | phase + 1, state =>
      let previous :=
        statefulSparseCutPlayMany cNum cDen m hm responder k phase state
      let block :=
        statefulSparseCutPlay cNum cDen m hm responder (phase * k) k previous.1
      (block.1, previous.2 ++ block.2)

@[simp] theorem statefulSparseCutPlayMany_zero
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (k : ℕ) (state : State) :
    statefulSparseCutPlayMany (X := X)
      cNum cDen m hm responder k 0 state = (state, []) := rfl

theorem statefulSparseCutPlayMany_length
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (k phase : ℕ) (state : State) :
    (statefulSparseCutPlayMany (X := X)
      cNum cDen m hm responder k phase state).2.length = phase * k := by
  induction phase with
  | zero => simp
  | succ phase ih =>
      unfold statefulSparseCutPlayMany
      rw [List.length_append, ih,
        statefulSparseCutPlay_length (X := X)]
      rw [Nat.succ_mul]

/-- Exact trace equation across all stateful phases. -/
theorem statefulSparseCutPlayMany_trace
    {State : Type v}
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X)
    (trace : State → List (LazyRound X))
    (htrace : TracksRounds responder trace)
    (k phase : ℕ) (state : State) :
    trace (statefulSparseCutPlayMany (X := X)
      cNum cDen m hm responder k phase state).1 =
      trace state ++
        (statefulSparseCutPlayMany (X := X)
          cNum cDen m hm responder k phase state).2 := by
  induction phase generalizing state with
  | zero => simp
  | succ phase ih =>
      unfold statefulSparseCutPlayMany
      let previous :=
        statefulSparseCutPlayMany (X := X)
          cNum cDen m hm responder k phase state
      let block :=
        statefulSparseCutPlay (X := X)
          cNum cDen m hm responder (phase * k) k previous.1
      calc
        trace block.1 =
            trace previous.1 ++ block.2 := by
              simpa [block] using
                statefulSparseCutPlay_trace (X := X)
                  cNum cDen m hm responder trace htrace
                  (phase * k) k previous.1
        _ = (trace state ++ previous.2) ++ block.2 := by
              rw [show trace previous.1 =
                trace state ++ previous.2 by
                  simpa [previous] using ih (state := state)]
        _ = trace state ++ (previous.2 ++ block.2) := by
              rw [List.append_assoc]

/-- `phase` stateful entropy phases have balanced expansion
`phase / 4`. -/
theorem statefulSparseCutPlayMany_balancedExpander
    {State : Type v} {m k phase : ℕ}
    (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (state : State)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (statefulSparseCutPlayMany (X := X)
        1 4 m hm responder k phase state).2
      1 4 phase 4 := by
  induction phase generalizing state with
  | zero =>
      refine ⟨by decide, ?_⟩
      intro T _hlarge _hhalf
      simp
  | succ phase ih =>
      unfold statefulSparseCutPlayMany
      let previous :=
        statefulSparseCutPlayMany (X := X)
          1 4 m hm responder k phase state
      let block :=
        statefulSparseCutPlay (X := X)
          1 4 m hm responder (phase * k) k previous.1
      have hprevious :
          IsBalancedEdgeExpanderWith (X := X)
            previous.2 1 4 phase 4 := by
        simpa [previous] using ih (state := state)
      have hblock :
          IsBalancedEdgeExpanderWith (X := X)
            block.2 1 4 1 4 := by
        simpa [block] using
          statefulSparseCutPlay_balancedExpander_one_four_of_potential_budget
            (X := X) hm responder (phase * k) k previous.1
              (by decide) hn hbudget
      simpa [previous, block, Nat.succ_eq_add_one] using
        balancedEdgeExpanderWith_append_same_den
          (X := X) hprevious hblock

/-- Sixteen stateful phases have balanced expansion at least four. -/
theorem statefulSparseCutPlayMany_balancedExpander_four
    {State : Type v} {m k : ℕ}
    (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (state : State)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (statefulSparseCutPlayMany (X := X)
        1 4 m hm responder k 16 state).2
      1 4 4 1 := by
  have h :=
    statefulSparseCutPlayMany_balancedExpander
      (X := X) hm responder state hn hbudget (phase := 16)
  refine ⟨by decide, ?_⟩
  intro T hlarge hhalf
  have hbound := h.2 T hlarge hhalf
  omega

/-- Sixteen stateful phases followed by the final peeling bisection give a
half-edge-expander and the final construction state. -/
theorem exists_stateful_list_halfExpander
    {State : Type v} {m : ℕ}
    (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X) (state : State) (k : ℕ)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    ∃ (finalState : State) (rounds : List (LazyRound X)),
      rounds.length = 16 * k + 1 ∧ IsHalfEdgeExpander rounds := by
  let phaseResult :=
    statefulSparseCutPlayMany (X := X)
      1 4 m hm responder k 16 state
  let phaseRounds := phaseResult.2
  have hbalanced :
      IsBalancedEdgeExpanderWith (X := X) phaseRounds 1 4 4 1 := by
    simpa [phaseResult, phaseRounds] using
      statefulSparseCutPlayMany_balancedExpander_four
        (X := X) hm responder state hn hbudget
  let finalResponder : SequentialResponder X :=
    fun _round B => (responder (16 * k) phaseResult.1 B).matching
  rcases exists_final_bisection_halfExpander_of_balancedExpander_four
      (X := X) (rounds := phaseRounds) hm hbalanced hn
      finalResponder 0 with
    ⟨B, hhalf⟩
  let reply := responder (16 * k) phaseResult.1 B
  let finalRound : LazyRound X := {
    cut := B
    matching := reply.matching
  }
  have hround :
      LazyRound.ofResponder finalResponder 0 B = finalRound := by
    rfl
  refine ⟨reply.next, phaseRounds ++ [finalRound], ?_, ?_⟩
  · have hlen :
        phaseRounds.length = 16 * k := by
      simpa [phaseResult, phaseRounds] using
        statefulSparseCutPlayMany_length
          (X := X) 1 4 m hm responder k 16 state
    simp [hlen]
  · simpa [hround] using hhalf

/-- The preceding construction with an exact equation for a caller-supplied
round trace. -/
theorem exists_stateful_list_halfExpander_with_trace
    {State : Type v} {m : ℕ}
    (hm : 2 * m = Fintype.card X)
    (responder : StatefulResponder State X)
    (trace : State → List (LazyRound X))
    (htrace : TracksRounds responder trace)
    (state : State) (k : ℕ)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    ∃ (finalState : State) (rounds : List (LazyRound X)),
      rounds.length = 16 * k + 1 ∧
        IsHalfEdgeExpander rounds ∧
          trace finalState = trace state ++ rounds := by
  let phaseResult :=
    statefulSparseCutPlayMany (X := X)
      1 4 m hm responder k 16 state
  let phaseRounds := phaseResult.2
  have hbalanced :
      IsBalancedEdgeExpanderWith (X := X) phaseRounds 1 4 4 1 := by
    simpa [phaseResult, phaseRounds] using
      statefulSparseCutPlayMany_balancedExpander_four
        (X := X) hm responder state hn hbudget
  let finalResponder : SequentialResponder X :=
    fun _round B => (responder (16 * k) phaseResult.1 B).matching
  rcases exists_final_bisection_halfExpander_of_balancedExpander_four
      (X := X) (rounds := phaseRounds) hm hbalanced hn
      finalResponder 0 with
    ⟨B, hhalf⟩
  let reply := responder (16 * k) phaseResult.1 B
  let finalRound : LazyRound X := {
    cut := B
    matching := reply.matching
  }
  have hround :
      LazyRound.ofResponder finalResponder 0 B = finalRound := by
    rfl
  have hphaseTrace :
      trace phaseResult.1 = trace state ++ phaseRounds := by
    simpa [phaseResult, phaseRounds] using
      statefulSparseCutPlayMany_trace (X := X)
        1 4 m hm responder trace htrace k 16 state
  refine ⟨reply.next, phaseRounds ++ [finalRound], ?_, ?_, ?_⟩
  · have hlen :
        phaseRounds.length = 16 * k := by
      simpa [phaseResult, phaseRounds] using
        statefulSparseCutPlayMany_length
          (X := X) 1 4 m hm responder k 16 state
    simp [hlen]
  · simpa [hround] using hhalf
  · rw [show trace reply.next =
      trace phaseResult.1 ++ [finalRound] by
        simpa [reply, finalRound] using
          htrace (16 * k) phaseResult.1 B]
    rw [hphaseTrace, List.append_assoc]

/-- Universal logarithmic round budget for stateful cut matching. -/
theorem exists_generic_log_round_halfExpander_stateful :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {X : Type u} [Fintype X] [DecidableEq X]
        {State : Type v} {k : ℕ},
        1 < k → 0 < Fintype.card X → Even (Fintype.card X) →
          Fintype.card X ≤ k →
            ∀ (responder : StatefulResponder State X) (state : State),
              ∃ (finalState : State) (rounds : List (LazyRound X)),
                rounds.length ≤ cRound * Nat.log 2 k ∧
                  IsHalfEdgeExpander rounds := by
  rcases exists_phaseRoundConstant with ⟨C, hCpos, hC⟩
  refine ⟨16 * C + 1, by omega, ?_⟩
  intro X _ _ State k hk hn heven hnk responder state
  let L := Nat.log 2 k
  let phaseLength := C * L
  have hLpos : 0 < L :=
    Nat.log_pos (by decide : 1 < 2) hk
  rcases heven with ⟨m, hm⟩
  have hm' : 2 * m = Fintype.card X := by omega
  have hlog :=
    real_log_card_le_two_natLog_of_card_le (X := X) hk hn hnk
  have hright :
      2 * (L : ℝ) <
        entropyGapConstant * (phaseLength : ℝ) / 32 := by
    have hphaseCast :
        (phaseLength : ℝ) = (C : ℝ) * (L : ℝ) := by
      simp [phaseLength]
    rw [hphaseCast]
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hLpos
    have hgap_pos : 0 < entropyGapConstant := entropyGapConstant_pos
    nlinarith
  have hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (phaseLength : ℝ) := by
    unfold sparseCutRoundIncrement
    norm_num
    have hlog' :
        Real.log (Fintype.card X : ℝ) ≤ 2 * (L : ℝ) := by
      simpa [L] using hlog
    have hnR : 0 < (Fintype.card X : ℝ) := by exact_mod_cast hn
    nlinarith
  rcases exists_stateful_list_halfExpander
      (X := X) hm' responder state phaseLength hn hbudget with
    ⟨finalState, rounds, hlen, hhalf⟩
  refine ⟨finalState, rounds, ?_, hhalf⟩
  rw [hlen]
  dsimp [phaseLength]
  nlinarith

/-- A named universal phase constant, independent of the graph and of all
type universes. -/
noncomputable def universalPhaseRoundConstant : ℕ :=
  Classical.choose exists_phaseRoundConstant

theorem universalPhaseRoundConstant_pos :
    0 < universalPhaseRoundConstant :=
  (Classical.choose_spec exists_phaseRoundConstant).1

theorem universalPhaseRoundConstant_gap :
    64 <
      entropyGapConstant * (universalPhaseRoundConstant : ℝ) :=
  (Classical.choose_spec exists_phaseRoundConstant).2

/-- The corresponding explicit universal logarithmic round multiplier. -/
noncomputable def universalRoundConstant : ℕ :=
  16 * universalPhaseRoundConstant + 1

theorem universalRoundConstant_pos :
    0 < universalRoundConstant := by
  unfold universalRoundConstant
  omega

/-- Logarithmic stateful cut matching with a named, universe-independent
round constant and exact caller trace provenance. -/
theorem universalRoundConstant_spec :
    ∀ {X : Type u} [Fintype X] [DecidableEq X]
      {State : Type v} {k : ℕ},
      1 < k → 0 < Fintype.card X → Even (Fintype.card X) →
        Fintype.card X ≤ k →
          ∀ (responder : StatefulResponder State X)
            (trace : State → List (LazyRound X)),
            TracksRounds responder trace →
              ∀ state : State,
                ∃ (finalState : State) (rounds : List (LazyRound X)),
                  rounds.length ≤ universalRoundConstant * Nat.log 2 k ∧
                    IsHalfEdgeExpander rounds ∧
                      trace finalState = trace state ++ rounds := by
  intro X _ _ State k hk hn heven hnk responder trace htrace state
  let C := universalPhaseRoundConstant
  have hC : 64 < entropyGapConstant * (C : ℝ) := by
    exact universalPhaseRoundConstant_gap
  let L := Nat.log 2 k
  let phaseLength := C * L
  have hLpos : 0 < L :=
    Nat.log_pos (by decide : 1 < 2) hk
  rcases heven with ⟨m, hm⟩
  have hm' : 2 * m = Fintype.card X := by omega
  have hlog :=
    real_log_card_le_two_natLog_of_card_le (X := X) hk hn hnk
  have hright :
      2 * (L : ℝ) <
        entropyGapConstant * (phaseLength : ℝ) / 32 := by
    have hphaseCast :
        (phaseLength : ℝ) = (C : ℝ) * (L : ℝ) := by
      simp [phaseLength]
    rw [hphaseCast]
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hLpos
    have hgap_pos : 0 < entropyGapConstant := entropyGapConstant_pos
    nlinarith
  have hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (phaseLength : ℝ) := by
    unfold sparseCutRoundIncrement
    norm_num
    have hlog' :
        Real.log (Fintype.card X : ℝ) ≤ 2 * (L : ℝ) := by
      simpa [L] using hlog
    have hnR : 0 < (Fintype.card X : ℝ) := by exact_mod_cast hn
    nlinarith
  rcases exists_stateful_list_halfExpander_with_trace
      (X := X) hm' responder trace htrace state phaseLength hn hbudget with
    ⟨finalState, rounds, hlen, hhalf, hrounds⟩
  refine ⟨finalState, rounds, ?_, hhalf, hrounds⟩
  rw [hlen]
  dsimp [phaseLength]
  unfold universalRoundConstant
  nlinarith

/-- Existential wrapper retained for source-facing clients. -/
theorem exists_generic_log_round_halfExpander_stateful_with_trace :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {X : Type u} [Fintype X] [DecidableEq X]
        {State : Type v} {k : ℕ},
        1 < k → 0 < Fintype.card X → Even (Fintype.card X) →
          Fintype.card X ≤ k →
            ∀ (responder : StatefulResponder State X)
              (trace : State → List (LazyRound X)),
              TracksRounds responder trace →
                ∀ state : State,
                  ∃ (finalState : State) (rounds : List (LazyRound X)),
                    rounds.length ≤ cRound * Nat.log 2 k ∧
                      IsHalfEdgeExpander rounds ∧
                        trace finalState = trace state ++ rounds :=
  ⟨universalRoundConstant, universalRoundConstant_pos,
    universalRoundConstant_spec⟩

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
