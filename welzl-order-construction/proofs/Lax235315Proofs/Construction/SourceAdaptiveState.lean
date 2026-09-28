import Lax235315Proofs.Construction.HistoryRoundSource
import Lax235315Proofs.Construction.GuardedAdaptiveProtocol
import Lax235315Proofs.Construction.GuardedArithmetic
import Lax235315Proofs.Construction.RoundPotential
import Lax235315Proofs.Construction.AdaptiveMachineBridge

/-! Canonical round-boundary source states for an adaptive tape tree.  The
input field is empty; each fresh block is appended only while executing the
next literal source round. -/

namespace Lax235315Proofs.Construction.SourceAdaptiveState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.GuardedAdaptiveProtocol
open Lax235315Proofs.Construction.GraphAdaptiveProtocol
open Lax235315Proofs.Construction.PositionFailureBounds
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.HistoryRoundSource
open Lax235315Proofs.Construction.RoundPotential
open Lax235315Proofs.Construction.AdaptiveStateProtocol
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.AdaptiveBitBlocks
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.AdaptiveMachineBridge
open Lax11.GraphEncoding
open Lax195003.WordRamRandomness

structure RoundState (c n : ℕ) (x : List ℕ)
    (G : SimpleGraph (Fin n)) where
  env : Env
  nontrivial : 1 < n
  frontier : Frontier (sourceBound c x) c n x env
  history : Stored G (6 * c ^ 2 * Nat.clog 2 n) env
  square : env.vars "csq" = c ^ 2
  nearBound : env.vars "nearBound" = 6 * c ^ 2 * Nat.clog 2 n
  threshold : env.vars "threshold" = 12 * c ^ 2 * Nat.clog 2 n
  large : 12 * c ^ 2 * Nat.clog 2 n < env.vars "acount"
  emptyInput : env.inp = []

def withInput (σ : Env) (input : List ℕ) : Env :=
  {σ with inp := input}

/-- Replacing only unread source bits leaves the graph frontier unchanged,
provided the replacement tape is binary and fits the source word bound. -/
lemma frontier_withInput {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ) (input : List ℕ)
    (hfit : ∀ v ∈ input, v < B)
    (hbits : ∀ v ∈ input, v ≤ 1) :
    Frontier B c n x (withInput σ input) := by
  have hw : Workspace B c n x (withInput σ input) :=
    ⟨⟨h.workspace.bounded.vars, h.workspace.bounded.arrays, hfit⟩,
      h.workspace.parameter, h.workspace.vertices, h.workspace.edges,
      h.workspace.logarithm, h.workspace.radixSize,
      h.workspace.offsets, h.workspace.targets, h.workspace.lengths,
      hbits, h.workspace.output⟩
  exact ⟨hw, h.success, h.activeCount, h.nonemptyA, h.nonemptyB,
    h.activeABits, h.activeBBits, h.nextABits, h.nextBBits,
    h.conservation, h.shrinking⟩

def stored_withInput {n k : ℕ} {G : SimpleGraph (Fin n)}
    {σ : Env} (h : Stored G k σ) (input : List ℕ) :
    Stored G k (withInput σ input) := by
  exact h.frame rfl rfl rfl rfl rfl rfl rfl rfl

def withBlock {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (s : RoundState c n x G) {K : ℕ} (bits : Fin K → Bool) : Env :=
  withInput s.env (bitTape bits)

lemma bitTape_binary {K : ℕ} (bits : Fin K → Bool) :
    ∀ v ∈ bitTape bits, v ≤ 1 := by
  intro v hv
  simp only [bitTape, List.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  split <;> omega

lemma frontier_withBlock {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    {K : ℕ} (bits : Fin K → Bool)
    (hB : 2 < sourceBound c x) :
    Frontier (sourceBound c x) c n x (withBlock s bits) := by
  apply frontier_withInput s.frontier (bitTape bits)
  · intro v hv
    have hvbit := bitTape_binary bits v hv
    omega
  · exact bitTape_binary bits

def stored_withBlock {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    {K : ℕ} (bits : Fin K → Bool) :
    Stored G (6 * c ^ 2 * Nat.clog 2 n) (withBlock s bits) :=
  stored_withInput s.history (bitTape bits)

def toGuardedState {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (s : RoundState c n x G) : GuardedState n c (Nat.clog 2 n) := by
  refine ⟨⟨view s.env "activeA", view s.env "activeB", ?_⟩, ?_⟩
  · apply Finset.card_pos.mp
    rw [activeFinset_card_eq_activeVertices]
    have hn : 0 < n := by have := s.nontrivial; omega
    exact Finset.card_pos.mpr (s.frontier.nonemptyA hn)
  · rw [← s.frontier.activeCount]
    exact s.large

@[simp] lemma guarded_activeA {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G) :
    (toGuardedState s).activeA = view s.env "activeA" := rfl

@[simp] lemma guarded_activeB {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G) :
    (toGuardedState s).activeB = view s.env "activeB" := rfl

lemma query_width_eq_source_block {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G) :
    GuardedAdaptiveProtocol.width (some (toGuardedState s)) =
      8 * Nat.clog 2 n * s.env.vars "acount" := by
  simp only [GuardedAdaptiveProtocol.width,
    GraphAdaptiveProtocol.queryWidth, guarded_activeA]
  rw [s.frontier.activeCount]
  ring

lemma square_le_vertices {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G) : c ^ 2 ≤ n := by
  have hL : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) s.nontrivial
  have hmul : 12 * c ^ 2 ≤ 12 * c ^ 2 * Nat.clog 2 n := by
    nlinarith
  have hcount : s.env.vars "acount" ≤ n := by
    rw [s.frontier.activeCount]
    exact activeVertices_card_le _ _
  have hsmall : c ^ 2 ≤ 12 * c ^ 2 := by omega
  exact (hsmall.trans hmul).trans ((Nat.le_of_lt s.large).trans hcount)

/-- A canonical state executes exactly one complete source round when fed a
block of the query width.  The resulting input is empty, so it is again a
round boundary. -/
lemma round_on_block {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c)
    (bits : Fin (width (some (toGuardedState s))) → Bool) :
    ∃ τ, Run (sourceBound c x) reductionRound (withBlock s bits) τ
        (4500 * (x.length + 1) + 120 * Nat.clog 2 n * s.env.vars "acount") ∧
      τ.inp = [] ∧
      ((Frontier (sourceBound c x) c n x τ ∧
        τ.vars "round" = s.env.vars "round" + 1 ∧
        τ.vars "acount" ≤ s.env.vars "acount" / 2 + c ^ 2 ∧
        Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) τ)) ∨
        (τ.vars "good" ≠ 1 ∧ τ.vars "acount" = 0)) := by
  obtain ⟨_, _, _, hqB, hnB, htargetB, _, hdenomB⟩ :=
    source_fits_of_square_le hx hc s.nontrivial (square_le_vertices s)
  have hboundB : 6 * c ^ 2 * Nat.clog 2 n < sourceBound c x := by
    have hcount : s.env.vars "acount" ≤ n := by
      rw [s.frontier.activeCount]
      exact activeVertices_card_le _ _
    have hnB' : n < sourceBound c x := by
      simpa only [s.frontier.workspace.vertices] using
        s.frontier.workspace.bounded.vars "n"
    have hthresholdB : 12 * c ^ 2 * Nat.clog 2 n < sourceBound c x :=
      lt_trans (lt_of_lt_of_le s.large hcount) hnB'
    have hhalf : 6 * c ^ 2 * Nat.clog 2 n ≤
        12 * c ^ 2 * Nat.clog 2 n := by nlinarith
    exact lt_of_le_of_lt hhalf hthresholdB
  have hfront := frontier_withBlock s bits (by dsimp [sourceBound]; omega)
  have hwidth : (bitTape bits).length =
      8 * Nat.clog 2 n * s.env.vars "acount" := by
    simpa [query_width_eq_source_block s] using
      (Lax235315Proofs.Construction.RandomKeyEquiv.bitTape_length bits)
  obtain ⟨τ, hr, _, hinp, hout⟩ :=
    reductionRound_run_stored hx hG hfront (stored_withBlock s bits)
      hc s.nontrivial s.large s.square s.nearBound
      (by simpa [withBlock, withInput, hwidth])
      hqB hnB htargetB hdenomB hboundB
  refine ⟨τ, ?_, ?_, hout⟩
  · simpa [withBlock, withInput] using hr
  · simpa [withBlock, withInput, ← hwidth] using hinp

/-- An accepted source round that remains above the stopping threshold has
all fields needed for another canonical adaptive query. -/
def afterAcceptedRound {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    {bits : Fin (width (some (toGuardedState s))) → Bool} {τ : Env}
    (hr : Run (sourceBound c x) reductionRound (withBlock s bits) τ
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * s.env.vars "acount"))
    (hfront : Frontier (sourceBound c x) c n x τ)
    (hstore : Stored G (6 * c ^ 2 * Nat.clog 2 n) τ)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < τ.vars "acount")
    (hempty : τ.inp = []) : RoundState c n x G := by
  refine ⟨τ, s.nontrivial, hfront, hstore, ?_, ?_, ?_, hlarge, hempty⟩
  · exact (hr.frame_var "csq" (by decide)).trans (by simpa [withBlock, withInput] using s.square)
  · exact (hr.frame_var "nearBound" (by decide)).trans
      (by simpa [withBlock, withInput] using s.nearBound)
  · exact (hr.frame_var "threshold" (by decide)).trans
      (by simpa [withBlock, withInput] using s.threshold)

def Accepted {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (s : RoundState c n x G) (τ : Env) : Prop :=
  Frontier (sourceBound c x) c n x τ ∧
    τ.vars "round" = s.env.vars "round" + 1 ∧
    τ.vars "acount" ≤ s.env.vars "acount" / 2 + c ^ 2 ∧
    Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) τ)

noncomputable def roundOutput {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c)
    (bits : Fin (width (some (toGuardedState s))) → Bool) : Env :=
  Classical.choose (round_on_block s hx hG hc bits)

lemma roundOutput_spec {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c)
    (bits : Fin (width (some (toGuardedState s))) → Bool) :
    Run (sourceBound c x) reductionRound (withBlock s bits)
      (roundOutput s hx hG hc bits)
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * s.env.vars "acount") ∧
    (roundOutput s hx hG hc bits).inp = [] ∧
    (Accepted s (roundOutput s hx hG hc bits) ∨
      ((roundOutput s hx hG hc bits).vars "good" ≠ 1 ∧
        (roundOutput s hx hG hc bits).vars "acount" = 0)) := by
  exact Classical.choose_spec (round_on_block s hx hG hc bits)

def sourceWidth {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} :
    Option (RoundState c n x G) → ℕ
  | none => 0
  | some s => width (some (toGuardedState s))

noncomputable def nextState {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) :
    ∀ state : Option (RoundState c n x G),
      (Fin (sourceWidth state) → Bool) → Option (RoundState c n x G)
  | none, _ => none
  | some s, bits => by
      classical
      exact
      let τ := roundOutput s hx hG hc bits
      if h : Accepted s τ ∧ 12 * c ^ 2 * Nat.clog 2 n < τ.vars "acount" then
        some (afterAcceptedRound s (roundOutput_spec s hx hG hc bits).1
          h.1.1 (Classical.choice h.1.2.2.2) h.2
          (roundOutput_spec s hx hG hc bits).2.1)
      else none

@[simp] lemma nextState_none {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (bits : Fin (sourceWidth (none : Option (RoundState c n x G))) → Bool) :
    nextState hx hG hc none bits = none := rfl

lemma nextState_shrinks {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (s : RoundState c n x G)
    (bits : Fin (sourceWidth (some s)) → Bool)
    (s' : RoundState c n x G)
    (hnext : nextState hx hG hc (some s) bits = some s') :
    (activeVertices n (view s'.env "activeA")).card ≤
      (activeVertices n (view s.env "activeA")).card / 2 + c ^ 2 := by
  classical
  dsimp [nextState] at hnext
  split_ifs at hnext with haccepted
  · cases hnext
    change (activeVertices n (view (roundOutput s hx hG hc bits) "activeA")).card ≤
      (activeVertices n (view s.env "activeA")).card / 2 + c ^ 2
    rw [← haccepted.1.1.activeCount, ← s.frontier.activeCount]
    exact haccepted.1.2.2.1

noncomputable def sourceBad {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (hL : 0 < Nat.clog 2 n) :
    ∀ state : Option (RoundState c n x G), Finset (Fin (sourceWidth state) → Bool)
  | none => ∅
  | some s => badBlock G c (Nat.clog 2 n) hL (toGuardedState s).toGraphQueryState

def sourcePotential {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} : Option (RoundState c n x G) → ℕ
  | none => 0
  | some s => 24 * Nat.clog 2 n *
      (activeVertices n (view s.env "activeA")).card

lemma source_step_pays_bits {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) :
    ∀ state bits, sourceWidth state +
      sourcePotential (nextState hx hG hc state bits) ≤ sourcePotential state := by
  intro state bits
  cases state with
  | none => simp [sourceWidth, sourcePotential, nextState]
  | some s =>
      cases hnext : nextState hx hG hc (some s) bits with
      | none =>
          simp [sourceWidth, sourcePotential, query_width_eq_source_block s, hnext]
          rw [← s.frontier.activeCount]
          nlinarith
      | some s' =>
          have hshrink := nextState_shrinks hx hG hc s bits s' hnext
          rw [← s.frontier.activeCount] at hshrink
          have hpay := bit_reserve_step
            (Nat.clog_pos (by omega) s.nontrivial) s.large hshrink
          rw [s.frontier.activeCount] at hpay
          have hwidth : sourceWidth (some s) =
              8 * Nat.clog 2 n *
                (activeVertices n (view s.env "activeA")).card := by
            rw [show sourceWidth (some s) =
              8 * Nat.clog 2 n * s.env.vars "acount" from
              query_width_eq_source_block s, s.frontier.activeCount]
          simpa [sourcePotential, hnext, hwidth,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpay

lemma locallyBounded_source {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hNpow : n ≤ 2 ^ Nat.clog 2 n)
    (hL : 0 < Nat.clog 2 n) :
    ∀ R state, LocallyBounded
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n)
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R state) := by
  apply AdaptiveStateProtocol.locallyBounded
    (width := sourceWidth) (bad := sourceBad (G := G) (x := x) (c := c) hL)
    (next := nextState hx hG hc)
  intro state
  cases state with
  | none =>
      simp [sourceBad, sourceWidth]
      positivity
  | some s =>
      simpa [sourceBad, sourceWidth, width, queryWidth, badBlock] using
        (badRoundBits_fraction_le (view s.env "activeA")
          (view s.env "activeB") hc (toGuardedState s).nonemptyA hG hNpow hL)

lemma source_maxConsumedBits_le_tape {c n T : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hreserve : 24 * Nat.clog 2 n * n ≤ T)
    (hL : 0 < Nat.clog 2 n) :
    ∀ R s, maxConsumedBits
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R (some s)) ≤ T := by
  intro R s
  have hstep := source_step_pays_bits hx hG hc
  have hbits := AdaptiveStateProtocol.maxConsumedBits_le_potential
    (width := sourceWidth) (bad := sourceBad (G := G) (x := x) (c := c) hL)
    (next := nextState hx hG hc) sourcePotential hstep R (some s)
  have hcount := activeVertices_card_le n (view s.env "activeA")
  have hmul := Nat.mul_le_mul_left (24 * Nat.clog 2 n) hcount
  exact hbits.trans (hmul.trans hreserve)

lemma source_success_count_of_good_paths {c n T : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hNpow : n ≤ 2 ^ Nat.clog 2 n)
    (hreserve : 24 * Nat.clog 2 n * n ≤ T)
    (hbudget : (Nat.clog 2 n : ℚ) *
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n) ≤ 1 / 3)
    (start : RoundState c n x G) (good : Set (Fin T → Bool))
    (hsuccess : ∀ ρ,
      ρ ∉ failingTapes
        (protocol sourceWidth
          (sourceBad (G := G) (x := x) (c := c)
            (Nat.clog_pos (by omega) start.nontrivial))
          (nextState hx hG hc) (Nat.clog 2 n) (some start)) T
        (fits_of_maxConsumedBits _ T
          (source_maxConsumedBits_le_tape hx hG hc hreserve
            (Nat.clog_pos (by omega) start.nontrivial) _ start)) → ρ ∈ good) :
    (2 / 3 : ℚ) * 2 ^ T ≤ (good.ncard : ℚ) := by
  let ε : ℚ := 1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n
  let p := protocol sourceWidth
    (sourceBad (G := G) (x := x) (c := c)
      (Nat.clog_pos (by omega) start.nontrivial))
    (nextState hx hG hc) (Nat.clog 2 n) (some start)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hlocal : LocallyBounded ε p :=
    locallyBounded_source hx hG hc hNpow
      (Nat.clog_pos (by omega) start.nontrivial) _ _
  have hbits : maxConsumedBits p ≤ T :=
    source_maxConsumedBits_le_tape hx hG hc hreserve
      (Nat.clog_pos (by omega) start.nontrivial) _ _
  exact success_count_of_protocol p ε hε hlocal hbits hbudget good hsuccess

end Lax235315Proofs.Construction.SourceAdaptiveState
