import Lax235315Proofs.Construction.HistoryRoundSource
import Lax235315Proofs.Construction.GuardedAdaptiveProtocol
import Lax235315Proofs.Construction.GuardedArithmetic
import Lax235315Proofs.Construction.RoundPotential
import Lax235315Proofs.Construction.AdaptiveMachineBridge
import Lax235315Proofs.Construction.InputSuffixFrame
import Lax235315Proofs.Construction.RationalFailureBounds
import Lax235315Proofs.Construction.HistoryDriverSource

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
open Lax235315Proofs.Construction.InputSuffixFrame
open Lax235315.ConstructionContracts
open Lax235315Proofs.Construction.RationalFailureBounds
open Lax235315Proofs.Construction.HistoryDriverSource
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.DriverFinish
open Lax235315Proofs.Construction.GuardedDriverSource
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

lemma Accepted.good {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    {s : RoundState c n x G} {τ : Env} (h : Accepted s τ) :
    τ.vars "good" = 1 := h.1.success

lemma Accepted.withBitTape {c n K : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {s : RoundState c n x G} {τ : Env}
    (h : Accepted s τ) (tail : Fin K → Bool) :
    Accepted s (withInput τ (bitTape tail)) := by
  have hB : 2 < sourceBound c x := by dsimp [sourceBound]; omega
  have hfront := frontier_withInput h.1 (bitTape tail)
    (by intro v hv; have := bitTape_binary tail v hv; omega)
    (bitTape_binary tail)
  refine ⟨hfront, ?_, ?_, ?_⟩
  · simpa [withInput] using h.2.1
  · simpa [withInput] using h.2.2.1
  · obtain ⟨hstore⟩ := h.2.2.2
    exact ⟨stored_withInput hstore (bitTape tail)⟩

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

lemma roundOutput_on_tail {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c)
    (bits : Fin (width (some (toGuardedState s))) → Bool)
    (tail : List ℕ) :
    Run (sourceBound c x) reductionRound
      (withInput s.env (bitTape bits ++ tail))
      (withInput (roundOutput s hx hG hc bits) tail)
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * s.env.vars "acount") := by
  have hs := roundOutput_spec s hx hG hc bits
  have hr := run_on_any_tail_after_exact_prefix hs.1 hs.2.1 tail
  simpa [withBlock, withInput] using hr

lemma loopTest_withInput {B c n : ℕ} {x : List ℕ}
    {σ : Env} (h : Frontier B c n x σ) (tail : List ℕ) :
    (Cond.lt (.var "threshold") (.var "acount")).evalB B (withInput σ tail) =
      some (decide (σ.vars "threshold" < σ.vars "acount")) := by
  have ht : (Expr.var "threshold").evalB B (withInput σ tail) =
      some (σ.vars "threshold") := by
    simpa [withInput] using
      (evalB_var (h.workspace.bounded.vars "threshold"))
  have ha : (Expr.var "acount").evalB B (withInput σ tail) =
      some (σ.vars "acount") := by
    simpa [withInput] using
      (evalB_var (h.workspace.bounded.vars "acount"))
  rw [evalB_condLt ht ha]

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

lemma nextState_some_env {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (s : RoundState c n x G)
    (bits : Fin (sourceWidth (some s)) → Bool)
    (s' : RoundState c n x G)
    (hnext : nextState hx hG hc (some s) bits = some s') :
    s'.env = roundOutput s hx hG hc bits := by
  classical
  dsimp [nextState] at hnext
  split_ifs at hnext with haccepted
  · cases hnext
    rfl

lemma nextState_some_round {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (s : RoundState c n x G)
    (bits : Fin (sourceWidth (some s)) → Bool)
    (s' : RoundState c n x G)
    (hnext : nextState hx hG hc (some s) bits = some s') :
    s'.env.vars "round" = s.env.vars "round" + 1 := by
  classical
  dsimp [nextState] at hnext
  split_ifs at hnext with haccepted
  · cases hnext
    exact haccepted.1.2.1

lemma nextState_stops_after_accepted {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (s : RoundState c n x G)
    (bits : Fin (sourceWidth (some s)) → Bool)
    (haccept : Accepted s (roundOutput s hx hG hc bits))
    (hnext : nextState hx hG hc (some s) bits = none) :
    (roundOutput s hx hG hc bits).vars "acount" ≤
      12 * c ^ 2 * Nat.clog 2 n := by
  classical
  dsimp [nextState] at hnext
  split_ifs at hnext with hcontinue
  exact Nat.le_of_not_gt (fun h => hcontinue ⟨haccept, h⟩)

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

/-- The state reached after the protocol has consumed its allotted number of
queries; a stopped state remains stopped while zero-width queries follow. -/
noncomputable def endState {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hL : 0 < Nat.clog 2 n) :
    (R : ℕ) → (state : Option (RoundState c n x G)) →
    (T : ℕ) → Fits
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R state) T → (Fin T → Bool) →
      Option (RoundState c n x G)
  | 0, state, _, _, _ => state
  | R + 1, state, T, hfit, tape => by
      obtain ⟨hk, hchild⟩ := hfit
      let parts := splitEquiv hk tape
      exact endState hx hG hc hL R (nextState hx hG hc state parts.1)
        (T - sourceWidth state) (hchild parts.1) parts.2

lemma endState_none {c n T R : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hL : 0 < Nat.clog 2 n)
    (hfit : Fits
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R none) T)
    (tape : Fin T → Bool) :
    endState hx hG hc hL R none T hfit tape = none := by
  induction R generalizing T with
  | zero => rfl
  | succ R ih =>
      rcases hfit with ⟨hk, hchild⟩
      let parts := splitEquiv hk tape
      simpa [endState, nextState_none, parts] using
        (ih (hchild parts.1) parts.2)

/-- A large round-boundary state cannot survive all `clog n` adaptive
queries: every continuing round increments its recorded round counter, whose
frontier invariant keeps it strictly below that limit. -/
lemma endState_none_after_remaining_rounds {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c)
    (hL : 0 < Nat.clog 2 n) :
    ∀ {R T : ℕ} (s : RoundState c n x G),
      s.env.vars "round" + R = Nat.clog 2 n →
      (hfit : Fits
        (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
          (nextState hx hG hc) R (some s)) T) →
      (tape : Fin T → Bool) →
      endState hx hG hc hL R (some s) T hfit tape = none := by
  intro R
  induction R with
  | zero =>
      intro T s hround hfit tape
      have hbound := s.frontier.shrinking.rounds_succ_le_clog hc s.nontrivial
      omega
  | succ R ih =>
      intro T s hround hfit tape
      rcases hfit with ⟨hk, hchild⟩
      let parts := splitEquiv hk tape
      cases hnext : nextState hx hG hc (some s) parts.1 with
      | none =>
          have hchild' : Fits
              (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
                (nextState hx hG hc) R none) (T - sourceWidth (some s)) := by
            simpa only [hnext] using hchild parts.1
          simpa [endState, parts, hnext] using
            (endState_none hx hG hc hL hchild' parts.2)
      | some s' =>
          have hstep := nextState_some_round hx hG hc s parts.1 s' hnext
          have hround' : s'.env.vars "round" + R = Nat.clog 2 n := by omega
          have hchild' : Fits
              (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
                (nextState hx hG hc) R (some s')) (T - sourceWidth (some s)) := by
            simpa only [hnext] using hchild parts.1
          simpa [endState, parts, hnext] using
            (ih s' hround' hchild' parts.2)

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

lemma machine_tape_reserve {K n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (hx : EncodesGraph x n G)
    (hK : 24 ≤ K) :
    24 * Nat.clog 2 n * n ≤ timeBudget K n x := by
  have hn : n ≤ x.length + 1 := by have := hx.length_eq; omega
  have h₁ := Nat.mul_le_mul_left (24 * Nat.clog 2 n) hn
  have h₂ := Nat.mul_le_mul_right (x.length + 1)
    (Nat.mul_le_mul_left 24 (Nat.le_succ (Nat.clog 2 n)))
  have h₃ := Nat.mul_le_mul_right
    ((x.length + 1) * (Nat.clog 2 n + 1)) hK
  dsimp [timeBudget]
  nlinarith [h₁, h₂, h₃]

lemma source_failure_budget {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (s : RoundState c n x G)
    (hc : 1 ≤ c) :
    (Nat.clog 2 n : ℚ) *
      (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n) ≤ 1 / 3 := by
  have hcount : s.env.vars "acount" ≤ n := by
    rw [s.frontier.activeCount]
    exact activeVertices_card_le _ _
  have hlarge : 12 * c ^ 2 * Nat.clog 2 n < n :=
    lt_of_lt_of_le s.large hcount
  have hbound := active_loop_total_failure_le_one_six_rat hc s.nontrivial hlarge
  linarith

/-- All numerical and probabilistic accounting is discharged for the literal
source-state protocol.  The sole remaining input is that its good paths
produce successful source executions. -/
lemma machine_probability_of_source_good_paths {K c n w : ℕ}
    {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hK : 60001 ≤ K) (hvalid : ValidInput K c n w G x)
    (start : RoundState c n x G)
    (hsuccess : ∀ ρ : Fin (timeBudget K n x) → Bool,
      GoodPath
        (protocol sourceWidth
          (sourceBad (G := G) (x := x) (c := c)
            (Nat.clog_pos (by omega) start.nontrivial))
          (nextState hvalid.2.2.1 hvalid.2.1 hvalid.1)
          (Nat.clog 2 n) (some start)) (timeBudget K n x)
        (fits_of_maxConsumedBits _ _
          (source_maxConsumedBits_le_tape hvalid.2.2.1 hvalid.2.1
            hvalid.1 (machine_tape_reserve hvalid.2.2.1 (by omega))
            (Nat.clog_pos (by omega) start.nontrivial) _ start)) ρ →
      ρ ∈ sourceGoodTapes c n x (sourceCost 6000 n x) (timeBudget K n x)) :
    (2 / 3 : ℚ) * 2 ^ timeBudget K n x ≤
      ((goodTapes w c x (timeBudget K n x)).ncard : ℚ) := by
  let p := protocol sourceWidth
    (sourceBad (G := G) (x := x) (c := c)
      (Nat.clog_pos (by omega) start.nontrivial))
    (nextState hvalid.2.2.1 hvalid.2.1 hvalid.1)
    (Nat.clog 2 n) (some start)
  let ε : ℚ := 1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hNpow : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
  have hlocal : LocallyBounded ε p :=
    locallyBounded_source hvalid.2.2.1 hvalid.2.1 hvalid.1 hNpow
      (Nat.clog_pos (by omega) start.nontrivial) _ _
  have hreserve : 24 * Nat.clog 2 n * n ≤ timeBudget K n x :=
    machine_tape_reserve hvalid.2.2.1 (by omega)
  have hbits : maxConsumedBits p ≤ timeBudget K n x :=
    source_maxConsumedBits_le_tape hvalid.2.2.1 hvalid.2.1 hvalid.1
      hreserve (Nat.clog_pos (by omega) start.nontrivial) _ _
  have hcost : 10 * sourceCost 6000 n x + 1 ≤ timeBudget K n x :=
    cost_lift (by omega)
  apply machine_success_count_of_protocol (by omega) hvalid hcost p ε hε
    hlocal hbits (source_failure_budget start hvalid.1)
  intro ρ hρ
  exact hsuccess ρ ((goodPath_iff_not_mem_failingTapes p _ _ _).2 hρ)

/-- A successful big-step execution need not carry the final near-linear
cost proof itself: determinism identifies its result with the already proved
bounded total source run on the same tape. -/
lemma sourceGoodTapes_of_bigStep_good {c n T k : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hT : sourceCost 6000 n x ≤ T)
    (ρ : Fin T → Bool) {τ : Env}
    (hr : BigStepB (sourceBound c x) welzlCom
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) τ k)
    (hg : τ.vars "good" = 1) :
    ρ ∈ sourceGoodTapes c n x (sourceCost 6000 n x) T := by
  obtain ⟨υ, hrun, _, _⟩ := welzlCom_run_correct hx hG hc hT ρ
  have heq := run_final_eq (show Run (sourceBound c x) welzlCom
    (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
      ((c :: x) ++ bitTape ρ)) τ k from ⟨k, le_rfl, hr⟩) hrun
  subst υ
  exact ⟨τ, hrun, hg⟩

lemma finish_after_good_loop {c n : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env}
    (hfront : Frontier (sourceBound c x) c n x σ)
    (hstore : Stored G (6 * c ^ 2 * Nat.clog 2 n) σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hsmall : σ.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n) :
    ∃ τ, Run (sourceBound c x) finish σ τ (104 * (n + 1)) ∧
      τ.vars "good" = 1 := by
  have hnB : n < sourceBound c x := by
    simpa only [hfront.workspace.vertices] using
      hfront.workspace.bounded.vars "n"
  have hpost : DriverPost (sourceBound c x) c n x σ :=
    ⟨hfront.workspace, Or.inl hfront, fun _ => hsmall⟩
  obtain ⟨τ, hr, hgood, _, _⟩ :=
    finish_run hpost hc hn hnB (fun _ => ⟨hstore⟩)
  exact ⟨τ, hr, hgood.trans hfront.success⟩

end Lax235315Proofs.Construction.SourceAdaptiveState
