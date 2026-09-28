import Lax235315Proofs.Construction.HistoryRoundSource
import Lax235315Proofs.Construction.GuardedAdaptiveProtocol
import Lax235315Proofs.Construction.GuardedArithmetic

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

end Lax235315Proofs.Construction.SourceAdaptiveState
