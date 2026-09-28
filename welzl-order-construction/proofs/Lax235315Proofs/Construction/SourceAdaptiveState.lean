import Lax235315Proofs.Construction.HistoryRoundSource
import Lax235315Proofs.Construction.GuardedAdaptiveProtocol

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

end Lax235315Proofs.Construction.SourceAdaptiveState
