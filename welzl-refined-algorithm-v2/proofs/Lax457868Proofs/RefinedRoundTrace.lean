import Lax457868Proofs.RefinedRoundLoop
import Lax457868Proofs.SourceTapePrefix

/-! A chronological certificate for the actual source iterations. Each record
retains both machine states, the exact consumed prefix, the active cardinality
at entry, and the source cost. -/

namespace Lax457868Proofs.RefinedRoundTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundSource

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

structure RoundEvent where
  entry : Env
  exit : Env
  active : ℕ
  consumed : List ℕ
  cost : ℕ
  accepted : Bool

/-- Successive records share their physical endpoint. The consumed words are
the actual prefix removed by the source run, not an independent random tape. -/
inductive TraceChain {n : ℕ} (B c : ℕ) (G : SimpleGraph (Fin n))
    (x rest : List ℕ) : Env → Env → List RoundEvent → Prop where
  | nil (σ : Env) : TraceChain B c G x rest σ σ []
  | cons {σ ρ τ : Env} {tail : List RoundEvent} {active cost : ℕ}
      {accepted : Bool}
      {consumed : List ℕ}
      (hready : LoopReady B c G x rest σ)
      (hguard : roundGuard.evalB B σ = some true)
      (hactive : σ.vars "acount" = active)
      (hrun : Run B preparedRefinedRoundSource σ ρ cost)
      (hinput : σ.inp = consumed ++ ρ.inp)
      (hconsumed : consumed.length ≤ cost)
      (houtcome : if accepted then
          LoopReady B c G x rest ρ ∧ 0 < ρ.vars "acount"
        else ρ.vars "acount" = 0)
      (htail : TraceChain B c G x rest ρ τ tail) :
      TraceChain B c G x rest σ τ
        ({ entry := σ, exit := ρ, active, consumed, cost, accepted } :: tail)

def traceCost (events : List RoundEvent) : ℕ :=
  (events.map fun e => 1 + roundGuard.size + e.cost).sum +
    (1 + roundGuard.size)

private lemma run_while_true {B K K' : ℕ} {b : Cond} {c : Com}
    {σ σ' σ'' : Env} (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ' K)
    (htail : Run B (.while b c) σ' σ'' K') :
    Run B (.while b c) σ σ'' (1 + b.size + K + K') := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := htail
  exact ⟨1 + b.size + k + k', by omega, .while_true hb hbs hbs'⟩

/-- The literal while execution yields a causally ordered list of exactly its
body calls. Its total source charge is the sum of recorded body charges and
the guard charge for each call and the final false test. -/
lemma round_while_run_traced {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4 * (x.length + 1) ≤ B)
    (hlargeN : 2 * refinedCutoffK c < n)
    (hready : LoopReady B c G x rest σ)
    (hpositive : 0 < σ.vars "acount") :
    ∃ τ K events,
      Run B (.while roundGuard preparedRefinedRoundSource) σ τ K ∧
      TraceChain B c G x rest σ τ events ∧
      K = traceCost events ∧
      τ.vars "n" = n ∧
      (τ.vars "acount" = 0 ∨
        (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) ∧
      (τ.vars "acount" = 0 →
        ∃ before e, events = before ++ [e] ∧ e.accepted = false) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have core : ∀ m : ℕ, ∀ ρ : Env,
      LoopReady B c G x rest ρ → 0 < ρ.vars "acount" →
        ρ.vars "acount" = m →
      ∃ τ K events,
        Run B (.while roundGuard preparedRefinedRoundSource) ρ τ K ∧
        TraceChain B c G x rest ρ τ events ∧
        K = traceCost events ∧
        τ.vars "n" = n ∧
        (τ.vars "acount" = 0 ∨
          (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) ∧
        (τ.vars "acount" = 0 →
          ∃ before e, events = before ++ [e] ∧ e.accepted = false) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro ρ hreadyρ hpositiveρ hm
      have hreadyKeep := hreadyρ
      obtain ⟨A, C, bits, sizes, D, hA, hCsub, hC, hsep, ⟨hstore⟩, hbounded,
        hcapacity, hroundCapacity, hacount, hsizesLen, hsizesSum,
        hpotential, hroundLog, hout, hinput, htape⟩ := hreadyρ
      have hAm : A.card = m := by omega
      have hguard := guard_eval D hA hacount hlargeN hB hx
      by_cases hlarge : 2 * refinedCutoffK c < A.card
      · have htrue : roundGuard.evalB B ρ = some true := by
          simpa [hlarge] using hguard
        obtain ⟨ρ', K, hstep, hnStep, hresult⟩ := round_step D hA hCsub hC hstore
          hbounded hcapacity hroundCapacity hacount hsizesLen hsizesSum
          hpotential hroundLog hout hinput htape hx hG hc hB hlarge
        have hstepKeep := hstep
        obtain ⟨k, hk, hbig⟩ := hstep
        obtain ⟨pre, hpre, hpreLen, _⟩ :=
          Lax457868Proofs.SourceTapePrefix.consumed_prefix hbig
        have hpreCost : pre.length ≤ K := hpreLen.trans hk
        rcases hresult with ⟨A', hstrict, hpositive', hacount', hready'⟩ | hfail
        · obtain ⟨τ, K', events, htail, hchain, hcost, hnTail,
            hresult', hlast⟩ :=
            ih A'.card (by omega) ρ' hready' (by omega) hacount'
          refine ⟨τ, 1 + roundGuard.size + K + K',
            { entry := ρ, exit := ρ', active := A.card,
              consumed := pre, cost := K, accepted := true } :: events,
            run_while_true htrue hstepKeep htail,
            TraceChain.cons (accepted := true) hreadyKeep htrue hacount
              hstepKeep hpre hpreCost
              (by simpa using
                (show LoopReady B c G x rest ρ' ∧ 0 < ρ'.vars "acount" from
                  ⟨hready', by omega⟩)) hchain,
            ?_, hnTail, hresult', ?_⟩
          · simp [traceCost, hcost, Nat.add_assoc]
          · intro hzero
            obtain ⟨before, e, heq, hefalse⟩ := hlast hzero
            exact ⟨(RoundEvent.mk ρ ρ' A.card pre K true) :: before,
              e, by simp [heq], hefalse⟩
        · have hcut' : ρ'.vars "cutoffResult" = 2 * refinedCutoffK c := by
            rw [hstepKeep.frame_var "cutoffResult" (by decide)]
            exact D.cutoff
          have hfalse := failed_guard_false hcut' hfail hlargeN hnB
          have htail : Run B (.while roundGuard preparedRefinedRoundSource)
              ρ' ρ' (1 + roundGuard.size) := Run.while_false hfalse
          refine ⟨ρ', 1 + roundGuard.size + K + (1 + roundGuard.size),
            [{ entry := ρ, exit := ρ', active := A.card,
               consumed := pre, cost := K, accepted := false }],
            run_while_true htrue hstepKeep htail,
            TraceChain.cons (accepted := false) hreadyKeep htrue hacount hstepKeep hpre hpreCost
              (by simpa using hfail) (TraceChain.nil ρ'),
            ?_, hnStep, Or.inl hfail, ?_⟩
          · simp [traceCost, Nat.add_assoc]
          · intro _
            exact ⟨[], RoundEvent.mk ρ ρ' A.card pre K false, rfl, rfl⟩
      · have hfalse : roundGuard.evalB B ρ = some false := by
          simpa [hlarge] using hguard
        exact ⟨ρ, 1 + roundGuard.size, [], Run.while_false hfalse,
          TraceChain.nil ρ, rfl, D.vertices,
          Or.inr ⟨hreadyKeep, by omega⟩,
          by intro hzero; omega⟩
  have hreadyKeep := hready
  obtain ⟨A, C, bits, sizes, D, hA, hC, hne, hsep, hs, hb, hcap, hrc,
    hac, hlen, hsum, hpot, hlog, hout, hin, ht⟩ := hready
  exact core A.card σ hreadyKeep hpositive hac

end Lax457868Proofs.RefinedRoundTrace
