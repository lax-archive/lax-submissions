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
          LoopReady B c G x rest ρ ∧ 0 < ρ.vars "acount" ∧
          3 * ρ.vars "acount" ≤ 2 * active ∧
          ρ.vars "round" = σ.vars "round" + 1
        else ρ.vars "acount" = 0 ∧
          ((ρ.vars "initialRetryStatus" = 2 ∨ ρ.vars "initialRetryStatus" = 3) ∨
            (ρ.vars "repairRetryStatus" = 2 ∨ ρ.vars "repairRetryStatus" = 3)))
      (hstop : accepted = false → tail = [])
      (htail : TraceChain B c G x rest ρ τ tail) :
      TraceChain B c G x rest σ τ
        ({ entry := σ, exit := ρ, active, consumed, cost, accepted } :: tail)

def traceCost (events : List RoundEvent) : ℕ :=
  (events.map fun e => 1 + roundGuard.size + e.cost).sum +
    (1 + roundGuard.size)

/-- Zero-padded active size and source charge at the given chronological
attempt index. -/
def activeAt : List RoundEvent → ℕ → ℕ
  | [], _ => 0
  | event :: _, 0 => event.active
  | _ :: tail, i + 1 => activeAt tail i

def chargeAt : List RoundEvent → ℕ → ℕ
  | [], _ => 0
  | event :: _, 0 => 1 + roundGuard.size + event.cost
  | _ :: tail, i + 1 => chargeAt tail i

def failedAt (events : List RoundEvent) (i : ℕ) : Bool :=
  match events[i]? with
  | none => false
  | some event => !event.accepted

def failureStatus (ρ : Env) : Prop :=
  (ρ.vars "initialRetryStatus" = 2 ∨ ρ.vars "initialRetryStatus" = 3) ∨
    (ρ.vars "repairRetryStatus" = 2 ∨ ρ.vars "repairRetryStatus" = 3)

/-- A failed recorded iteration is an actual sampler-status failure. -/
lemma TraceChain.failedAt_status {n B c : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) (i : ℕ)
    (hfail : failedAt events i = true) :
    ∃ event, events[i]? = some event ∧ failureStatus event.exit := by
  induction h generalizing i with
  | nil => simp [failedAt] at hfail
  | cons hready hguard hactive hrun hinput hconsumed houtcome hstop htail ih =>
    rename_i σ0 ρ0 τ0 tail active cost accepted consumed
    cases i with
    | zero =>
      have ha : accepted = false := by
        simpa [failedAt] using hfail
      have hs := houtcome
      simp only [ha, Bool.cond_false] at hs
      exact ⟨{ entry := σ0, exit := ρ0, active, consumed, cost, accepted },
        rfl, hs.2⟩
    | succ j =>
      have hj : failedAt tail j = true := by simpa [failedAt] using hfail
      obtain ⟨event, hevent, hstatus⟩ := ih j hj
      exact ⟨event, by simpa using hevent, hstatus⟩

def usedBefore (events : List RoundEvent) (i : ℕ) : ℕ :=
  ((events.take i).flatMap fun event => event.consumed).length

lemma usedBefore_le_total (events : List RoundEvent) (i : ℕ) :
    usedBefore events i ≤ (events.flatMap fun event => event.consumed).length := by
  exact (List.IsPrefix.length_le
    ((List.take_prefix i events).flatMap fun event => event.consumed))

lemma TraceChain.active_contract {n B c : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) (i : ℕ) :
    3 * activeAt events (i + 1) ≤ 2 * activeAt events i := by
  induction h generalizing i with
  | nil => simp [activeAt]
  | cons hready hguard hactive hrun hinput hconsumed houtcome hstop htail ih =>
    rename_i σ0 ρ0 τ0 tail active cost accepted consumed
    cases i with
    | succ i => simpa only [activeAt] using ih i
    | zero =>
      by_cases ha : accepted = true
      · have hcontract : 3 * ρ0.vars "acount" ≤ 2 * active := by
          have hh := houtcome
          simp only [ha, Bool.cond_true] at hh
          exact hh.2.2.1
        cases htail with
        | nil => simp [activeAt]
        | cons hready' hguard' hactive' hrun' hinput' hconsumed' houtcome'
            hstop' htail' =>
          simp only [activeAt]
          omega
      · have hf : accepted = false := by cases accepted <;> simp_all
        have hempty := hstop hf
        subst tail
        simp [activeAt]

lemma TraceChain.first_active_le {n B c : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) : activeAt events 0 ≤ n := by
  cases h with
  | nil => simp [activeAt]
  | cons hready _ hactive _ _ _ _ _ _ =>
    obtain ⟨A, C, bits, sizes, D, hA, _, _, _, _, _, _, _, hacount,
      _, _, _, _, _, _, _⟩ := hready
    have hcard : A.card ≤ n := by simpa using Finset.card_le_card hA
    simp only [activeAt]
    omega

lemma sum_chargeAt_pad (events : List RoundEvent) (R : ℕ)
    (hlen : events.length ≤ R) :
    (∑ i ∈ Finset.range R, chargeAt events i) =
      (events.map fun e => 1 + roundGuard.size + e.cost).sum := by
  induction events generalizing R with
  | nil => simp [chargeAt]
  | cons event tail ih =>
    cases R with
    | zero => simp at hlen
    | succ R =>
      have htail : tail.length ≤ R := by simpa using hlen
      rw [Finset.sum_range_succ']
      simp only [chargeAt, List.map_cons, List.sum_cons]
      rw [ih R htail]
      omega

/-- The records partition the one physical input prefix read by the loop. -/
lemma TraceChain.consumed_append {n B c : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) :
    σ.inp = (events.flatMap fun e => e.consumed) ++ τ.inp := by
  induction h with
  | nil => simp
  | cons _ _ _ _ hinput _ _ _ _ ih =>
    rw [hinput, ih]
    simp only [List.flatMap_cons, List.append_assoc]

/-- The total number of read words is bounded by the recorded source
charges; this follows from the physical input-prefix certificate. -/
lemma TraceChain.consumed_length_le_cost {n B c : ℕ}
    {G : SimpleGraph (Fin n)} {x rest : List ℕ}
    {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) :
    (events.flatMap fun e => e.consumed).length ≤
      (events.map fun e => e.cost).sum := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ hconsumed _ _ _ ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

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
      events.length + σ.vars "round" ≤ Nat.clog 2 n ∧
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
        events.length + ρ.vars "round" ≤ Nat.clog 2 n ∧
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
        rcases hresult with ⟨A', hstrict, hpositive', hcontract', hround',
            hacount', hready'⟩ | hfail
        · obtain ⟨τ, K', events, htail, hchain, hcost, hlength, hnTail,
            hresult', hlast⟩ :=
            ih A'.card (by omega) ρ' hready' (by omega) hacount'
          refine ⟨τ, 1 + roundGuard.size + K + K',
            { entry := ρ, exit := ρ', active := A.card,
              consumed := pre, cost := K, accepted := true } :: events,
            run_while_true htrue hstepKeep htail,
            TraceChain.cons (accepted := true) hreadyKeep htrue hacount
              hstepKeep hpre hpreCost
              (by simpa using
                (show LoopReady B c G x rest ρ' ∧ 0 < ρ'.vars "acount" ∧
                    3 * ρ'.vars "acount" ≤ 2 * A.card ∧
                    ρ'.vars "round" = ρ.vars "round" + 1 from
                  ⟨hready', by omega, by omega, hround'⟩))
              (by simp) hchain,
            ?_, ?_, hnTail, hresult', ?_⟩
          · simp [traceCost, hcost, Nat.add_assoc]
          · simp only [List.length_cons]
            omega
          · intro hzero
            obtain ⟨before, e, heq, hefalse⟩ := hlast hzero
            exact ⟨(RoundEvent.mk ρ ρ' A.card pre K true) :: before,
              e, by simp [heq], hefalse⟩
        · obtain ⟨hzero, hstatus⟩ := hfail
          have hcut' : ρ'.vars "cutoffResult" = 2 * refinedCutoffK c := by
            rw [hstepKeep.frame_var "cutoffResult" (by decide)]
            exact D.cutoff
          have hfalse := failed_guard_false hcut' hzero hlargeN hnB
          have htail : Run B (.while roundGuard preparedRefinedRoundSource)
              ρ' ρ' (1 + roundGuard.size) := Run.while_false hfalse
          refine ⟨ρ', 1 + roundGuard.size + K + (1 + roundGuard.size),
            [{ entry := ρ, exit := ρ', active := A.card,
               consumed := pre, cost := K, accepted := false }],
            run_while_true htrue hstepKeep htail,
            TraceChain.cons (accepted := false) hreadyKeep htrue hacount hstepKeep hpre hpreCost
              (by simpa using And.intro hzero hstatus) (by intro _; rfl) (TraceChain.nil ρ'),
            ?_, ?_, hnStep, Or.inl hzero, ?_⟩
          · simp [traceCost, Nat.add_assoc]
          · simp only [List.length_singleton]
            omega
          · intro _
            exact ⟨[], RoundEvent.mk ρ ρ' A.card pre K false, rfl, rfl⟩
      · have hfalse : roundGuard.evalB B ρ = some false := by
          simpa [hlarge] using hguard
        exact ⟨ρ, 1 + roundGuard.size, [], Run.while_false hfalse,
          TraceChain.nil ρ, rfl, by simp; omega,
          D.vertices,
          Or.inr ⟨hreadyKeep, by omega⟩,
          by intro hzero; omega⟩
  have hreadyKeep := hready
  obtain ⟨A, C, bits, sizes, D, hA, hC, hne, hsep, hs, hb, hcap, hrc,
    hac, hlen, hsum, hpot, hlog, hout, hin, ht⟩ := hready
  exact core A.card σ hreadyKeep hpositive hac

end Lax457868Proofs.RefinedRoundTrace
