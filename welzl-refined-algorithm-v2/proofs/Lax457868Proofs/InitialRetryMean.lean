import Lax457868Proofs.FullInitialAttemptMean
import Lax457868Proofs.InitialAbortProbability

/-! Mean bounds for the actual source retry loop. -/
namespace Lax457868Proofs.InitialRetryMean

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.FullInitialAttemptMean
open Lax457868Proofs.FullInitialAttempt
open Lax457868Proofs.InitialAbortProbability
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

variable {B n m domainCap r t bufferCap targetCap Q k cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

/-- A zero-status retry decision after a checked full attempt is exactly an
ordinary mathematical rejection.  The acceptance flag is Boolean on the
selector-success path; this matters because scratch flags may be stale when
selection aborts. -/
lemma decision_zero_rejected
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {σa σd : Env} {q p : ℕ}
    (hstatus : R.I.σ.vars "initialRetryStatus" = 0)
    (hfull : BigStepB B fullInitialAttempt R.I.σ σa q)
    (hdecision : BigStepB B initialRetryDecision σa σd p)
    (hzero : σd.vars "initialRetryStatus" = 0) :
    σa.vars "batchFailed" = 0 ∧ σa.vars "repFailed" = 0 ∧
      σa.vars "attemptAccepted" = 0 := by
  have hrun : Run B fullInitialAttempt R.I.σ σa q :=
    Run.of_bigStepB hfull
  have hstatusA : σa.vars "initialRetryStatus" = 0 := by
    rw [hrun.frame_var "initialRetryStatus" (by decide)]
    exact hstatus
  obtain ⟨hbatch0, hrep0, hnot1⟩ :=
    decision_status_zero_rejected hstatusA hdecision hzero
  obtain ⟨σsel, σc, tape, tail, values, used, drawFailed, stageCost,
    hbits, htrace, hselRun, hfullCanon, hbatch, hinpSel, houtSel,
    hoff, htgt, hactiveA, hactiveB, hn, hqpow,
    hdrawFailure, hdrawSuccess⟩ :=
    fullInitialAttempt_run_bits R.I R.hactiveA R.hdegree R.hinter
      R.hneighbors R.hexceptionFlags R.hexceptionList R.hnearBound
      R.hexceptionCap R.hnB R.hkB R.hcapB
  have heq : σc = σa := by
    obtain ⟨_, _, hc⟩ := hfullCanon
    exact (BigStep.unique hc.bigStep hfull.bigStep).1
  cases drawFailed with
  | true =>
      have hb : σc.vars "batchFailed" = 1 := by simpa using hbatch
      rw [heq] at hb
      omega
  | false =>
      obtain ⟨W, repFailed, repUsed, hW, hWA, hvaluesLen,
        hrepLe, hrepVal, hinp, hrepFailure, hrepSuccess⟩ :=
        hdrawSuccess rfl
      cases repFailed with
      | true =>
          obtain ⟨hselEq, _, _, _⟩ := hrepFailure rfl
          have hr : σc.vars "repFailed" = 1 := by
            rw [hselEq]
            simpa using hrepVal
          rw [heq] at hr
          omega
      | false =>
          obtain ⟨mapped, choice, packedExceptions, packedSample,
            hmappedSel, hdraws, hchoiceSample, hchoiceRep,
            hacceptRun, hExceptionsEq, hflags, hlist, hprefixE,
            hcountE, hacceptBit, hsampleFlags, hord, hprefixW,
            hcountW, hrepFinal, hactiveBFinal, hinpFinal⟩ :=
            hrepSuccess rfl
          have hbit : σa.vars "attemptAccepted" =
              (if (choice.exceptions k).card ≤ cap then 1 else 0) := by
            simpa [heq] using hacceptBit
          constructor
          · exact hbatch0
          constructor
          · exact hrep0
          · by_cases hpass : (choice.exceptions k).card ≤ cap
            · simp [hpass] at hbit
              exact False.elim (hnot1 hbit)
            · simpa [hpass] using hbit

lemma tail_cost_of_not_rejected
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (N : ℕ) (hb : attemptBitBudget n m r t ≤ N)
    (hstatus : R.I.σ.vars "initialRetryStatus" = 0)
    (ρ : Tape N) {σa σd τ : Env} {q p u : ℕ}
    (hfull : BigStepB B fullInitialAttempt
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hb)).I.σ
      σa q)
    (hdecision : BigStepB B initialRetryDecision σa σd p)
    (htail : BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      σd τ u)
    (hnot : ¬ readyAttemptRejected R hb ρ) : u = 4 := by
  apply retryWhile_nonzero_cost _ htail
  intro hzero
  obtain ⟨hbatch, hrep, haccept⟩ :=
    decision_zero_rejected
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hb))
      (by simpa [ReadyInput.reinput_state] using hstatus)
      hfull hdecision hzero
  apply hnot
  exact ⟨σa, q, Run.of_bigStepB hfull, hbatch, hrep, haccept⟩

/-- On the last ordinary rejection the runtime counter becomes zero. -/
lemma decision_zero_left_one {B : ℕ} {σa σd : Env} {p : ℕ}
    (hleft : σa.vars "initialRetriesLeft" = 1)
    (hdecision : BigStepB B initialRetryDecision σa σd p)
    (hzero : σd.vars "initialRetryStatus" = 0) :
    σd.vars "initialRetriesLeft" = 0 := by
  unfold initialRetryDecision at hdecision
  cases hdecision with
  | ite_false _ hset =>
      cases hset with
      | assign he =>
          obtain ⟨rfl, _⟩ := evalB_lit_iff.mp he
          simp at hzero
  | ite_true _ hrep =>
      cases hrep with
      | ite_false _ hset =>
          cases hset with
          | assign he =>
              obtain ⟨rfl, _⟩ := evalB_lit_iff.mp he
              simp at hzero
      | ite_true _ haccept =>
          cases haccept with
          | ite_true _ hset =>
              cases hset with
              | assign he =>
                  obtain ⟨rfl, _⟩ := evalB_lit_iff.mp he
                  simp at hzero
          | ite_false _ hrestore =>
              cases hrestore with
              | seq hfirst hlast =>
                  have hmid := (Run.of_bigStepB hfirst).frame_var
                    "initialRetriesLeft" (by decide)
                  cases hlast with
                  | assign he =>
                      obtain ⟨v, one, hv, hone, hresult, _⟩ :=
                        evalB_bin_iff.mp he
                      obtain ⟨hval, _⟩ := evalB_var_iff.mp hv
                      obtain ⟨rfl, _⟩ := evalB_lit_iff.mp hone
                      simp [Bop.apply] at hresult
                      simp [hmid, hleft] at hval
                      simp [Env.setVar] at *
                      omega

/-- Replay an actual retry tail after changing only unread bits of the first
attempt.  The machine state before the tail is the canonical rejected next
state with that changed suffix. -/
lemma rejected_tail_replay
    (R J : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (bits bits' : List Bool)
    (hbudget : attemptBitBudget n m r t ≤ bits.length)
    (hbudget' : attemptBitBudget n m r t ≤ bits'.length)
    {σa σb σd τ : Env} {q qb p pd u d : ℕ}
    (hrun : Run B fullInitialAttempt
      (R.reinput bits (by simpa [attemptBitBudget] using hbudget)).I.σ σa q)
    (hinp : σa.inp = (bits.drop d).map Bool.toNat ++ R.I.rest)
    (hpre : bits.take d = bits'.take d)
    (hdecision : Run B initialRetryDecision σa J.I.σ p)
    (hJbits : J.I.bits = bits.drop d)
    (hnextBudget : attemptBitBudget n m r t ≤ (bits'.drop d).length)
    (hfull' : BigStepB B fullInitialAttempt
      (R.reinput bits' (by simpa [attemptBitBudget] using hbudget')).I.σ
      σb qb)
    (hdecision' : BigStepB B initialRetryDecision σb σd pd)
    (htail : BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      σd τ u) :
    BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      (J.reinput (bits'.drop d)
        (by simpa [attemptBitBudget] using hnextBudget)).I.σ τ u := by
  obtain ⟨hrun', hdec'⟩ :=
    rejected_step_replay R J bits bits' hbudget hbudget' hrun hinp
      hpre hdecision hJbits hnextBudget
  have heqA : σb = {σa with inp := (bits'.drop d).map Bool.toNat ++ R.I.rest} := by
    obtain ⟨_, _, hc⟩ := hrun'
    exact (BigStep.unique hfull'.bigStep hc.bigStep).1
  have heqD : σd =
      (J.reinput (bits'.drop d)
        (by simpa [attemptBitBudget] using hnextBudget)).I.σ := by
    obtain ⟨_, _, hc⟩ := hdec'
    exact (BigStep.unique (by simpa [heqA] using hdecision'.bigStep)
      hc.bigStep).1
  simpa only [heqD] using htail

/-- Average a nonnegative continuation cost after one actual stopped
attempt.  The conditional hypothesis is over completions of the observed
prefix; it is not an independent fresh-tape assumption. -/
private lemma stopped_retry_tail_mean {N : ℕ}
    (used : Tape N → ℕ) (first : Tape N → Prop)
    [DecidablePred first] (tailCost : Tape N → ℕ) (H : ℚ)
    (hH : 0 ≤ H)
    (hbound : ∀ ρ, used ρ ≤ N)
    (hcausal : ∀ ρ τ,
      (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ) →
      used τ = used ρ)
    (hfirst : ∀ ρ τ,
      (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ) →
      (first τ ↔ first ρ))
    (hhalf : 2 * (Finset.univ.filter first).card ≤ 2 ^ N)
    (hstop : ∀ ρ, ¬ first ρ → tailCost ρ ≤ 4)
    (hmean : ∀ ρ, first ρ →
      (∑ suffix : Tape (N - used ρ),
        (if first ((splitEquiv (hbound ρ)).symm
          ((splitEquiv (hbound ρ) ρ).1, suffix)) then
          (tailCost ((splitEquiv (hbound ρ)).symm
            ((splitEquiv (hbound ρ) ρ).1, suffix)) : ℚ) else 0)) ≤
          H * 2 ^ (N - used ρ)) :
    2 * (∑ ρ, (tailCost ρ : ℚ)) ≤ (H + 8) * 2 ^ N := by
  classical
  let X : Tape N → ℚ := fun ρ => if first ρ then tailCost ρ else 0
  let Y : Tape N → ℚ := fun ρ => if first ρ then H else 0
  have hY : ∀ ρ τ,
      (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ) →
      Y τ = Y ρ := by
    intro ρ τ hp
    simp only [Y]
    by_cases hf : first ρ
    · have ht : first τ := (hfirst ρ τ hp).mpr hf
      simp [hf, ht]
    · have ht : ¬ first τ := fun h => hf ((hfirst ρ τ hp).mp h)
      simp [hf, ht]
  have hconditional : ∀ ρ,
      (∑ suffix : Tape (N - used ρ),
        X ((splitEquiv (hbound ρ)).symm
          ((splitEquiv (hbound ρ) ρ).1, suffix))) ≤
          Y ρ * 2 ^ (N - used ρ) := by
    intro ρ
    by_cases hf : first ρ
    · simpa [X, Y, hf] using hmean ρ hf
    · have hf' : ∀ suffix : Tape (N - used ρ),
          ¬ first ((splitEquiv (hbound ρ)).symm
            ((splitEquiv (hbound ρ) ρ).1, suffix)) := by
        intro suffix
        have hp : (List.ofFn ρ).take (used ρ) =
            (List.ofFn ((splitEquiv (hbound ρ)).symm
              ((splitEquiv (hbound ρ) ρ).1, suffix))).take (used ρ) := by
          rw [StoppedPrefixAveraging.prefix_of_split (hbound ρ),
            StoppedPrefixAveraging.prefix_of_split (hbound ρ)]
          simp
        exact fun hh => hf ((hfirst ρ _ hp).mp hh)
      simp [X, Y, hf, hf']
  have hX := StoppedPrefixAveraging.sum_le_of_stopped_prefix used
    hbound hcausal X Y hY hconditional
  have hYsum : (∑ ρ, Y ρ) =
      H * ((Finset.univ.filter first).card : ℚ) := by
    simp only [Y]
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, mul_comm]
  have hhalfQ : 2 * ((Finset.univ.filter first).card : ℚ) ≤
      (2 ^ N : ℚ) := by exact_mod_cast hhalf
  have hpoint : ∀ ρ, (tailCost ρ : ℚ) ≤ X ρ + 4 := by
    intro ρ
    by_cases hf : first ρ
    · simp [X, hf]
    · simp [X, hf]
      exact_mod_cast hstop ρ hf
  have hsum := Finset.sum_le_sum
    (fun ρ (_ : ρ ∈ (Finset.univ : Finset (Tape N))) => hpoint ρ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_tape, nsmul_eq_mul] at hsum
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hsum
  rw [hYsum] at hX
  have hweighted : 2 * H * ((Finset.univ.filter first).card : ℚ) ≤
      H * 2 ^ N := by
    nlinarith only [mul_le_mul_of_nonneg_left hhalfQ hH]
  linear_combination 2 * hsum + 2 * hX + hweighted

/-- The first actual retry iteration has the previously established full
attempt mean.  This statement retains the actual tail BigStep and cost for
the renewal estimate. -/
lemma actual_first_mean
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (N left : ℕ)
    (hleft : R.I.σ.vars "initialRetriesLeft" = left)
    (hstatus : R.I.σ.vars "initialRetryStatus" = 0)
    (hpositive : 0 < left) (hleftB : left < B)
    (hb : attemptBitBudget n m r t ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hb)).I.σ
      (final ρ) (cost ρ)) :
    ∃ (attemptFinal decisionFinal : Tape N → Env)
      (attemptCost decisionCost tailCost : Tape N → ℕ),
      (∀ ρ, BigStepB B fullInitialAttempt
        (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hb)).I.σ
        (attemptFinal ρ) (attemptCost ρ)) ∧
      (∀ ρ, BigStepB B initialRetryDecision
        (attemptFinal ρ) (decisionFinal ρ) (decisionCost ρ)) ∧
      (∀ ρ, BigStepB B
        (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
        (decisionFinal ρ) (final ρ) (tailCost ρ)) ∧
      (∀ ρ, cost ρ = 8 + attemptCost ρ + decisionCost ρ + tailCost ρ) ∧
      (∀ ρ, decisionCost ρ ≤ 20) ∧
      (∑ ρ, attemptCost ρ) ≤
        (r*(42*Nat.clog 2 m+133)+12*Nat.clog 2 m+1180*n+
          624*targetCap+64*Q+571)*2^N := by
  classical
  have hd (ρ : Tape N) :=
    retryWhile_first_attempt
      (by simpa [ReadyInput.reinput_state] using hleft)
      (by simpa [ReadyInput.reinput_state] using hstatus)
      hpositive hleftB (hrun ρ)
  choose σa σd q p u ha hp hu hc using hd
  refine ⟨σa, σd, q, p, u, ha, hp, hu, ?_, ?_, ?_⟩
  · intro ρ
    have h := hc ρ
    simp [Cond.size, Expr.size] at h
    omega
  · intro ρ
    exact retryDecision_cost_le (hp ρ)
  · apply actual_full_mean R N hb σa q
    intro ρ
    simpa [ReadyInput.reinput_state] using ha ρ

/-- The actual tail family on a rejected stopped-prefix fiber is the retry
loop from its canonical post-decision ReadyInput, so an induction mean bound
applies to every completion of that very prefix. -/
private lemma rejected_tail_conditional
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (N left : ℕ) (hleftTwo : 2 ≤ left) (hleftB : left < B)
    (hsavedM : R.I.σ.vars "initialDomainSize" = m)
    (hsavedR : R.I.σ.vars "initialBatchTarget" = r)
    (hleft : R.I.σ.vars "initialRetriesLeft" = left)
    (hstatus : R.I.σ.vars "initialRetryStatus" = 0)
    (hbudget : left * attemptBitBudget n m r t ≤ N)
    (hper : attemptBitBudget n m r t ≤ N)
    [DecidablePred (readyAttemptRejected R hper)]
    (attemptFinal decisionFinal final : Tape N → Env)
    (attemptCost decisionCost tailCost : Tape N → ℕ)
    (ha : ∀ ρ, BigStepB B fullInitialAttempt
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (attemptFinal ρ) (attemptCost ρ))
    (hd : ∀ ρ, BigStepB B initialRetryDecision
      (attemptFinal ρ) (decisionFinal ρ) (decisionCost ρ))
    (hu : ∀ ρ, BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      (decisionFinal ρ) (final ρ) (tailCost ρ))
    (H : ℚ)
    (hIH : ∀ (J : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
      (N' : ℕ),
      J.I.activeB = R.I.activeB →
      J.I.σ.vars "initialDomainSize" = m →
      J.I.σ.vars "initialBatchTarget" = r →
      J.I.σ.vars "initialRetriesLeft" = left - 1 →
      J.I.σ.vars "initialRetryStatus" = 0 →
      (left - 1) * attemptBitBudget n m r t ≤ N' →
      (hper' : attemptBitBudget n m r t ≤ N') →
      (final' : Tape N' → Env) → (cost' : Tape N' → ℕ) →
      (∀ tail, BigStepB B
        (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
        (J.reinput (List.ofFn tail)
          (by simpa [attemptBitBudget] using hper')).I.σ
        (final' tail) (cost' tail)) →
      (∑ tail, (cost' tail : ℚ)) ≤ H * 2 ^ N')
    (ρ : Tape N)
    (hfirst : readyAttemptRejected R hper ρ) :
    let used := readyAttemptConsumed R hper
    (∑ suffix : Tape (N - used ρ),
      if readyAttemptRejected R hper
          ((splitEquiv (readyAttemptConsumed_le R hper ρ)).symm
            ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1, suffix)) then
        (tailCost ((splitEquiv (readyAttemptConsumed_le R hper ρ)).symm
          ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1, suffix)) : ℚ)
      else 0) ≤ H * 2 ^ (N - used ρ) := by
  classical
  let used := readyAttemptConsumed R hper
  let bits := List.ofFn ρ
  let Rρ := R.reinput bits (by simpa [attemptBitBudget, bits] using hper)
  obtain ⟨σa, q, hrun, hbatch, hrep, haccept⟩ := hfirst
  obtain ⟨d, J, p, hdBound, hinp, hJbits, hJrest, hJactive,
    hdecision, hJsavedM, hJsavedR, hJleft, hJstatus, hJbudget⟩ :=
    rejected_next_ready Rρ (left - 1) (by omega)
      (by simpa [Rρ, ReadyInput.reinput_state] using hsavedM)
      (by simpa [Rρ, ReadyInput.reinput_state] using hsavedR)
      (by
        have heq : left - 1 + 1 = left := by omega
        simpa [Rρ, ReadyInput.reinput_state, heq] using hleft)
      (by simpa [Rρ, ReadyInput.reinput_state] using hstatus)
      (by omega)
      (by
        have heq : left - 1 + 1 = left := by omega
        simpa [Rρ, bits, ReadyInput.reinput_bits, heq] using hbudget)
      (by simpa [Rρ, bits] using hrun) hbatch hrep haccept
  have hinp' : σa.inp = (bits.drop d).map Bool.toNat ++ R.I.rest := by
    have hrest : Rρ.I.rest = R.I.rest := rfl
    have hbits : Rρ.I.bits = bits := by
      exact R.reinput_bits bits (by simpa [attemptBitBudget, bits] using hper)
    simpa only [hbits, hrest] using hinp
  have hJbits' : J.I.bits = bits.drop d := by
    simpa [Rρ, ReadyInput.reinput_bits] using hJbits
  have hused : d = used ρ := by
    change d = readyAttemptConsumed R hper ρ
    obtain ⟨σu, qu, hrunu, hinpu, hdu⟩ :=
      readyAttemptConsumed_spec R hper ρ
    have heq : σa = σu := by
      obtain ⟨_, _, ha'⟩ := hrun
      obtain ⟨_, _, hb'⟩ := hrunu
      exact (BigStep.unique ha'.bigStep hb'.bigStep).1
    have heqInp := hinp'.symm.trans (by simpa [heq, bits] using hinpu)
    have hlen := congrArg List.length heqInp
    simp only [List.length_append, List.length_map, List.length_drop] at hlen
    have hdN : d ≤ N := hdBound.trans hper
    have huN : used ρ ≤ N := readyAttemptConsumed_le R hper ρ
    simp only [bits, List.length_ofFn] at hlen
    omega
  have htailN : J.I.bits.length = N - used ρ := by
    rw [hJbits']
    simp [bits, hused]
  have htailBudget : (left - 1) * attemptBitBudget n m r t ≤
      N - used ρ := by
    rw [htailN] at hJbudget
    exact hJbudget
  have hperTail : attemptBitBudget n m r t ≤ N - used ρ := by
    have hmul := Nat.mul_le_mul_right
      (attemptBitBudget n m r t) (show 1 ≤ left - 1 by omega)
    have hle : attemptBitBudget n m r t ≤
        (left - 1) * attemptBitBudget n m r t := by simpa using hmul
    exact hle.trans htailBudget
  let extend : Tape (N - used ρ) → Tape N := fun suffix =>
    (splitEquiv (readyAttemptConsumed_le R hper ρ)).symm
      ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1, suffix)
  have htailRun (suffix : Tape (N - used ρ)) :
      BigStepB B
        (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
        (J.reinput (List.ofFn suffix)
          (by simpa [attemptBitBudget] using hperTail)).I.σ
        (final (extend suffix)) (tailCost (extend suffix)) := by
    let τ := extend suffix
    have hpair : splitEquiv (readyAttemptConsumed_le R hper ρ) τ =
        ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1, suffix) :=
      Equiv.apply_symm_apply _ _
    have hprefix : bits.take d = (List.ofFn τ).take d := by
      rw [hused]
      rw [StoppedPrefixAveraging.prefix_of_split
        (readyAttemptConsumed_le R hper ρ),
        StoppedPrefixAveraging.prefix_of_split
        (readyAttemptConsumed_le R hper ρ), hpair]
    have hdrop : (List.ofFn τ).drop d = List.ofFn suffix := by
      rw [hused]
      change (List.ofFn τ).drop (readyAttemptConsumed R hper ρ) =
        List.ofFn suffix
      rw [StoppedPrefixAveraging.boolTape_split
        (readyAttemptConsumed_le R hper ρ) τ, hpair]
      have hlen :
          (List.ofFn ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1)).length =
            used ρ := by simpa only [used] using
              (List.length_ofFn (f := (splitEquiv
                (readyAttemptConsumed_le R hper ρ) ρ).1))
      have hle : readyAttemptConsumed R hper ρ ≤
          (List.ofFn ((splitEquiv (readyAttemptConsumed_le R hper ρ) ρ).1)).length := by
        simpa [used] using hlen.ge
      rw [List.drop_append_of_le_length hle]
      simp [hlen, used]
    have hnextPer : attemptBitBudget n m r t ≤
        ((List.ofFn τ).drop d).length := by
      rw [hdrop]
      simpa using hperTail
    have hreplay := rejected_tail_replay R J bits (List.ofFn τ)
      (by simpa [bits] using hper)
      (by simpa using hper)
      (by simpa [bits] using hrun)
      hinp' hprefix hdecision hJbits' hnextPer
      (ha τ) (hd τ) (hu τ)
    simpa only [hdrop] using hreplay
  have htailMean := hIH J (N - used ρ) hJactive hJsavedM hJsavedR
    hJleft hJstatus htailBudget hperTail
    (fun suffix => final (extend suffix))
    (fun suffix => tailCost (extend suffix)) htailRun
  dsimp [used]
  calc
    _ ≤ ∑ suffix : Tape (N - readyAttemptConsumed R hper ρ),
        (tailCost (extend suffix) : ℚ) := by
          apply Finset.sum_le_sum
          intro suffix _
          by_cases hf : readyAttemptRejected R hper (extend suffix)
          · simp [extend, hf]
          · simp [extend, hf]
    _ ≤ H * 2 ^ (N - readyAttemptConsumed R hper ρ) := htailMean

def fullCoefficient (n m r targetCap Q : ℕ) : ℕ :=
  r*(42*Nat.clog 2 m+133)+12*Nat.clog 2 m+1180*n+
    624*targetCap+64*Q+571

def retryCoefficient (n m r targetCap Q : ℕ) : ℕ :=
  2*fullCoefficient n m r targetCap Q+70

/-- Actual finite flat-tape mean cost of the bounded initial retry loop. -/
lemma actual_retry_mean
    (active : ℕ → ℕ)
    (hmass : SamplerWeightedRetries.badMass
      (SamplerInitialRetries.outcomeWeight A
        (activeVertices n active)
        (fun b => numericNeighborhood G b ∩ A) r)
      (SamplerInitialRetries.outcomeBad A
        (activeVertices n active)
        (fun b => numericNeighborhood G b ∩ A) r k cap) ≤ (1 / 2 : ℚ)) :
    ∀ (left N : ℕ)
      (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A),
      R.I.activeB = active →
      R.I.σ.vars "initialDomainSize" = m →
      R.I.σ.vars "initialBatchTarget" = r →
      R.I.σ.vars "initialRetriesLeft" = left →
      R.I.σ.vars "initialRetryStatus" = 0 →
      left < B →
      left * attemptBitBudget n m r t ≤ N →
      (hper : attemptBitBudget n m r t ≤ N) →
      (final : Tape N → Env) → (cost : Tape N → ℕ) →
      (∀ ρ, BigStepB B
        (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
        (R.reinput (List.ofFn ρ)
          (by simpa [attemptBitBudget] using hper)).I.σ
        (final ρ) (cost ρ)) →
      (∑ ρ, (cost ρ : ℚ)) ≤
        retryCoefficient n m r targetCap Q * 2 ^ N := by
  classical
  intro left
  induction left with
  | zero =>
      intro N R hactive hsavedM hsavedR hleft hstatus hB hbudget hper
        final cost hrun
      have h3B : 3 < B := by
        obtain ⟨a, ha⟩ := R.I.hAnonempty
        have han := Finset.mem_range.mp (R.I.hA ha)
        have hbound := R.hnB
        omega
      have hc (ρ : Tape N) : cost ρ ≤ 14 :=
        retryWhile_zero_cost
          (by simpa [ReadyInput.reinput_state] using hstatus)
          (by simpa [ReadyInput.reinput_state] using hleft)
          h3B (hrun ρ)
      calc
        (∑ ρ, (cost ρ : ℚ)) ≤ ∑ _ρ : Tape N, (14 : ℚ) := by
          apply Finset.sum_le_sum
          intro ρ _
          exact_mod_cast hc ρ
        _ = 14 * 2 ^ N := by simp [card_tape, Nat.cast_pow, mul_comm]
        _ ≤ retryCoefficient n m r targetCap Q * 2 ^ N := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show 14 ≤ retryCoefficient n m r targetCap Q by
            unfold retryCoefficient
            omega)
  | succ fuel ih =>
      intro N R hactive hsavedM hsavedR hleft hstatus hB hbudget hper
        final cost hrun
      obtain ⟨σa, σd, q, p, u, ha, hd, hu, hcost, hp, hqMean⟩ :=
        actual_first_mean R N (fuel + 1) hleft hstatus (by omega)
          hB hper final cost hrun
      let C := fullCoefficient n m r targetCap Q
      let H := retryCoefficient n m r targetCap Q
      have hq : (∑ ρ, (q ρ : ℚ)) ≤ C * 2 ^ N := by
        exact_mod_cast hqMean
      have hpmean : (∑ ρ, (p ρ : ℚ)) ≤ 20 * 2 ^ N := by
        calc
          (∑ ρ, (p ρ : ℚ)) ≤ ∑ _ρ : Tape N, (20 : ℚ) := by
            apply Finset.sum_le_sum
            intro ρ _
            exact_mod_cast hp ρ
          _ = 20 * 2 ^ N := by simp [card_tape, Nat.cast_pow, mul_comm]
      have hcostSum : (∑ ρ, (cost ρ : ℚ)) =
          8 * 2 ^ N + (∑ ρ, (q ρ : ℚ)) +
            (∑ ρ, (p ρ : ℚ)) + (∑ ρ, (u ρ : ℚ)) := by
        simp_rw [hcost]
        simp only [Nat.cast_add, Finset.sum_add_distrib]
        simp [card_tape, Nat.cast_pow]
        ring
      cases fuel with
      | zero =>
          have h3B : 3 < B := by
            obtain ⟨a, ha⟩ := R.I.hAnonempty
            have han := Finset.mem_range.mp (R.I.hA ha)
            have hbound := R.hnB
            omega
          have hu14 (ρ : Tape N) : u ρ ≤ 14 := by
            by_cases hzero : (σd ρ).vars "initialRetryStatus" = 0
            · have hleftA : (σa ρ).vars "initialRetriesLeft" = 1 := by
                have hf := (Run.of_bigStepB (ha ρ)).frame_var
                  "initialRetriesLeft" (by decide)
                rw [hf]
                simpa [ReadyInput.reinput_state] using hleft
              have hleftD := decision_zero_left_one hleftA (hd ρ) hzero
              exact retryWhile_zero_cost hzero hleftD h3B (hu ρ)
            · have hfour := retryWhile_nonzero_cost hzero (hu ρ)
              omega
          have humean : (∑ ρ, (u ρ : ℚ)) ≤ 14 * 2 ^ N := by
            calc
              _ ≤ ∑ _ρ : Tape N, (14 : ℚ) := by
                apply Finset.sum_le_sum
                intro ρ _
                exact_mod_cast hu14 ρ
              _ = 14 * 2 ^ N := by simp [card_tape, Nat.cast_pow, mul_comm]
          rw [hcostSum]
          have hCoeff : (retryCoefficient n m r targetCap Q : ℚ) =
              2 * C + 70 := by simp [C, retryCoefficient, Nat.cast_add,
                Nat.cast_mul]
          rw [hCoeff]
          nlinarith only [hq, hpmean, humean,
            show (0 : ℚ) ≤ 2 ^ N by positivity]
      | succ fuel' =>
          let used := readyAttemptConsumed R hper
          let first := readyAttemptRejected R hper
          have hmassR : SamplerWeightedRetries.badMass
              (SamplerInitialRetries.outcomeWeight A
                (activeVertices n R.I.activeB)
                (fun b => numericNeighborhood G b ∩ A) r)
              (SamplerInitialRetries.outcomeBad A
                (activeVertices n R.I.activeB)
                (fun b => numericNeighborhood G b ∩ A) r k cap) ≤
                (1 / 2 : ℚ) := by rw [hactive]; exact hmass
          have hhalf : 2 * (Finset.univ.filter first).card ≤ 2 ^ N := by
            simpa [first, readyAttemptRejectedFiber] using
              readyAttemptRejected_half R hper hmassR
          have husedBound : ∀ ρ, used ρ ≤ N :=
            readyAttemptConsumed_le R hper
          have husedCausal : ∀ ρ τ,
              (List.ofFn ρ).take (used ρ) =
                (List.ofFn τ).take (used ρ) → used τ = used ρ :=
            readyAttemptConsumed_causal R hper
          have hfirstCausal : ∀ ρ τ,
              (List.ofFn ρ).take (used ρ) =
                (List.ofFn τ).take (used ρ) →
              (first τ ↔ first ρ) := by
            intro ρ τ hpre
            constructor
            · intro hτ
              have hu := husedCausal ρ τ hpre
              have hpre' : (List.ofFn τ).take (used τ) =
                  (List.ofFn ρ).take (used τ) := by simpa [hu] using hpre.symm
              exact readyAttemptRejected_of_same_prefix R hper τ ρ hpre' hτ
            · exact readyAttemptRejected_of_same_prefix R hper ρ τ hpre
          have hstop : ∀ ρ, ¬ first ρ → u ρ ≤ 4 := by
            intro ρ hn
            exact (tail_cost_of_not_rejected R N hper hstatus ρ
              (ha ρ) (hd ρ) (hu ρ) hn).le
          have hIH : ∀ (J : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
              (N' : ℕ),
              J.I.activeB = R.I.activeB →
              J.I.σ.vars "initialDomainSize" = m →
              J.I.σ.vars "initialBatchTarget" = r →
              J.I.σ.vars "initialRetriesLeft" = fuel' + 1 →
              J.I.σ.vars "initialRetryStatus" = 0 →
              (fuel' + 1) * attemptBitBudget n m r t ≤ N' →
              (hper' : attemptBitBudget n m r t ≤ N') →
              (final' : Tape N' → Env) → (cost' : Tape N' → ℕ) →
              (∀ tail, BigStepB B
                (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
                (J.reinput (List.ofFn tail)
                  (by simpa [attemptBitBudget] using hper')).I.σ
                (final' tail) (cost' tail)) →
              (∑ tail, (cost' tail : ℚ)) ≤ H * 2 ^ N' := by
            intro J N' hJactive hJM hJR hJL hJS hJB hJP f c hrun'
            exact ih N' J (hJactive.trans hactive) hJM hJR hJL hJS
              (by omega) hJB hJP f c hrun'
          have hconditional : ∀ ρ, first ρ →
              (∑ suffix : Tape (N - used ρ),
                if first ((splitEquiv (husedBound ρ)).symm
                  ((splitEquiv (husedBound ρ) ρ).1, suffix)) then
                  (u ((splitEquiv (husedBound ρ)).symm
                    ((splitEquiv (husedBound ρ) ρ).1, suffix)) : ℚ) else 0) ≤
                H * 2 ^ (N - used ρ) := by
            intro ρ hf
            simpa [used, first, H] using
              rejected_tail_conditional R N (fuel' + 2) (by omega)
                hB hsavedM hsavedR hleft hstatus hbudget hper
                σa σd final q p u ha hd hu H (by
                  intro J N' hJa hJm hJr hJl hJs hJb hJp f c hr
                  exact hIH J N' hJa hJm hJr (by simpa using hJl) hJs
                    (by simpa using hJb) hJp f c hr) ρ hf
          have htail := stopped_retry_tail_mean used first u (H : ℚ)
            (by positivity) husedBound husedCausal hfirstCausal
            hhalf hstop hconditional
          rw [hcostSum]
          have hCoeff : (retryCoefficient n m r targetCap Q : ℚ) =
              2 * C + 70 := by simp [C, retryCoefficient, Nat.cast_add,
                Nat.cast_mul]
          rw [hCoeff]
          rw [hCoeff] at htail
          nlinarith only [hq, hpmean, htail,
            show (0 : ℚ) ≤ 2 ^ N by positivity]

/-- The four deterministic assignments before the retry while loop cost
exactly eight steps and leave the canonical ready setup state. -/
lemma source_setup_decompose
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap : ℕ)
    (hcap : R.I.σ.vars "initialRetryCap" = attemptCap)
    (hcapB : attemptCap < B)
    {τ : Env} {cost : ℕ}
    (hrun : BigStepB B initialSamplerRetriesSource R.I.σ τ cost) :
    ∃ loopCost,
      BigStepB B
        (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
        (R.withSetup attemptCap).I.σ τ loopCost ∧
      cost ≤ 8 + loopCost := by
  let σ₁ := R.I.σ.setVar "initialDomainSize" m
  let σ₂ := σ₁.setVar "initialBatchTarget" r
  let σ₃ := σ₂.setVar "initialRetriesLeft" attemptCap
  let σ₄ := σ₃.setVar "initialRetryStatus" 0
  have hfirstEval : (Expr.var "drawModulus").evalB B R.I.σ = some m := by
    rw [evalB_var_iff]
    exact ⟨R.I.hdrawModulus.symm, by rw [R.I.hdrawModulus]; exact R.I.hmB⟩
  have hfirst : Run B (.assign "initialDomainSize" (.var "drawModulus"))
      R.I.σ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (x := "initialDomainSize") hfirstEval)
  have hsecondEval : (Expr.var "batchTarget").evalB B σ₁ = some r := by
    rw [evalB_var_iff]
    constructor
    · simpa [σ₁] using R.I.hbatchTarget.symm
    · simpa [σ₁, R.I.hbatchTarget] using R.I.hrB
  have hsecond : Run B (.assign "initialBatchTarget" (.var "batchTarget"))
      σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (x := "initialBatchTarget") hsecondEval)
  have hthirdEval : (Expr.var "initialRetryCap").evalB B σ₂ =
      some attemptCap := by
    rw [evalB_var_iff]
    constructor
    · simpa [σ₂, σ₁] using hcap.symm
    · simpa [σ₂, σ₁, hcap] using hcapB
  have hthird : Run B (.assign "initialRetriesLeft" (.var "initialRetryCap"))
      σ₂ σ₃ 2 := by
    simpa [σ₃] using (Run.assign (x := "initialRetriesLeft") hthirdEval)
  have hfourth : Run B (.assign "initialRetryStatus" (.lit 0))
      σ₃ σ₄ 2 := by
    simpa [σ₄] using
      (Run.assign (x := "initialRetryStatus") (evalB_lit (by omega : 0 < B)))
  unfold initialSamplerRetriesSource at hrun
  cases hrun with
  | seq h₁ hrest₁ =>
    cases hrest₁ with
    | seq h₂ hrest₂ =>
      cases hrest₂ with
      | seq h₃ hrest₃ =>
        cases hrest₃ with
        | seq h₄ hloop =>
          obtain ⟨_, hk₁, hc₁⟩ := hfirst
          have he₁ := BigStep.unique h₁.bigStep hc₁.bigStep
          obtain ⟨_, hk₂, hc₂⟩ := hsecond
          have he₂ := (BigStep.unique
            (by simpa [he₁.1] using h₂.bigStep) hc₂.bigStep)
          obtain ⟨_, hk₃, hc₃⟩ := hthird
          have he₃ := (BigStep.unique
            (by simpa [he₂.1] using h₃.bigStep) hc₃.bigStep)
          obtain ⟨_, hk₄, hc₄⟩ := hfourth
          have he₄ := (BigStep.unique
            (by simpa [he₃.1] using h₄.bigStep) hc₄.bigStep)
          have hloop' : ∃ loopCost, BigStepB B
              (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
              (R.withSetup attemptCap).I.σ τ loopCost := by
            exact ⟨_, by simpa [ReadyInput.withSetup, σ₄, σ₃, σ₂, σ₁, he₄.1]
              using hloop⟩
          obtain ⟨loopCost, hloop'⟩ := hloop'
          refine ⟨loopCost, hloop', ?_⟩
          have hEqCost := (BigStep.unique
            (by simpa [ReadyInput.withSetup, σ₄, σ₃, σ₂, σ₁, he₄.1]
              using hloop.bigStep) hloop'.bigStep).2
          omega

/-- Exact source-program mean, including its four saved-register setup
assignments. -/
lemma actual_source_mean
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap N : ℕ)
    (hcap : R.I.σ.vars "initialRetryCap" = attemptCap)
    (hcapB : attemptCap < B)
    (hbudget : attemptCap * attemptBitBudget n m r t ≤ N)
    (hper : attemptBitBudget n m r t ≤ N)
    (hmass : SamplerWeightedRetries.badMass
      (SamplerInitialRetries.outcomeWeight A
        (activeVertices n R.I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r)
      (SamplerInitialRetries.outcomeBad A
        (activeVertices n R.I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r k cap) ≤ (1 / 2 : ℚ))
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B initialSamplerRetriesSource
      (R.reinput (List.ofFn ρ)
        (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ)) :
    (∑ ρ, (cost ρ : ℚ)) ≤
      (retryCoefficient n m r targetCap Q + 8) * 2 ^ N := by
  classical
  let S := R.withSetup attemptCap
  have hSactive : S.I.activeB = R.I.activeB := rfl
  have hSM : S.I.σ.vars "initialDomainSize" = m := by
    simp [S, ReadyInput.withSetup]
  have hSR : S.I.σ.vars "initialBatchTarget" = r := by
    simp [S, ReadyInput.withSetup]
  have hSleft : S.I.σ.vars "initialRetriesLeft" = attemptCap := by
    simp [S, ReadyInput.withSetup]
  have hSstatus : S.I.σ.vars "initialRetryStatus" = 0 := by
    simp [S, ReadyInput.withSetup]
  have hSbits : S.I.bits = R.I.bits := rfl
  have hd (ρ : Tape N) :=
    source_setup_decompose
      (R.reinput (List.ofFn ρ)
        (by simpa [attemptBitBudget] using hper))
      attemptCap (by simpa [ReadyInput.reinput_state] using hcap)
      hcapB (hrun ρ)
  choose loopCost hloop hcost using hd
  have hloop' (ρ : Tape N) : BigStepB B
      (.while (.eq (.var "initialRetryStatus") (.lit 0)) initialRetryBody)
      (S.reinput (List.ofFn ρ)
        (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (loopCost ρ) := by
    simpa [S, ReadyInput.withSetup, ReadyInput.reinput_state, Env.setVar]
      using hloop ρ
  have hmean := actual_retry_mean R.I.activeB hmass attemptCap N S
    hSactive hSM hSR hSleft hSstatus hcapB hbudget hper
    final loopCost hloop'
  have hsum : (∑ ρ, (cost ρ : ℚ)) ≤
      8 * 2 ^ N + (∑ ρ, (loopCost ρ : ℚ)) := by
    calc
      _ ≤ ∑ ρ : Tape N, ((8 : ℚ) + loopCost ρ) := by
        apply Finset.sum_le_sum
        intro ρ _
        exact_mod_cast hcost ρ
      _ = _ := by simp [Finset.sum_add_distrib, Nat.cast_pow, mul_comm]
  nlinarith only [hsum, hmean]

end Lax457868Proofs.InitialRetryMean
