import Lax457868Proofs.FullInitialAttemptMean

/-! Mean bounds for the actual source retry loop. -/
namespace Lax457868Proofs.InitialRetryMean

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.FullInitialAttemptMean
open Lax457868Proofs.FullInitialAttempt
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

variable {B n m domainCap r t bufferCap targetCap Q k cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

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

end Lax457868Proofs.InitialRetryMean
