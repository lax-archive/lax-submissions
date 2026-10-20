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

end Lax457868Proofs.InitialRetryMean
