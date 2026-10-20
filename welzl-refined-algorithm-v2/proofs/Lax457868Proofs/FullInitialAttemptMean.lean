import Lax457868Proofs.InitialAttemptMean
import Lax457868Proofs.InitialSamplerRetriesSource

/-! Expected cost of the actual full initial attempt, including the
computed exception set and acceptance decision. -/
namespace Lax457868Proofs.FullInitialAttemptMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.FullInitialAttempt
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

variable {B n m domainCap r t bufferCap targetCap Q k cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

lemma actual_full_decompose
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {τ : Env} {cost : ℕ} (hrun : BigStepB B fullInitialAttempt R.I.σ τ cost) :
    ∃ σsel j, BigStepB B initialSamplerAttempt R.I.σ σsel j ∧
      cost ≤ j + (414*n+300*targetCap+341) := by
  obtain ⟨σsel,σf,tape,tail,values,used,failed,stageCost,hbits,htrace,hsel,
      hfull,hrest⟩ := fullInitialAttempt_run_bits_withTail R.I
    R.hactiveA R.hdegree R.hinter R.hneighbors R.hexceptionFlags
    R.hexceptionList R.hnearBound R.hexceptionCap R.hnB R.hkB R.hcapB
  change BigStepB B (initialSamplerAttempt.seq _) R.I.σ τ cost at hrun
  cases hrun with
  | seq ha hb =>
    obtain ⟨j,hj,hs⟩ := hsel
    have he := BigStep.unique ha.bigStep hs.bigStep
    rcases he with ⟨he,hcost⟩
    subst_vars
    obtain ⟨q,hq,hqrun⟩ := hfull.2
    have heq := BigStep.unique hb.bigStep hqrun.bigStep
    refine ⟨_,_,ha,?_⟩
    omega

/-- Every actual full-attempt execution satisfies the same mean bound.
No upper-bound execution cost is substituted for the actual machine count. -/
lemma actual_full_mean
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (N : ℕ) (hb : attemptBitBudget n m r t ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B fullInitialAttempt
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
      (final ρ) (cost ρ)) :
    (∑ ρ, cost ρ) ≤
      (r*(42*Nat.clog 2 m+133)+12*Nat.clog 2 m+1180*n+
        624*targetCap+64*Q+571)*2^N := by
  classical
  let J (ρ : Tape N) := R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hb)
  have hd (ρ : Tape N) := actual_full_decompose (J ρ) (hrun ρ)
  choose sel selCost hsel hcost using hd
  have hm := InitialAttemptMean.actual_initial_mean R.I N
    (by simpa [attemptBitBudget] using hb) sel selCost hsel
  have hs := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hcost ρ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_tape, nsmul_eq_mul] at hs
  nlinarith

end Lax457868Proofs.FullInitialAttemptMean
