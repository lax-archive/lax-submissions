import Lax457868Proofs.ExceptionRepairMean
import Lax457868Proofs.RefinedRepairCharges

/-! Average the actual chronological exception loop over its unread suffix. -/
set_option maxHeartbeats 1000000
namespace Lax457868Proofs.ExceptionLoopMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ExceptionRepairMean
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open scoped symmDiff BigOperators

variable {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}

structure StepRecord
    (R : LoopInput B n s t bufferCap targetCap q cap k e G x E groupedB Wbase A Wcurrent)
    (i : ℕ) where
  Wnext : Finset ℕ
  next : LoopInput B n s t bufferCap targetCap q cap k e G x E groupedB Wbase A Wnext
  attempts : ℕ
  used : ℕ
  bodyCost : ℕ
  run : Run B exceptionRepairBody R.σ next.σ bodyCost
  bound : bodyCost ≤ oneExceptionCharge x G A R.rep s
    (classScanCharge x R.size R.label R.ord (R.exceptionList i))
    (R.exceptionList i) k attempts used + 11
  attempts_le : attempts ≤ cap
  used_le : used ≤ attempts*(s*t)
  bits : next.bits = R.bits.drop
    (used*Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card)
  fixed : SameFixed R next
  outcome : (next.σ.vars "repairRetryStatus" = 1 ∧
    next.σ.vars "exceptionIndex" = i+1 ∧ next.σ.vars "exceptionStop" = e) ∨
    (next.σ.vars "exceptionIndex" = i ∧ next.σ.vars "exceptionStop" = i)
  far : 2*k/3 < (farDomain G A R.rep (R.exceptionList i)).card →
    FarStepTrace R i attempts used

lemma stepRecord_exists
    (R : LoopInput B n s t bufferCap targetCap q cap k e G x E groupedB Wbase A Wcurrent)
    (i : ℕ) (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e) (hi : i < e)
    (hb : cap*(s*t*Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card) ≤ R.bits.length) :
    Nonempty (StepRecord R i) := by
  obtain ⟨W,P,a,u,c,hr,hc,ha,hu,hbits,hfixed,ho,hfar,hfailed⟩ :=
    one_step_run_trace R hindex hstop hi hb
  refine ⟨⟨W,P,a,u,_,hr,?_,ha,hu,hbits,hfixed,?_,hfar⟩⟩
  · rw [hc]
    split_ifs <;> omega
  · rcases ho with hs | hf
    · exact Or.inl ⟨hs.1,hs.2.1,hs.2.2.1⟩
    · exact Or.inr ⟨hf.2.1,hf.2.2.1⟩

lemma far_card_le (R : LoopInput B n s t bufferCap targetCap q cap k e
    G x E groupedB Wbase A Wcurrent) (b : ℕ) :
    (farDomain G A R.rep b).card ≤ n := by
  have hsub : farDomain G A R.rep b ⊆ A := by
    intro v hv
    simp only [farDomain,Finset.mem_symmDiff,Finset.mem_inter] at hv
    tauto
  exact (Finset.card_le_card (hsub.trans R.hA)).trans (by simp)

/-- Include the source while guard and the success/failure bookkeeping in
one input-dependent per-exception mean charge. -/
noncomputable def meanStepCharge (R : LoopInput B n s t bufferCap targetCap q cap k e
    G x E groupedB Wbase A Wcurrent) (b : ℕ) : ℕ :=
  domainCharge x G A R.rep b + 2*classScanCharge x R.size R.label R.ord b +
    (12+60*s)*Nat.clog 2 n+278*s+157

lemma body_mean
    (R : LoopInput B n s t bufferCap targetCap q cap k e G x E groupedB Wbase A Wcurrent)
    (i N : ℕ) (hk : 2 ≤ k)
    (hb : cap*(s*t*Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card) ≤ N)
    (hh : 2*k/3 < (farDomain G A R.rep (R.exceptionList i)).card →
      2*(SamplerLocalSuccess.localTrialFailureSet (numericNeighborhood G) groupedB Wbase
        (R.exceptionList i) (farDomain G A R.rep (R.exceptionList i)) s).card ≤
        (farDomain G A R.rep (R.exceptionList i)).card^s)
    (F : ∀ ρ : FlatTape N, StepRecord (R.reinput (flatBits ρ)) i) :
    (∑ ρ, ((F ρ).bodyCost+4 : ℚ)) ≤
      (meanStepCharge R (R.exceptionList i) : ℚ)*2^N := by
  classical
  let b := R.exceptionList i
  let X := farDomain G A R.rep b
  let L := Nat.clog 2 X.card
  let scan := classScanCharge x R.size R.label R.ord b
  let D := domainCharge x G A R.rep b
  have hpoint (ρ : FlatTape N) : (F ρ).bodyCost ≤
      oneExceptionCharge x G A R.rep s scan b k (F ρ).attempts (F ρ).used+11 :=
    (F ρ).bound
  have hlog : L ≤ Nat.clog 2 n := Nat.clog_mono_right 2 (far_card_le R b)
  by_cases hf : 2*k/3 < X.card
  · have hX2 : 2 ≤ X.card := by omega
    have hL : 0 < L := by
      have hpow := Nat.le_pow_clog (by omega : 1 < 2) X.card
      by_contra hz
      have hzero : L = 0 := by omega
      change X.card ≤ 2^L at hpow
      rw [hzero] at hpow
      norm_num at hpow
      omega
    have hm := far_step_mean_any_tape R (i := i) (N := N)
      (by simpa [Nat.mul_assoc] using hb) hL (hh hf)
      (fun ρ => (F ρ).attempts) (fun ρ => (F ρ).used)
      (fun ρ => (F ρ).far hf)
      (fun ρ => ⟨(F ρ).attempts_le,(F ρ).used_le⟩)
    have hpointQ (ρ : FlatTape N) : ((F ρ).bodyCost+4 : ℚ) ≤
        (D+19 : ℕ) + localActualCharge L s scan (F ρ).attempts (F ρ).used := by
      have h := hpoint ρ
      rw [oneExceptionCharge_far_eq R.rep scan b (F ρ).attempts
        (F ρ).used (by simpa [X, b] using hf)] at h
      have hn : (F ρ).bodyCost + 4 ≤
          (D+19)+localActualCharge L s scan (F ρ).attempts (F ρ).used := by
        dsimp [D, L, X, b] at h ⊢
        omega
      exact_mod_cast hn
    have hs := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hpointQ ρ)
    have hcoef : D+19+localMeanBound L s scan ≤ meanStepCharge R b := by
      rw [localMeanBound_expanded]
      dsimp [meanStepCharge]
      have hmul := Nat.mul_le_mul_left (12+60*s) hlog
      omega
    have hc : (((D+19:ℕ):ℚ) + (localMeanBound L s scan:ℕ)) ≤
        (meanStepCharge R b:ℚ) := by
      exact_mod_cast hcoef
    have hs' : (∑ ρ, ((F ρ).bodyCost+4:ℚ)) ≤
        ((D+19:ℕ):ℚ) * (2:ℚ)^N +
          (∑ ρ, (localActualCharge L s scan (F ρ).attempts (F ρ).used:ℚ)) := by
      calc
        _ ≤ ∑ ρ, (((D+19:ℕ):ℚ) +
            (localActualCharge L s scan (F ρ).attempts (F ρ).used:ℚ)) := hs
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
    have hm' : (∑ ρ, (localActualCharge L s scan
          (F ρ).attempts (F ρ).used:ℚ)) ≤
        (localMeanBound L s scan:ℕ) * (2:ℚ)^N := by
      simpa only [Nat.cast_pow] using hm
    calc
      _ ≤ ((D+19:ℕ):ℚ) * (2:ℚ)^N +
          (∑ ρ, (localActualCharge L s scan (F ρ).attempts (F ρ).used:ℚ)) := hs'
      _ ≤ ((D+19:ℕ):ℚ) * (2:ℚ)^N +
          (localMeanBound L s scan:ℕ) * (2:ℚ)^N := by
        exact add_le_add_right hm' (((D+19:ℕ):ℚ) * (2:ℚ)^N)
      _ = (((D+19:ℕ):ℚ) + (localMeanBound L s scan:ℕ)) * (2:ℚ)^N := by
        rw [add_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · have hnear : X.card ≤ 2*k/3 := by omega
    have hcost (ρ : FlatTape N) : (F ρ).bodyCost+4 ≤ D+21 := by
      have h := hpoint ρ
      have hnear' : (((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (R.rep b) ∩ A))).card ≤ 2*k/3 := by
        simpa [X, farDomain] using hnear
      simp only [oneExceptionCharge, if_pos hnear'] at h
      dsimp [D, b] at h ⊢
      omega
    have hs := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) =>
      (show ((F ρ).bodyCost+4:ℚ) ≤ (D+21:ℕ) by exact_mod_cast hcost ρ))
    have hc : D+21 ≤ meanStepCharge R b := by dsimp [meanStepCharge,D]; omega
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul] at hs
    calc
      _ ≤ (D+21:ℕ)*(2^N:ℚ) := by simpa [mul_comm] using hs
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

end Lax457868Proofs.ExceptionLoopMean
