import Lax457868Proofs.ExceptionRepairMean
import Lax457868Proofs.RefinedRepairCharges

/-! Average the actual chronological exception loop over its unread suffix. -/
set_option maxHeartbeats 1000000
namespace Lax457868Proofs.ExceptionLoopMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ExceptionRepairMean
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRepairCharge
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
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
    ((next.σ.vars "repairRetryStatus" = 2 ∨
        next.σ.vars "repairRetryStatus" = 3) ∧
      next.σ.vars "exceptionIndex" = i ∧ next.σ.vars "exceptionStop" = i)
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
    · exact Or.inr ⟨hf.1,hf.2.1,hf.2.2.1⟩

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

/-- A source call cannot consume beyond its uniform reserved bit segment. -/
lemma stepRecord_used_bound
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i N : ℕ) (hb : cap * (s*t*Nat.clog 2 n) ≤ N)
    (ρ : FlatTape N)
    (z : StepRecord (R.reinput (flatBits ρ)) i) :
    z.used * Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card ≤ N := by
  have hlog : Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card ≤
      Nat.clog 2 n := Nat.clog_mono_right 2 (far_card_le R (R.exceptionList i))
  have hu : z.used ≤ cap*(s*t) :=
    z.used_le.trans (Nat.mul_le_mul_right (s*t) z.attempts_le)
  calc
    _ ≤ (cap*(s*t))*Nat.clog 2 n := by gcongr
    _ = cap*(s*t*Nat.clog 2 n) := by ring
    _ ≤ N := hb

/-- Determinism of the actual body fixes the poststate and stopping position
on every completion of its consumed Boolean prefix. -/
lemma stepRecord_same_prefix
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i N : ℕ) (hb : cap * (s*t*Nat.clog 2 n) ≤ N)
    (F : ∀ ρ : FlatTape N, StepRecord (R.reinput (flatBits ρ)) i)
    (ρ τ : FlatTape N)
    (hp : (flatBits ρ).take
      ((F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card) =
      (flatBits τ).take
      ((F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card)) :
    (F τ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card =
      (F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card ∧
    (F τ).next.σ = {(F ρ).next.σ with inp :=
      ((flatBits τ).drop ((F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card)).map Bool.toNat ++ R.rest} := by
  have hrestρ : (F ρ).next.rest = R.rest := (F ρ).fixed.2.2.2.2.2.1
  have hrestτ : (F τ).next.rest = R.rest := (F τ).fixed.2.2.2.2.2.1
  have hinρ : (F ρ).next.σ.inp =
      ((flatBits ρ).drop ((F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card)).map Bool.toNat ++ R.rest := by
    rw [(F ρ).next.hinput, (F ρ).bits, hrestρ]
    rfl
  have hinτ : (F τ).next.σ.inp =
      ((flatBits τ).drop ((F τ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card)).map Bool.toNat ++ R.rest := by
    rw [(F τ).next.hinput, (F τ).bits, hrestτ]
    rfl
  have hrρ : Run B exceptionRepairBody
      {R.σ with inp := (flatBits ρ).map Bool.toNat ++ R.rest}
      (F ρ).next.σ (F ρ).bodyCost := by
    simpa only [LoopInput.reinput_state] using (F ρ).run
  have hrτ : Run B exceptionRepairBody
      {R.σ with inp := (flatBits τ).map Bool.toNat ++ R.rest}
      (F τ).next.σ (F τ).bodyCost := by
    simpa only [LoopInput.reinput_state] using (F τ).run
  exact bool_run_same_prefix (flatBits ρ) (flatBits τ) R.rest
    hrρ hrτ hinρ hinτ
    (by simpa [flatBits] using stepRecord_used_bound R i N hb ρ (F ρ))
    (by simpa [flatBits] using stepRecord_used_bound R i N hb τ (F τ)) hp

lemma meanStepCharge_eq_of_sameFixed
    {Wnext : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wnext)
    (h : SameFixed R Rnext) (b : ℕ) :
    meanStepCharge Rnext b = meanStepCharge R b := by
  rcases h with ⟨_, hr, hz, hl, ho, _, _⟩
  simp only [meanStepCharge, hr, hz, hl, ho]

/-- One actual true-guard while step is charged by the chosen actual body
certificate, and the remaining source loop starts in its exact poststate. -/
lemma while_step_decompose
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i : ℕ) (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e) (hi : i < e)
    (z : StepRecord R i) (final : Env) (cost : ℕ)
    (hrun : BigStepB B
      (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
        exceptionRepairBody) R.σ final cost) :
    ∃ postCost,
      BigStepB B
        (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
          exceptionRepairBody) z.next.σ final postCost ∧
      cost ≤ z.bodyCost + 4 + postCost := by
  have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
  have heB : e < B := by have := R.heLe; have := R.hn1B; omega
  have hg : (Cond.lt (.var "exceptionIndex")
      (.var "exceptionStop")).evalB B R.σ = some true := by
    simpa [hi] using loop_guard hindex hstop hiB heB
  cases hrun with
  | while_false hfalse => simp [hg] at hfalse
  | while_true _ hbody htail =>
    obtain ⟨k, hk, hbody'⟩ := z.run
    obtain ⟨hstate, hcost⟩ := BigStep.unique hbody.bigStep hbody'.bigStep
    subst_vars
    refine ⟨_, htail, ?_⟩
    simp only [Cond.size, Expr.size]
    omega

/-- Average the exact bounded-source cost of the remaining while loop over
all completions of a fixed prepared repair state. -/
lemma while_mean_aux (fuel : ℕ) :
    ∀ {Wcurrent : Finset ℕ}
      (R : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wcurrent) (i N : ℕ),
      i + fuel = e →
      R.σ.vars "exceptionIndex" = i →
      R.σ.vars "exceptionStop" = e →
      R.σ.vars "repairRetryStatus" = 1 →
      fuel * (cap * (s*t*Nat.clog 2 n)) ≤ N →
      (∀ b ∈ E, 2*k/3 < (farDomain G A R.rep b).card →
        2*(SamplerLocalSuccess.localTrialFailureSet
          (numericNeighborhood G) groupedB Wbase b
          (farDomain G A R.rep b) s).card ≤
          (farDomain G A R.rep b).card^s) →
      2 ≤ k →
      ∀ (final : FlatTape N → Env) (cost : FlatTape N → ℕ),
      (∀ ρ, BigStepB B
        (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
          exceptionRepairBody)
        (R.reinput (flatBits ρ)).σ (final ρ) (cost ρ)) →
      (∑ ρ, (cost ρ : ℚ)) ≤
        ((4 + ∑ j ∈ Finset.Ico i e,
          meanStepCharge R (R.exceptionList j) : ℕ) : ℚ) * 2^N := by
  induction fuel with
  | zero =>
      intro Wcurrent R i N hremaining hindex hstop hstatus hbudget hhalf hk
        final cost hrun
      have hie : i = e := by omega
      have heB : e < B := by have := R.heLe; have := R.hn1B; omega
      have hcost (ρ : FlatTape N) : cost ρ = 4 := by
        have hg : (Cond.lt (.var "exceptionIndex")
            (.var "exceptionStop")).evalB B (R.reinput (flatBits ρ)).σ =
            some false := by
          simpa [LoopInput.reinput_state, hie] using
            loop_guard hindex hstop (by omega : i < B) heB
        have hh : BigStepB B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody) (R.reinput (flatBits ρ)).σ
              (R.reinput (flatBits ρ)).σ 4 := by
          simpa [Cond.size, Expr.size] using
            (BigStepB.while_false (c := exceptionRepairBody) hg)
        exact (BigStep.unique (hrun ρ).bigStep hh.bigStep).2
      simp [hcost, hie, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        mul_comm]
  | succ fuel ih =>
      intro Wcurrent R i N hremaining hindex hstop hstatus hbudget hhalf hk
        final cost hrun
      have hi : i < e := by omega
      let C := cap * (s*t*Nat.clog 2 n)
      have hcall : cap * (s*t*Nat.clog 2
          (farDomain G A R.rep (R.exceptionList i)).card) ≤ N := by
        have hclog := Nat.clog_mono_right 2
          (far_card_le R (R.exceptionList i))
        calc
          _ ≤ C := by dsimp [C]; gcongr
          _ ≤ (fuel+1)*C := by
            simpa using Nat.mul_le_mul_right C (show 1 ≤ fuel+1 by omega)
          _ ≤ N := hbudget
      have hC : C ≤ N := by
        have h := Nat.mul_le_mul_right C (show 1 ≤ fuel+1 by omega)
        have h' : C ≤ (fuel+1)*C := by simpa only [one_mul] using h
        exact h'.trans hbudget
      let F : ∀ ρ : FlatTape N, StepRecord (R.reinput (flatBits ρ)) i :=
        fun ρ => Classical.choice (stepRecord_exists
          (R.reinput (flatBits ρ)) i
          (by simpa [LoopInput.reinput_state] using hindex)
          (by simpa [LoopInput.reinput_state] using hstop) hi
          (by simpa [LoopInput.reinput] using hcall))
      let used (ρ : FlatTape N) := (F ρ).used * Nat.clog 2
        (farDomain G A R.rep (R.exceptionList i)).card
      have hu (ρ : FlatTape N) : used ρ ≤ N :=
        stepRecord_used_bound R i N hC ρ (F ρ)
      have hs (ρ τ : FlatTape N)
          (hp : (flatBits ρ).take (used ρ) = (flatBits τ).take (used ρ)) :
          used τ = used ρ ∧
          (F τ).next.σ = {(F ρ).next.σ with inp :=
            ((flatBits τ).drop (used ρ)).map Bool.toNat ++ R.rest} :=
        stepRecord_same_prefix R i N hC F ρ τ hp
      have hdec (ρ : FlatTape N) : ∃ postCost,
          BigStepB B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody)
            (F ρ).next.σ (final ρ) postCost ∧
          cost ρ ≤ (F ρ).bodyCost + 4 + postCost :=
        while_step_decompose (R.reinput (flatBits ρ)) i
          (by simpa [LoopInput.reinput_state] using hindex)
          (by simpa [LoopInput.reinput_state] using hstop) hi
          (F ρ) (final ρ) (cost ρ) (hrun ρ)
      choose postCost hpost hcost using hdec
      have hpostmean : (∑ ρ, (postCost ρ : ℚ)) ≤
          ((4 + ∑ j ∈ Finset.Ico (i+1) e,
            meanStepCharge R (R.exceptionList j) : ℕ) : ℚ) * 2^N := by
        let M : ℕ := 4 + ∑ j ∈ Finset.Ico (i+1) e,
          meanStepCharge R (R.exceptionList j)
        have hcausal (ρ τ : FlatTape N)
            (hp : (flatBits ρ).take (used ρ) =
              (flatBits τ).take (used ρ)) : used τ = used ρ :=
          (hs ρ τ hp).1
        have hfiber (ρ : FlatTape N) :
            (∑ tail : FlatTape (N - used ρ),
              (postCost ((splitEquiv (hu ρ)).symm
                ((splitEquiv (hu ρ) ρ).1, tail)) : ℚ)) ≤
              (M : ℚ) * 2^(N - used ρ) := by
          let Rnext := (F ρ).next
          have hfixed : SameFixed R Rnext := by
            rcases (F ρ).fixed with ⟨hl, hr, hz, hc, ho, ht, hq⟩
            exact ⟨hl, hr, hz, hc, ho, ht,
              by simpa [LoopInput.reinput_state] using hq⟩
          have hbits : Rnext.bits = (flatBits ρ).drop (used ρ) :=
            (F ρ).bits
          have hrest : Rnext.rest = R.rest := hfixed.2.2.2.2.2.1
          have htailN : Rnext.bits.length = N - used ρ := by
            rw [hbits, List.length_drop, flatBits_length]
          have htailBudget : fuel*C ≤ N - used ρ := by
            have husedC : used ρ ≤ C := by
              have hlog := Nat.clog_mono_right 2
                (far_card_le R (R.exceptionList i))
              have hattempts : (F ρ).used ≤ cap*(s*t) :=
                (F ρ).used_le.trans
                  (Nat.mul_le_mul_right (s*t) (F ρ).attempts_le)
              dsimp [used, C]
              calc
                _ ≤ (cap*(s*t))*Nat.clog 2 n := by gcongr
                _ = _ := by ring
            have hsum : fuel*C + used ρ ≤ N := by
              calc
                _ ≤ fuel*C + C := by omega
                _ = (fuel+1)*C := by ring
                _ ≤ N := hbudget
            omega
          have hcharge (b : ℕ) : meanStepCharge Rnext b = meanStepCharge R b :=
            meanStepCharge_eq_of_sameFixed R Rnext hfixed b
          have hentry : Rnext.exceptionList = R.exceptionList := hfixed.1
          have hrep : Rnext.rep = R.rep := hfixed.2.1
          have hcompletion (tail : FlatTape (N - used ρ)) :
              let τ := (splitEquiv (hu ρ)).symm
                ((splitEquiv (hu ρ) ρ).1, tail)
              (F τ).next.σ = (Rnext.reinput (flatBits tail)).σ := by
            intro τ
            have hp : (flatBits ρ).take (used ρ) =
                (flatBits τ).take (used ρ) := by
              rw [show flatBits ρ = List.ofFn ρ by rfl,
                show flatBits τ = List.ofFn τ by rfl,
                prefix_of_split (hu ρ), prefix_of_split (hu ρ)]
              simp [τ]
            have heq := (hs ρ τ hp).2
            have hdrop : (flatBits τ).drop (used ρ) = flatBits tail := by
              have hsplit := boolTape_split (hu ρ) τ
              have hpair : splitEquiv (hu ρ) τ =
                  ((splitEquiv (hu ρ) ρ).1, tail) :=
                Equiv.apply_symm_apply _ _
              change (List.ofFn τ).drop (used ρ) = List.ofFn tail
              rw [hsplit, hpair]
              simp
            rw [LoopInput.reinput_state, ← hdrop, hrest]
            exact heq
          by_cases hsuccess : Rnext.σ.vars "repairRetryStatus" = 1
          · have hout := (F ρ).outcome
            have hsuccess' : (F ρ).next.σ.vars "repairRetryStatus" = 1 := hsuccess
            have hnext : Rnext.σ.vars "exceptionIndex" = i+1 ∧
                Rnext.σ.vars "exceptionStop" = e := by
              rcases hout with hh | hh
              · exact ⟨hh.2.1, hh.2.2⟩
              · rcases hh.1 with htwo | hthree <;> omega
            let finals (tail : FlatTape (N - used ρ)) :=
              final ((splitEquiv (hu ρ)).symm
                ((splitEquiv (hu ρ) ρ).1, tail))
            let costs (tail : FlatTape (N - used ρ)) :=
              postCost ((splitEquiv (hu ρ)).symm
                ((splitEquiv (hu ρ) ρ).1, tail))
            have hrunTail (tail : FlatTape (N - used ρ)) :
                BigStepB B
                  (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
                    exceptionRepairBody)
                  (Rnext.reinput (flatBits tail)).σ (finals tail) (costs tail) := by
              simpa only [finals, costs, ← hcompletion tail] using
                hpost ((splitEquiv (hu ρ)).symm
                  ((splitEquiv (hu ρ) ρ).1, tail))
            have hhalfNext : ∀ b ∈ E,
                2*k/3 < (farDomain G A Rnext.rep b).card →
                2*(SamplerLocalSuccess.localTrialFailureSet
                  (numericNeighborhood G) groupedB Wbase b
                  (farDomain G A Rnext.rep b) s).card ≤
                  (farDomain G A Rnext.rep b).card^s := by
              rw [hrep]
              exact hhalf
            have hm := ih Rnext (i+1) (N-used ρ)
              (by omega) hnext.1 hnext.2 hsuccess
              (by simpa only [C] using htailBudget) hhalfNext hk
              finals costs hrunTail
            have hsumEq : (∑ j ∈ Finset.Ico (i+1) e,
                meanStepCharge Rnext (Rnext.exceptionList j)) =
                ∑ j ∈ Finset.Ico (i+1) e,
                  meanStepCharge R (R.exceptionList j) := by
              simp only [hentry, hcharge]
            simpa only [M, hsumEq, finals, costs] using hm
          · have hstopNext : Rnext.σ.vars "exceptionIndex" = i ∧
                Rnext.σ.vars "exceptionStop" = i := by
              rcases (F ρ).outcome with hh | hh
              · exact False.elim (hsuccess hh.1)
              · exact ⟨hh.2.1, hh.2.2⟩
            have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
            have hcostTail (tail : FlatTape (N - used ρ)) :
                postCost ((splitEquiv (hu ρ)).symm
                  ((splitEquiv (hu ρ) ρ).1, tail)) = 4 := by
              let τ := (splitEquiv (hu ρ)).symm
                ((splitEquiv (hu ρ) ρ).1, tail)
              have hsame := hcompletion tail
              have hg : (Cond.lt (.var "exceptionIndex")
                  (.var "exceptionStop")).evalB B (F τ).next.σ =
                  some false := by
                rw [hsame]
                simpa [LoopInput.reinput_state, hstopNext.1, hstopNext.2]
                  using loop_guard hstopNext.1 hstopNext.2 hiB hiB
              have hfalse : BigStepB B
                  (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
                    exceptionRepairBody) (F τ).next.σ (F τ).next.σ 4 := by
                simpa [Cond.size, Expr.size] using
                  (BigStepB.while_false (c := exceptionRepairBody) hg)
              exact (BigStep.unique (hpost τ).bigStep hfalse.bigStep).2
            simp only [hcostTail, Finset.sum_const, Finset.card_univ,
              Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
              nsmul_eq_mul]
            have hfour : (4:ℚ) ≤ M := by
              dsimp [M]
              exact_mod_cast (Nat.le_add_right 4 _)
            simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
              (mul_le_mul_of_nonneg_right hfour (by positivity :
                (0:ℚ) ≤ 2^(N-used ρ)))
        have havg := sum_le_of_stopped_prefix used hu hcausal
          (fun ρ => (postCost ρ : ℚ)) (fun _ => (M : ℚ))
          (by intros; rfl) hfiber
        have hcard : (∑ _ρ : FlatTape N, (M : ℚ)) =
            (M : ℚ)*2^N := by
          simp [Finset.sum_const, Finset.card_univ,
            Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            nsmul_eq_mul, mul_comm]
        simpa only [M, hcard] using havg
      have hbodymean := body_mean R i N hk hcall
        (hhalf (R.exceptionList i)
          (by
            apply (R.hprefix.2 (R.exceptionList i)).mp
            have hil : i < (Stack.toList e R.exceptionList).length := by
              simpa [Stack.toList] using hi
            have hget : (Stack.toList e R.exceptionList)[i] = R.exceptionList i := by
              simp [Stack.toList, hi]
            rw [← hget]
            exact List.getElem_mem hil)) F
      have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) =>
        (show (cost ρ:ℚ) ≤ ((F ρ).bodyCost+4:ℚ) + postCost ρ by
          exact_mod_cast hcost ρ))
      have hsplit : (∑ j ∈ Finset.Ico i e,
          meanStepCharge R (R.exceptionList j)) =
          meanStepCharge R (R.exceptionList i) +
            ∑ j ∈ Finset.Ico (i+1) e,
              meanStepCharge R (R.exceptionList j) := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi]
      simp only [Finset.sum_add_distrib] at hsum hbodymean
      rw [hsplit]
      push_cast at hsum hbodymean hpostmean ⊢
      nlinarith [hbodymean, hpostmean]

/-- The actual packed exception source has mean cost bounded by the sum of
the per-exception charges, including the initial assignments and final pack. -/
lemma packed_mean
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (N : ℕ) (hk : 2 ≤ k)
    (hbudget : E.card * (cap * (s*t*Nat.clog 2 n)) ≤ N)
    (hhalf : ∀ b ∈ E, 2*k/3 < (farDomain G A R.rep b).card →
      2*(SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b
        (farDomain G A R.rep b) s).card ≤
        (farDomain G A R.rep b).card^s)
    (final : FlatTape N → Env) (cost : FlatTape N → ℕ)
    (hrun : ∀ ρ : FlatTape N,
      BigStepB B exceptionRepairPackedSource
        (R.reinput (flatBits ρ)).σ (final ρ) (cost ρ)) :
    (∑ ρ, (cost ρ : ℚ)) ≤
      ((23 + 20*n + ∑ b ∈ E, meanStepCharge R b : ℕ) : ℚ) * 2^N := by
  classical
  have hset : (Stack.toList e R.exceptionList).toFinset = E := by
    ext b
    simpa using R.hprefix.2 b
  have hecard : E.card = e := by
    rw [← hset, List.toFinset_card_of_nodup R.hprefix.1]
    simp [Stack.toList]
  have hbudget' : e*(cap*(s*t*Nat.clog 2 n)) ≤ N := by
    simpa only [hecard] using hbudget
  obtain ⟨I, rinit, hbitsI, hfixedI, hindexI, hstopI, hstatusI⟩ :=
    initialize_loop R
  have hrestI : I.rest = R.rest := hfixedI.2.2.2.2.2.1
  have hin : R.σ.inp = [] ++ I.σ.inp := by
    simp only [List.nil_append, R.hinput, I.hinput, hbitsI, hrestI]
  have hinitρ (ρ : FlatTape N) :
      Run B exceptionRepairInit (R.reinput (flatBits ρ)).σ
        (I.reinput (flatBits ρ)).σ 6 := by
    have hh := run_replace_consumed_suffix rinit [] hin
      ((flatBits ρ).map Bool.toNat ++ R.rest)
    simpa [LoopInput.reinput_state, hrestI] using hh
  have hdec (ρ : FlatTape N) :
      ∃ (σloop : Env) (loopCost : ℕ),
        BigStepB B
          (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
            exceptionRepairBody)
          (I.reinput (flatBits ρ)).σ σloop loopCost ∧
        cost ρ ≤ 6 + loopCost + (20*n+13) := by
    let Rρ := R.reinput (flatBits ρ)
    have hbρ : e*(cap*(s*t*Nat.clog 2 n)) ≤ Rρ.bits.length := by
      simpa [Rρ, LoopInput.reinput, flatBits_length] using hbudget'
    obtain ⟨Wfinal, Rfinal, steps, rloop, _hbits, _hfixed,
      _hmap, _hvalid, hout⟩ := exceptionRepairLoop_run Rρ hbρ
    have hr := hrun ρ
    change BigStepB B
      (exceptionRepairLoopSource.seq
        (.ite (.eq (.var "repairRetryStatus") (.lit 1))
          packMarkedSamples .skip)) Rρ.σ (final ρ) (cost ρ) at hr
    generalize htotal : cost ρ = total at hr ⊢
    cases hr with
    | seq hloop htail =>
      rename_i σloop loopCost tailCost
      change BigStepB B
        (exceptionRepairInit.seq
          (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
            exceptionRepairBody)) Rρ.σ σloop loopCost at hloop
      cases hloop with
      | seq hinit hwhile =>
        rename_i σinit initCost whileCost
        obtain ⟨actualInit, hactualInit, hinitBig⟩ := hinitρ ρ
        have hinitEq := BigStep.unique hinit.bigStep hinitBig.bigStep
        obtain ⟨actualLoop, _hactualLoop, hloopBig⟩ := rloop
        have hloopEq := BigStep.unique
          (BigStepB.seq hinit hwhile).bigStep hloopBig.bigStep
        have htailLe : tailCost ≤ 20*n+13 := by
          have hstate : σloop = Rfinal.σ := hloopEq.1
          subst σloop
          have honeB : 1 < B := by have := R.hthreeB; omega
          rcases hout with hsuccess | hfailure
          · have hstatus := hsuccess.1
            have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
                B Rfinal.σ = some true := by
              simpa [hstatus] using evalB_condEq
                (evalB_var (by rw [hstatus]; exact honeB :
                  Rfinal.σ.vars "repairRetryStatus" < B))
                (evalB_lit honeB)
            have hflags01 : ∀ v < n, setFlag Wfinal v ≤ 1 := by
              intro v _
              by_cases hv : v ∈ Wfinal <;> simp [setFlag, hv]
            have hnB : n < B := by have := R.hn1B; omega
            obtain ⟨σpack, packed, rpack, _⟩ :=
              packMarkedSamples_run Rfinal.hn Rfinal.hsample Rfinal.hord
                hflags01 hnB honeB
            have rt : Run B
                (.ite (.eq (.var "repairRetryStatus") (.lit 1))
                  packMarkedSamples .skip) Rfinal.σ σpack (20*n+13) := by
              have h := Run.ite_true (d := .skip) hguard rpack
              simpa [show 4 + (20*n+9) = 20*n+13 by omega] using h
            obtain ⟨actualTail, hactualTail, htailBig⟩ := rt
            have hc := (BigStep.unique htail.bigStep htailBig.bigStep).2
            omega
          · have hstatus : Rfinal.σ.vars "repairRetryStatus" ≠ 1 := by
              rcases hfailure.1 with htwo | hthree <;> omega
            have hstatusB : Rfinal.σ.vars "repairRetryStatus" < B := by
              rcases hfailure.1 with htwo | hthree <;> have := R.hthreeB <;> omega
            have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
                B Rfinal.σ = some false := by
              simpa [hstatus] using evalB_condEq
                (evalB_var hstatusB) (evalB_lit honeB)
            have rt : Run B
                (.ite (.eq (.var "repairRetryStatus") (.lit 1))
                  packMarkedSamples .skip) Rfinal.σ Rfinal.σ 5 := by
              simpa [Cond.size, Expr.size] using
                (Run.ite_false (c := packMarkedSamples) hguard Run.skip)
            obtain ⟨actualTail, hactualTail, htailBig⟩ := rt
            have hc := (BigStep.unique htail.bigStep htailBig.bigStep).2
            omega
        refine ⟨σloop, whileCost, ?_, ?_⟩
        · simpa [Rρ, hinitEq.1] using hwhile
        · have hc := hinitEq.2
          omega
  choose finalWhile loopCost hwhile hcost using hdec
  have hhalfI : ∀ b ∈ E,
      2*k/3 < (farDomain G A I.rep b).card →
      2*(SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b
        (farDomain G A I.rep b) s).card ≤
        (farDomain G A I.rep b).card^s := by
    rw [hfixedI.2.1]
    exact hhalf
  have hmean := while_mean_aux (B := B) (n := n) (s := s) (t := t)
    (bufferCap := bufferCap) (targetCap := targetCap) (q := q)
    (cap := cap) (k := k) (e := e) (G := G) (x := x)
    (E := E) (groupedB := groupedB) (Wbase := Wbase) (A := A)
    e I 0 N (by omega) hindexI hstopI hstatusI hbudget'
    hhalfI hk finalWhile loopCost hwhile
  have hsumEq : (∑ j ∈ Finset.Ico 0 e,
      meanStepCharge I (I.exceptionList j)) =
      ∑ b ∈ E, meanStepCharge R b := by
    have hs := sum_slice_eq (start := 0) (size := e)
      (ord := R.exceptionList) (S := E) (by simpa using R.hprefix)
      (meanStepCharge R)
    calc
      _ = ∑ j ∈ Finset.Ico 0 e,
          meanStepCharge R (R.exceptionList j) := by
            simp [hfixedI.1, meanStepCharge_eq_of_sameFixed R I hfixedI]
      _ = _ := by simpa using hs
  have hbound := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) =>
    (show (cost ρ : ℚ) ≤ (6 + loopCost ρ + (20*n+13) : ℕ) by
      exact_mod_cast hcost ρ))
  rw [hsumEq] at hmean
  push_cast at hbound hmean ⊢
  simp only [Finset.sum_add_distrib] at hbound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul] at hbound
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
  nlinarith [hmean]

end Lax457868Proofs.ExceptionLoopMean
