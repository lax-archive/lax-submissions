import Lax457868Proofs.InitialOutcomeCharge
import Lax457868Proofs.FullInitialAttemptMean

/-! Representative-row charges read from the actual source poststate. -/
namespace Lax457868Proofs.InitialPhysicalReward
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialFlatLaw
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.FullInitialAttempt
open Lax457868Proofs.SamplerInitialRetries
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

variable {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

lemma successful_selection_outcome
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (ρ : FlatTape I.bits.length) {τ : Env} {cost : ℕ}
    (hrun : Run B initialSamplerAttempt
      {I.σ with inp := (flatBits ρ).map Bool.toNat ++ I.rest} τ cost)
    (hb : τ.vars "batchFailed" = 0) (hp : τ.vars "repFailed" = 0) :
    ∃ ω : InitialOutcome A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r,
      ρ ∈ sourceInitialOutcomeFiber I ω ∧
      ∀ b ∈ activeVertices n I.activeB,
        (outcomeChoice A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r ω).representative b =
          (τ.arrs "repB").getD b 0 := by
  classical
  let J := reinputInitialAttempt I (flatBits ρ) (by simpa using I.hbudget)
  obtain ⟨σ,j,hj,ho⟩ := initialSamplerAttempt_run_sourceOutcome J
  have he : σ = τ := by
    obtain ⟨_,_,hj⟩ := hj
    obtain ⟨_,_,hr⟩ := hrun
    exact (BigStep.unique hj.bigStep hr.bigStep).1
  obtain ⟨ω,hω⟩ := ho (by simpa [he] using hb) (by simpa [he] using hp)
  obtain ⟨w⟩ := (Finset.mem_filter.mp hω).2
  have hbits : flatBits ((flatBitsEquiv J.bits.length).symm ⟨J.bits,rfl⟩) =
      flatBits ρ := congrArg Subtype.val
        ((flatBitsEquiv J.bits.length).apply_symm_apply ⟨J.bits,rfl⟩)
  rw [hbits] at w
  let w₀ : SourceInitialOutcomeWitness I (flatBits ρ) ω := { w with }
  have hw : w₀.σfinal = τ := by
    obtain ⟨_,_,hh⟩ := w₀.attemptRun
    obtain ⟨_,_,hr⟩ := hrun
    exact (BigStep.unique hh.bigStep hr.bigStep).1
  refine ⟨ω,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨w₀⟩⟩,?_⟩
  intro b hb
  rw [w₀.representative b hb, ← hw, w₀.resultArray]
  have hbn := (mem_activeVertices.mp hb).1
  simp [arrOf,hbn]

/-- Any subset of successful selections has at most the one-pass expected
representative charge. The subset can be the actual acceptance event. -/
lemma selection_reward_le
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (final : FlatTape I.bits.length → Env) (cost : FlatTape I.bits.length → ℕ)
    (hrun : ∀ ρ, Run B initialSamplerAttempt
      {I.σ with inp := (flatBits ρ).map Bool.toNat ++ I.rest} (final ρ) (cost ρ))
    (keep : FlatTape I.bits.length → Prop) [DecidablePred keep]
    (hkeep : ∀ ρ, keep ρ →
      (final ρ).vars "batchFailed" = 0 ∧ (final ρ).vars "repFailed" = 0)
    (weight : ℕ → ℚ) (hweight : ∀ b, 0 ≤ weight b) :
    (∑ ρ, if keep ρ then
      (∑ b ∈ activeVertices n I.activeB, weight (((final ρ).arrs "repB").getD b 0))
      else 0) ≤ (∑ b ∈ activeVertices n I.activeB, weight b) * 2^I.bits.length := by
  classical
  have ho (ρ) (h : keep ρ) := successful_selection_outcome I ρ (hrun ρ)
    (hkeep ρ h).1 (hkeep ρ h).2
  let decoded ρ := if h : keep ρ then some (Classical.choose (ho ρ h)) else none
  have hd (ρ) (ω) (h : decoded ρ = some ω) : ρ ∈ sourceInitialOutcomeFiber I ω := by
    dsimp [decoded] at h
    split_ifs at h with hk
    · cases h
      exact (Classical.choose_spec (ho ρ hk)).1
  have hm := InitialOutcomeCharge.actual_representative_charge_le I decoded hd weight hweight
  have he (ρ) : (decoded ρ).elim 0 (fun ω =>
      ∑ b ∈ activeVertices n I.activeB,
        weight ((outcomeChoice A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r ω).representative b)) =
      if keep ρ then ∑ b ∈ activeVertices n I.activeB,
        weight (((final ρ).arrs "repB").getD b 0) else 0 := by
    by_cases hk : keep ρ
    · simp only [decoded,dif_pos hk,Option.elim_some,if_pos hk]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Classical.choose_spec (ho ρ hk)).2 b hb]
    · simp [decoded,hk]
  simp_rw [he] at hm
  exact (div_le_iff₀ (by positivity : (0:ℚ) < 2^I.bits.length)).mp hm

/-- The exception acceptance scan preserves both selected representatives
and selector flags, so the same reward bound applies to a full attempt. -/
lemma full_attempt_reward_le {k cap : ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (final : FlatTape R.I.bits.length → Env) (cost : FlatTape R.I.bits.length → ℕ)
    (hrun : ∀ ρ, Run B fullInitialAttempt
      {R.I.σ with inp := (flatBits ρ).map Bool.toNat ++ R.I.rest} (final ρ) (cost ρ))
    (keep : FlatTape R.I.bits.length → Prop) [DecidablePred keep]
    (hkeep : ∀ ρ, keep ρ →
      (final ρ).vars "batchFailed" = 0 ∧ (final ρ).vars "repFailed" = 0)
    (weight : ℕ → ℚ) (hweight : ∀ b, 0 ≤ weight b) :
    (∑ ρ, if keep ρ then
      (∑ b ∈ activeVertices n R.I.activeB,
        weight (((final ρ).arrs "repB").getD b 0)) else 0) ≤
      (∑ b ∈ activeVertices n R.I.activeB, weight b) * 2^R.I.bits.length := by
  have hd (ρ) : ∃ σ j, Run B initialSamplerAttempt
      {R.I.σ with inp := (flatBits ρ).map Bool.toNat ++ R.I.rest} σ j ∧
      (final ρ).arrs "repB" = σ.arrs "repB" ∧
      (final ρ).vars "batchFailed" = σ.vars "batchFailed" ∧
      (final ρ).vars "repFailed" = σ.vars "repFailed" := by
    obtain ⟨j,hj,h⟩ := hrun ρ
    change BigStepB B (initialSamplerAttempt.seq _) _ _ _ at h
    cases h with
    | seq hs ht =>
      have rt := Run.of_bigStepB ht
      exact ⟨_,_,Run.of_bigStepB hs,rt.frame_arr "repB" (by decide),
        rt.frame_var "batchFailed" (by decide), rt.frame_var "repFailed" (by decide)⟩
  choose σ j hj harr hbatch hrep using hd
  have hm := selection_reward_le R.I σ j hj keep
    (fun ρ hk => ⟨(hbatch ρ).symm.trans (hkeep ρ hk).1,
      (hrep ρ).symm.trans (hkeep ρ hk).2⟩) weight hweight
  simpa only [harr] using hm

private def tapeCongr {a b : ℕ} (h : a = b) : FlatTape a ≃ FlatTape b := by
  subst b
  exact Equiv.refl _

private lemma flatBits_tapeCongr {a b : ℕ} (h : a = b) (ρ : FlatTape a) :
    flatBits (tapeCongr h ρ) = flatBits ρ := by
  subst b
  rfl

/-- Length-independent form for the actual full-attempt family used by the
retry induction. -/
lemma actual_full_reward_le {k cap N : ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hb : attemptBitBudget n m r t ≤ N)
    (final : FlatTape N → Env) (cost : FlatTape N → ℕ)
    (hrun : ∀ ρ, Run B fullInitialAttempt
      {R.I.σ with inp := (flatBits ρ).map Bool.toNat ++ R.I.rest} (final ρ) (cost ρ))
    (keep : FlatTape N → Prop) [DecidablePred keep]
    (hkeep : ∀ ρ, keep ρ →
      (final ρ).vars "batchFailed" = 0 ∧ (final ρ).vars "repFailed" = 0)
    (weight : ℕ → ℚ) (hweight : ∀ b, 0 ≤ weight b) :
    (∑ ρ, if keep ρ then
      (∑ b ∈ activeVertices n R.I.activeB,
        weight (((final ρ).arrs "repB").getD b 0)) else 0) ≤
      (∑ b ∈ activeVertices n R.I.activeB, weight b) * 2^N := by
  let J := R.reinput (List.replicate N false) (by simpa [attemptBitBudget] using hb)
  have hlen : J.I.bits.length = N := by simp [J,ReadyInput.reinput_bits]
  let e := tapeCongr hlen
  have he (ρ) : flatBits (e ρ) = flatBits ρ := flatBits_tapeCongr hlen ρ
  have hm := full_attempt_reward_le J (final ∘ e) (cost ∘ e)
    (fun ρ => by
      have hr := hrun (e ρ)
      rw [he ρ] at hr
      exact hr)
    (keep ∘ e) (fun ρ h => hkeep (e ρ) h) weight hweight
  change (∑ ρ, (fun η : FlatTape N => if keep η then
      (∑ b ∈ activeVertices n R.I.activeB,
        weight (((final η).arrs "repB").getD b 0)) else 0) (e ρ)) ≤ _ at hm
  have hsum := e.sum_comp (fun η : FlatTape N => if keep η then
      (∑ b ∈ activeVertices n R.I.activeB,
        weight (((final η).arrs "repB").getD b 0)) else 0)
  rw [hsum] at hm
  have hac : J.I.activeB = R.I.activeB := rfl
  simpa only [hlen,hac] using hm

end Lax457868Proofs.InitialPhysicalReward
