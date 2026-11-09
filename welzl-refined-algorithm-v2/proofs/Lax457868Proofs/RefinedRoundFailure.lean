import Lax457868Proofs.RefinedPrefixFailure
import Lax457868Proofs.RefinedRoundMean
import Lax457868Proofs.InitialAbortProbability
import Lax457868Proofs.NumericGraphProbability

/-! Failure counting for the actual fixed-start prepared round. -/
namespace Lax457868Proofs.RefinedRoundFailure

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.InitialAbortProbability
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.CompleteSamplerMean
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedPrefixFailure
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.NumericGraphProbability
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.StoppedPrefixAveraging
open scoped BigOperators

set_option maxHeartbeats 2000000

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Both terminal statuses of the actual initial retry source, counted on
the full fair tape including the unused suffix. -/
lemma initial_failure_count
    {B n m domainCap r bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r n bufferCap targetCap Q k cap G x A)
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hcapB : n < B) (hn : 0 < n)
    (hbudget : n * attemptBitBudget n m r n ≤ N)
    (hper : attemptBitBudget n m r n ≤ N)
    (hmass : SamplerWeightedRetries.badMass
      (SamplerInitialRetries.outcomeWeight A
        (ReusedOriginal.Construction.MarkingMath.activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A) r)
      (SamplerInitialRetries.outcomeBad A
        (ReusedOriginal.Construction.MarkingMath.activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A) r k cap) ≤ (1 / 2 : ℚ))
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B initialSamplerRetriesSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ)) :
    2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
      (final ρ).vars "initialRetryStatus" = 2 ∨
        (final ρ).vars "initialRetryStatus" = 3)).card ≤
      (n * (r + n) + 1) * 2 ^ N := by
  classical
  let bad₂ := Finset.univ.filter (fun ρ : Tape N =>
    (final ρ).vars "initialRetryStatus" = 2)
  let bad₃ := Finset.univ.filter (fun ρ : Tape N =>
    (final ρ).vars "initialRetryStatus" = 3)
  have htwo : 2 ^ n * bad₂.card ≤ n * (r + n) * 2 ^ N := by
    have hs : bad₂ ⊆ sourceSelectorAbortFiber R hper := by
      intro ρ hρ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (final ρ), (cost ρ), Run.of_bigStepB (hrun ρ), ?_⟩
      exact (Finset.mem_filter.mp hρ).2
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hs)).trans
      (sourceSelectorAbort_count R hcap hcapB hbudget hper)
  have hthree : 2 ^ n * bad₃.card ≤ 2 ^ N := by
    have hs : bad₃ ⊆ sourceExhaustedFiber R hper := by
      intro ρ hρ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (final ρ), (cost ρ), Run.of_bigStepB (hrun ρ), ?_⟩
      exact (Finset.mem_filter.mp hρ).2
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hs)).trans
      (sourceExhaustedFiber_geometric R n hcap hcapB hn hbudget hper hmass)
  have hsubset : (Finset.univ.filter (fun ρ : Tape N =>
      (final ρ).vars "initialRetryStatus" = 2 ∨
        (final ρ).vars "initialRetryStatus" = 3)) ⊆ bad₂ ∪ bad₃ := by
    intro ρ hρ
    rcases (Finset.mem_filter.mp hρ).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hcard := (Finset.card_le_card hsubset).trans (Finset.card_union_le bad₂ bad₃)
  calc
    _ ≤ 2 ^ n * (bad₂.card + bad₃.card) := Nat.mul_le_mul_left _ hcard
    _ = 2 ^ n * bad₂.card + 2 ^ n * bad₃.card := by ring
    _ ≤ n * (r + n) * 2 ^ N + 2 ^ N := Nat.add_le_add htwo hthree
    _ = (n * (r + n) + 1) * 2 ^ N := by ring

/-- A conditional repair failure count at every accepted initial stopping
prefix lifts to the full physical sampler tape. -/
lemma accepted_repair_failure_count_of_conditional
    {B n m domainCap r t bufferCap targetCap Q k cap N Fcoef : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap : ℕ)
    (hper : attemptBitBudget n m r t ≤ N)
    (hbudget : attemptCap * attemptBitBudget n m r t ≤ N)
    (C : ∀ ρ : Tape N, Cut
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) attemptCap)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B completeSamplerSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ))
    (hafter : ∀ ρ : Tape N,
      (C ρ).final.vars "initialRetryStatus" = 1 →
      ∀ f : Tape (N - (C ρ).used) → Env,
      ∀ d : Tape (N - (C ρ).used) → ℕ,
      (∀ η, BigStepB B afterInitial
        {(C ρ).final with inp := (List.ofFn η).map Bool.toNat ++ R.I.rest}
        (f η) (d η)) →
      2 ^ n * (Finset.univ.filter (fun η : Tape (N - (C ρ).used) =>
        (f η).vars "repairRetryStatus" = 2 ∨
          (f η).vars "repairRetryStatus" = 3)).card ≤
        Fcoef * 2 ^ (N - (C ρ).used)) :
    2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
      (C ρ).final.vars "initialRetryStatus" = 1 ∧
        ((final ρ).vars "repairRetryStatus" = 2 ∨
          (final ρ).vars "repairRetryStatus" = 3))).card ≤
      Fcoef * 2 ^ N := by
  classical
  let used : Tape N → ℕ := fun ρ => (C ρ).used
  have hu : ∀ ρ, used ρ ≤ N := fun ρ => (C ρ).used_le.trans hbudget
  have hcausal := cut_causal R attemptCap N hper hbudget C
  let X : Tape N → ℚ := fun ρ =>
    if (C ρ).final.vars "initialRetryStatus" = 1 ∧
      ((final ρ).vars "repairRetryStatus" = 2 ∨
        (final ρ).vars "repairRetryStatus" = 3) then 1 else 0
  let Y : Tape N → ℚ := fun _ => (Fcoef : ℚ) / 2 ^ n
  have hcond (ρ : Tape N) :
      (∑ η : Tape (N - used ρ),
        X ((splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1, η))) ≤
      Y ρ * 2 ^ (N - used ρ) := by
    let extend : Tape (N - used ρ) → Tape N := fun η =>
      (splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1, η)
    have hp (η : Tape (N - used ρ)) :
        (List.ofFn ρ).take (used ρ) = (List.ofFn (extend η)).take (used ρ) := by
      rw [prefix_of_split (hu ρ),prefix_of_split (hu ρ)]
      simp [extend]
    have hstate (η : Tape (N - used ρ)) := (hcausal ρ (extend η) (hp η)).2
    by_cases hs : (C ρ).final.vars "initialRetryStatus" = 1
    · have hd (η : Tape (N - used ρ)) :
          ∃ d, BigStepB B afterInitial
            {(C ρ).final with inp := (List.ofFn η).map Bool.toNat ++ R.I.rest}
            (final (extend η)) d := by
        obtain ⟨ki,kt,hi,ht,hcost⟩ := actual_decompose
          (R.reinput (List.ofFn (extend η))
            (by simpa [attemptBitBudget] using hper)) (C (extend η)) (hrun (extend η))
        have hdrop : (List.ofFn (extend η)).drop (used ρ) = List.ofFn η := by
          rw [boolTape_split (hu ρ) (extend η)]
          simp [extend]
        refine ⟨kt,?_⟩
        rw [hstate η] at ht
        rw [hdrop] at ht
        exact ht
      choose d hd' using hd
      have hc := hafter ρ hs (fun η => final (extend η)) d hd'
      have hpoint (η : Tape (N - used ρ)) : X (extend η) ≤
          (if (final (extend η)).vars "repairRetryStatus" = 2 ∨
            (final (extend η)).vars "repairRetryStatus" = 3 then (1 : ℚ) else 0) := by
        have hstatus : (C (extend η)).final.vars "initialRetryStatus" = 1 := by
          simpa only [hstate η] using hs
        simp [X,hstatus]
      have hsum : (∑ η : Tape (N - used ρ), X (extend η)) ≤
          ((Finset.univ.filter (fun η : Tape (N - used ρ) =>
            (final (extend η)).vars "repairRetryStatus" = 2 ∨
              (final (extend η)).vars "repairRetryStatus" = 3)).card : ℚ) := by
        calc
          _ ≤ ∑ η : Tape (N - used ρ),
              (if (final (extend η)).vars "repairRetryStatus" = 2 ∨
                (final (extend η)).vars "repairRetryStatus" = 3 then (1 : ℚ) else 0) := by
                  apply Finset.sum_le_sum
                  intro η _
                  exact hpoint η
          _ = _ := by simp
      have hcQ : (2 ^ n : ℚ) *
          ((Finset.univ.filter (fun η : Tape (N - used ρ) =>
            (final (extend η)).vars "repairRetryStatus" = 2 ∨
              (final (extend η)).vars "repairRetryStatus" = 3)).card : ℚ) ≤
          (Fcoef : ℚ) * 2 ^ (N - used ρ) := by exact_mod_cast hc
      have hdiv : ((Finset.univ.filter (fun η : Tape (N - used ρ) =>
            (final (extend η)).vars "repairRetryStatus" = 2 ∨
              (final (extend η)).vars "repairRetryStatus" = 3)).card : ℚ) ≤
          ((Fcoef : ℚ) / 2 ^ n) * 2 ^ (N - used ρ) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ n)).2
        simpa [mul_comm,mul_left_comm,mul_assoc] using hcQ
      change (∑ η : Tape (N - used ρ), X (extend η)) ≤ Y ρ * 2 ^ (N - used ρ)
      exact hsum.trans hdiv
    · have hz (η : Tape (N - used ρ)) : X (extend η) = 0 := by
        have hnot : (C (extend η)).final.vars "initialRetryStatus" ≠ 1 := by
          simpa only [hstate η] using hs
        simp [X,hnot]
      change (∑ η : Tape (N - used ρ), X (extend η)) ≤ Y ρ * 2 ^ (N - used ρ)
      simp [hz,Y]
      positivity
  have htotal := sum_le_of_stopped_prefix used hu
    (fun ρ η hp => (hcausal ρ η hp).1) X Y (by intros; rfl) hcond
  have hX : (∑ ρ : Tape N, X ρ) =
      ((Finset.univ.filter (fun ρ : Tape N =>
        (C ρ).final.vars "initialRetryStatus" = 1 ∧
          ((final ρ).vars "repairRetryStatus" = 2 ∨
            (final ρ).vars "repairRetryStatus" = 3))).card : ℚ) := by simp [X]
  have hY : (∑ ρ : Tape N, Y ρ) = ((Fcoef : ℚ) / 2 ^ n) * 2 ^ N := by
    simp [Y,Nat.cast_pow,mul_comm]
  rw [hX,hY] at htotal
  -- The stopped-prefix inequality is scaled back to natural cardinality.
  have hp : (2 ^ n : ℚ) *
      ((Finset.univ.filter (fun ρ : Tape N =>
        (C ρ).final.vars "initialRetryStatus" = 1 ∧
          ((final ρ).vars "repairRetryStatus" = 2 ∨
            (final ρ).vars "repairRetryStatus" = 3))).card : ℚ) ≤
      (Fcoef : ℚ) * 2 ^ N := by
    calc
      _ ≤ (2 ^ n : ℚ) * (((Fcoef : ℚ) / 2 ^ n) * 2 ^ N) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by field_simp
  exact_mod_cast hp

/-- The deterministic outer-round suffix never writes either retry status. -/
private lemma round_tail_status {B cost : ℕ} {σ τ : Env}
    (h : BigStepB B
      (.ite (.eq (.var "initialRetryStatus") (.lit 1))
        (.ite (.eq (.var "repairRetryStatus") (.lit 1))
          ((partition "activeB" "ord" "sampleCount" "classB"
            "repsB" "nextB" "repB" "nextBCount").seq
            ((partition "activeA" "repsB" "nextBCount" "classA"
              "repsA" "nextA" "repA" "nextACount").seq commitReduction))
          (.assign "acount" (.lit 0)))
        (.assign "acount" (.lit 0))) σ τ cost) :
    τ.vars "initialRetryStatus" = σ.vars "initialRetryStatus" ∧
    τ.vars "repairRetryStatus" = σ.vars "repairRetryStatus" := by
  have hr := Run.of_bigStepB h
  exact ⟨hr.frame_var _ (by decide), hr.frame_var _ (by decide)⟩

/-- Any final retry failure flag on the prepared round is the same flag on
the actual sampler subrun; partition and commit leave the flags alone. -/
lemma prepared_failure_to_sampler_failure {B K cost samplerCost : ℕ}
    {σ σp τ samplerFinal : Env}
    (hprep : Run B PrepareRefinedRound.prepareRefinedRound σ σp K)
    (ha : BigStepB B preparedRefinedRoundSource σ τ cost)
    (hsam : BigStepB B completeSamplerSource σp samplerFinal samplerCost)
    (hfail : failureStatus τ) : failureStatus samplerFinal := by
  change BigStepB B (PrepareRefinedRound.prepareRefinedRound.seq refinedRoundSource)
    σ τ cost at ha
  cases ha with
  | seq hp hr =>
    obtain ⟨_,_,hp'⟩ := hprep
    have he := (BigStep.unique hp.bigStep hp'.bigStep).1
    subst σp
    change BigStepB B (completeSamplerSource.seq _) _ _ _ at hr
    cases hr with
    | seq hs ht =>
      have he' := (BigStep.unique hs.bigStep hsam.bigStep).1
      subst samplerFinal
      obtain ⟨hinit,hrepair⟩ := round_tail_status ht
      simpa only [failureStatus,hinit,hrepair] using hfail

private lemma after_initial_status {B cost : ℕ} {σ τ : Env}
    (h : BigStepB B afterInitial σ τ cost) :
    τ.vars "initialRetryStatus" = σ.vars "initialRetryStatus" := by
  exact (Run.of_bigStepB h).frame_var _ (by decide)

/-- Initial abort and accepted-prefix repair abort cover every actual sampler
failure status, with coefficients added only after the disjoint chronology. -/
lemma sampler_failure_count_of_conditional
    {B n m domainCap r bufferCap targetCap Q k cap N Frepair : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r n bufferCap targetCap Q k cap G x A)
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hcapB : n < B) (hn : 0 < n)
    (hbudget : n * attemptBitBudget n m r n ≤ N)
    (hper : attemptBitBudget n m r n ≤ N)
    (hmass : SamplerWeightedRetries.badMass
      (SamplerInitialRetries.outcomeWeight A
        (ReusedOriginal.Construction.MarkingMath.activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A) r)
      (SamplerInitialRetries.outcomeBad A
        (ReusedOriginal.Construction.MarkingMath.activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A) r k cap) ≤ (1 / 2 : ℚ))
    (C : ∀ ρ : Tape N, Cut
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) n)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B completeSamplerSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ))
    (hafter : ∀ ρ : Tape N,
      (C ρ).final.vars "initialRetryStatus" = 1 →
      ∀ f : Tape (N - (C ρ).used) → Env,
      ∀ d : Tape (N - (C ρ).used) → ℕ,
      (∀ η, BigStepB B afterInitial
        {(C ρ).final with inp := (List.ofFn η).map Bool.toNat ++ R.I.rest}
        (f η) (d η)) →
      2 ^ n * (Finset.univ.filter (fun η : Tape (N - (C ρ).used) =>
        (f η).vars "repairRetryStatus" = 2 ∨
          (f η).vars "repairRetryStatus" = 3)).card ≤
        Frepair * 2 ^ (N - (C ρ).used)) :
    2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
      failureStatus (final ρ))).card ≤
      (n * (r+n) + 1 + Frepair) * 2 ^ N := by
  classical
  have hd (ρ : Tape N) := actual_decompose
    (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) (C ρ) (hrun ρ)
  choose initialCost tailCost hi ht hcost using hd
  have hinit := initial_failure_count R hcap hcapB hn hbudget hper hmass
    (fun ρ => (C ρ).final) initialCost hi
  have hrepair := accepted_repair_failure_count_of_conditional R n hper hbudget
    C final cost hrun hafter
  let badInitial := Finset.univ.filter (fun ρ : Tape N =>
    (C ρ).final.vars "initialRetryStatus" = 2 ∨
      (C ρ).final.vars "initialRetryStatus" = 3)
  let badRepair := Finset.univ.filter (fun ρ : Tape N =>
    (C ρ).final.vars "initialRetryStatus" = 1 ∧
      ((final ρ).vars "repairRetryStatus" = 2 ∨
        (final ρ).vars "repairRetryStatus" = 3))
  have hsub : (Finset.univ.filter (fun ρ : Tape N =>
      failureStatus (final ρ))) ⊆ badInitial ∪ badRepair := by
    intro ρ hρ
    have hf : failureStatus (final ρ) := (Finset.mem_filter.mp hρ).2
    rcases (C ρ).status with hs | hs | hs
    · have he := after_initial_status (ht ρ)
      have hf' : (final ρ).vars "repairRetryStatus" = 2 ∨
          (final ρ).vars "repairRetryStatus" = 3 := by
        rcases hf with hfirst | hlast
        · rw [he,hs] at hfirst
          omega
        · exact hlast
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hs,hf'⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,Or.inl hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,Or.inr hs⟩)
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le badInitial badRepair)
  calc
    _ ≤ 2 ^ n * (badInitial.card + badRepair.card) :=
      Nat.mul_le_mul_left _ hcard
    _ = 2 ^ n * badInitial.card + 2 ^ n * badRepair.card := by ring
    _ ≤ (n * (r+n)+1) * 2 ^ N + Frepair * 2 ^ N :=
      Nat.add_le_add hinit hrepair
    _ = (n * (r+n)+1+Frepair) * 2 ^ N := by ring

/-- Failure statuses of a prepared-round family inject into the corresponding
actual complete-sampler statuses on the same tape. -/
lemma prepared_failure_count_le_sampler
    {B N K : ℕ}
    (start : Tape N → Env) (samplerStart : Tape N → Env)
    (hprep : ∀ ρ, Run B PrepareRefinedRound.prepareRefinedRound
      (start ρ) (samplerStart ρ) K)
    (final samplerFinal : Tape N → Env) (cost samplerCost : Tape N → ℕ)
    (hround : ∀ ρ, BigStepB B preparedRefinedRoundSource
      (start ρ) (final ρ) (cost ρ))
    (hsampler : ∀ ρ, BigStepB B completeSamplerSource
      (samplerStart ρ) (samplerFinal ρ) (samplerCost ρ)) :
    (Finset.univ.filter (fun ρ : Tape N => failureStatus (final ρ))).card ≤
      (Finset.univ.filter (fun ρ : Tape N => failureStatus (samplerFinal ρ))).card := by
  classical
  apply Finset.card_le_card
  intro ρ hρ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prepared_failure_to_sampler_failure (hprep ρ) (hround ρ) (hsampler ρ)
      (Finset.mem_filter.mp hρ).2⟩

/-- The two local retry statuses contribute at most the paper's coarse
`n³+n` coefficient when there are at most `n` exceptions and draws. -/
lemma repair_status_union_count {N n e s : ℕ} (he : e ≤ n) (hs : s ≤ n)
    (status2 status3 : Tape N → Prop) [DecidablePred status2]
    [DecidablePred status3]
    (h2 : 2 ^ n * (Finset.univ.filter status2).card ≤
      e * (n * s) * 2 ^ N)
    (h3 : 2 ^ n * (Finset.univ.filter status3).card ≤ e * 2 ^ N) :
    2 ^ n * (Finset.univ.filter (fun ρ => status2 ρ ∨ status3 ρ)).card ≤
      (n * (n * n) + n) * 2 ^ N := by
  classical
  have hsub : (Finset.univ.filter (fun ρ => status2 ρ ∨ status3 ρ)) ⊆
      (Finset.univ.filter status2) ∪ (Finset.univ.filter status3) := by
    intro ρ hρ
    rcases (Finset.mem_filter.mp hρ).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)
  have hcoef : e * (n * s) ≤ n * (n * n) := by
    exact (Nat.mul_le_mul_left e (Nat.mul_le_mul_left n hs)).trans
      (Nat.mul_le_mul_right (n * n) he)
  calc
    _ ≤ 2 ^ n * ((Finset.univ.filter status2).card +
      (Finset.univ.filter status3).card) := Nat.mul_le_mul_left _ hcard
    _ = 2 ^ n * (Finset.univ.filter status2).card +
      2 ^ n * (Finset.univ.filter status3).card := by ring
    _ ≤ e * (n * s) * 2 ^ N + e * 2 ^ N := Nat.add_le_add h2 h3
    _ = (e * (n * s) + e) * 2 ^ N := by ring
    _ ≤ (n * (n * n) + n) * 2 ^ N :=
      Nat.mul_le_mul_right _ (Nat.add_le_add hcoef he)

/-- The ready source round inherits any uniform actual complete-sampler
failure count at its deterministic preparation state. -/
lemma fixed_prepared_failure_of_sampler_count
    {B c n Fcoef : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4 * (x.length + 1) ≤ B)
    (hcount : ∀ {L : ℕ} {A : Finset ℕ},
      (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
        (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n)
        (refinedCutoffK c) (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A) →
      (T : RuntimeInput R (64*Nat.clog 2 c) n) →
      Set.InjOn
        (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
          (ReusedOriginal.Construction.PartitionResult.finSetAsSet A))
        (ReusedOriginal.Construction.PartitionResult.finSetAsSet
          (activeVertices n R.I.activeB)) →
      R.I.rest = [] →
      R.I.σ.vars "initialRetryCap" = n →
      n*attemptBitBudget n A.card (A.card/(4*c^2)) n +
        (A.card/(4*c^2*(64*Nat.clog 2 c+1))) *
          (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ L →
      (samplerFinal : Tape L → Env) → (samplerCost : Tape L → ℕ) →
      (∀ ρ, BigStepB B completeSamplerSource
        {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat}
        (samplerFinal ρ) (samplerCost ρ)) →
      2 ^ n * (Finset.univ.filter (fun ρ : Tape L =>
        failureStatus (samplerFinal ρ))).card ≤ Fcoef * 2 ^ L) :
    FixedPreparedRoundFailure (B := B) (c := c) (n := n)
      (Fcoef := Fcoef) (G := G) (x := x) := by
  classical
  intro S L hready hg hlen hreserve final cost hrun
  obtain ⟨A,C,bits,sizes,D,hA,hCsub,hC,hsep,⟨hstore⟩,hbounded,
    hcapacity,hroundCapacity,hacount,hsizesLen,hsizesSum,hpotential,
    hroundLog,hout,hinput,htape⟩ := hready
  have hlarge : 2 * refinedCutoffK c < A.card := by
    have hh := hg
    simp [roundGuard,evalB_condLt_iff,D.cutoff,hacount] at hh
    exact hh.2.2
  have hAn : A.card ≤ n := by simpa using Finset.card_le_card hA
  have hn : 0 < n := by
    obtain ⟨v,hv⟩ := hC
    have := Finset.mem_range.mp (hCsub hv)
    omega
  have hround : S.vars "round" < n := by omega
  have hbits : bits.length = L := by
    have hh := congrArg List.length hinput
    simp at hh
    omega
  have hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n +
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ L :=
    (round_budget_le (c := c) hAn).trans hreserve
  have hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ L := by
    have hh := Nat.mul_le_mul_right
      (attemptBitBudget n A.card (A.card/(4*c^2)) n)
      (show 1 ≤ n by omega)
    omega
  have hprepBudget : (A.card/(4*c^2))*n*Nat.clog 2 A.card +
      n*n*Nat.clog 2 n ≤ bits.length := by
    simpa only [attemptBitBudget,hbits] using hper
  obtain ⟨R,T,hprep,hRbits,hRrest,hCarray,hretryCap,hframePrep⟩ :=
    prepare_sampler_input D hx hc hA hCsub hlarge hB hinput hprepBudget
  have hRrest' : R.I.rest = [] := hRrest
  have hsepR : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (ReusedOriginal.Construction.PartitionResult.finSetAsSet A))
      (ReusedOriginal.Construction.PartitionResult.finSetAsSet
        (activeVertices n R.I.activeB)) := by
    have hflag : activeVertices n (ExceptionRefinementStep.setFlag C) = C := by
      simpa only [SamplePacking.flaggedVertices] using
        (flagged_setFlag hCsub)
    simpa only [hCarray,hflag] using hsep
  have hrun' (ρ : Tape L) : BigStepB B preparedRefinedRoundSource
      {S with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
      (final ρ) (cost ρ) := by
    simpa [hRrest'] using hrun ρ
  obtain ⟨samplerFinal,samplerCost,hsampler,_⟩ :=
    RefinedRoundMean.actual_prepared_family D hG hc hCsub hC hlarge
      hbounded hstore hcapacity hround R T hprep hCarray hretryCap
      (by simpa [hRbits,hbits] using hbudget)
      final cost hrun'
  have hsampler' (ρ : Tape L) : BigStepB B completeSamplerSource
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat}
      (samplerFinal ρ) (samplerCost ρ) := by
    simpa [hRrest'] using hsampler ρ
  have hprep' (ρ : Tape L) : Run B PrepareRefinedRound.prepareRefinedRound
      {S with inp := (List.ofFn ρ).map Bool.toNat}
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat} (40*n+58) := by
    have hi : S.inp = R.I.σ.inp := (hprep.frame_inp (by decide)).symm
    simpa only [List.nil_append] using
      run_replace_consumed_suffix hprep [] (by simpa using hi)
        ((List.ofFn ρ).map Bool.toNat)
  have hcard := prepared_failure_count_le_sampler
    (fun ρ : Tape L => {S with inp := (List.ofFn ρ).map Bool.toNat})
    (fun ρ : Tape L => {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat})
    hprep' final samplerFinal cost samplerCost hrun hsampler'
  exact (Nat.mul_le_mul_left _ hcard).trans
    (hcount R T hsepR hRrest' hretryCap hbudget samplerFinal samplerCost hsampler')

/-- Final packing preserves the repair status reported by the physical
exception loop. -/
lemma packed_repair_status {B cost : ℕ} {σ τ : Env}
    (h : BigStepB B ExceptionRepairLoop.exceptionRepairPackedSource σ τ cost) :
    ∃ middle loopCost, BigStepB B ExceptionRepairLoop.exceptionRepairLoopSource
      σ middle loopCost ∧
      τ.vars "repairRetryStatus" = middle.vars "repairRetryStatus" := by
  change BigStepB B (ExceptionRepairLoop.exceptionRepairLoopSource.seq
    (.ite (.eq (.var "repairRetryStatus") (.lit 1))
      SamplePacking.packMarkedSamples .skip)) σ τ cost at h
  cases h with
  | seq hloop hpack =>
    refine ⟨_,_,hloop,?_⟩
    exact (Run.of_bigStepB hpack).frame_var _ (by decide)

/-- A full-tape count for the source loop transfers unchanged through the
deterministic final packing command. -/
lemma packed_failure_count_of_loop
    {B n s t bufferCap targetCap q cap k e N Ccoef : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (L : ExceptionRepairLoop.LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B ExceptionRepairLoop.exceptionRepairPackedSource
      (L.reinput (List.ofFn ρ)).σ (final ρ) (cost ρ))
    (hloop : ∀ (loopFinal : Tape N → Env) (loopCost : Tape N → ℕ),
      (∀ ρ, BigStepB B ExceptionRepairLoop.exceptionRepairLoopSource
        (L.reinput (List.ofFn ρ)).σ (loopFinal ρ) (loopCost ρ)) →
      2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
        (loopFinal ρ).vars "repairRetryStatus" = 2 ∨
          (loopFinal ρ).vars "repairRetryStatus" = 3)).card ≤ Ccoef * 2 ^ N) :
    2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
      (final ρ).vars "repairRetryStatus" = 2 ∨
        (final ρ).vars "repairRetryStatus" = 3)).card ≤ Ccoef * 2 ^ N := by
  classical
  have hd (ρ : Tape N) := packed_repair_status (hrun ρ)
  choose loopFinal loopCost hsource hstatus using hd
  have hh := hloop loopFinal loopCost hsource
  simpa only [hstatus] using hh

/-- A fixed packed-repair source law supplies the conditional accepted-tail
bound required by the complete sampler's stopped initial retry prefix. -/
lemma sampler_failure_count_of_packed
    {B c n N : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A : Finset ℕ}
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n)
      (refinedCutoffK c) (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (T : RuntimeInput R (64*Nat.clog 2 c) n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G
        (ReusedOriginal.Construction.PartitionResult.finSetAsSet A))
      (ReusedOriginal.Construction.PartitionResult.finSetAsSet
        (activeVertices n R.I.activeB)))
    (hrest : R.I.rest = [])
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n +
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N)
    (hpacked : ∀ (choice : SamplerPhases.InitialChoice A
        (activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A)
        (A.card/(4*c^2))) (q M : ℕ),
      (L : ExceptionRepairLoop.LoopInput B n (64*Nat.clog 2 c) n n
        (2*Lax11.GraphEncoding.edgeCount x) q n (refinedCutoffK c)
        (choice.exceptions (refinedCutoffK c)).card G x
        (choice.exceptions (refinedCutoffK c)) (activeVertices n R.I.activeB)
        (ExceptionPhaseSource.phaseTwoSample G
          (choice.exceptions (refinedCutoffK c)) A choice.sample) A
        (ExceptionPhaseSource.phaseTwoSample G
          (choice.exceptions (refinedCutoffK c)) A choice.sample)) →
      (∀ b ∈ activeVertices n R.I.activeB,
        choice.representative b = L.rep b) →
      (choice.exceptions (refinedCutoffK c)).card *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ M →
      (f : Tape M → Env) → (d : Tape M → ℕ) →
      (∀ η, BigStepB B ExceptionRepairLoop.exceptionRepairPackedSource
        (L.reinput (List.ofFn η)).σ (f η) (d η)) →
      2 ^ n * (Finset.univ.filter (fun η : Tape M =>
        (f η).vars "repairRetryStatus" = 2 ∨
          (f η).vars "repairRetryStatus" = 3)).card ≤
        (n*(n*n)+n)*2^M)
    (samplerFinal : Tape N → Env) (samplerCost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B completeSamplerSource
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat}
      (samplerFinal ρ) (samplerCost ρ)) :
    2 ^ n * (Finset.univ.filter (fun ρ : Tape N =>
      failureStatus (samplerFinal ρ))).card ≤
      (n*(2*n)+n*(n*n)+1+n)*2^N := by
  classical
  have hn : 0 < n := by
    obtain ⟨a,ha⟩ := R.I.hAnonempty
    have := Finset.mem_range.mp (R.I.hA ha)
    omega
  have hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N :=
    (Nat.le_mul_of_pos_left _ hn).trans (by omega)
  let Rρ (ρ : Tape N) := R.reinput (List.ofFn ρ)
    (by simpa [attemptBitBudget] using hper)
  have hcapρ (ρ : Tape N) : (Rρ ρ).I.σ.vars "initialRetryCap" = n := by
    simpa [Rρ,ReadyInput.reinput,InitialFlatLaw.reinputInitialAttempt] using hcap
  have hbudgetρ (ρ : Tape N) :
      n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ (Rρ ρ).I.bits.length := by
    simpa [Rρ,ReadyInput.reinput_bits] using (show
      n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N by omega)
  let C (ρ : Tape N) : Cut (Rρ ρ) n :=
    Classical.choice (cut_exists (Rρ ρ) n (hcapρ ρ)
      (by have := R.hnB; omega) (hbudgetρ ρ))
  have hrun' (ρ : Tape N) : BigStepB B completeSamplerSource
      (Rρ ρ).I.σ (samplerFinal ρ) (samplerCost ρ) := by
    simpa [Rρ,hrest,ReadyInput.reinput,InitialFlatLaw.reinputInitialAttempt]
      using hrun ρ
  have hmass := numeric_initial_badMass_half hG hc A
    (activeVertices n R.I.activeB) R.I.hA
    (fun b hb => Finset.mem_range.mpr (mem_activeVertices.mp hb).1)
    R.I.hAnonempty hsep
  have hafter (ρ : Tape N)
      (hs : (C ρ).final.vars "initialRetryStatus" = 1)
      (f : Tape (N-(C ρ).used) → Env) (d : Tape (N-(C ρ).used) → ℕ)
      (ha : ∀ η, BigStepB B afterInitial
        {(C ρ).final with inp := (List.ofFn η).map Bool.toNat ++ R.I.rest}
        (f η) (d η)) :
      2 ^ n * (Finset.univ.filter (fun η : Tape (N-(C ρ).used) =>
        (f η).vars "repairRetryStatus" = 2 ∨
          (f η).vars "repairRetryStatus" = 3)).card ≤
        (n*(n*n)+n)*2^(N-(C ρ).used) := by
    have Tρ := runtime_reinput R T (List.ofFn ρ)
      (by simpa [attemptBitBudget] using hper)
    obtain ⟨choice,q,L,repairCost,hrepair,hcost,hLrest,he,hrep,_⟩ :=
      accepted_tail_family (Rρ ρ) Tρ (C ρ) hs f d
        (by simpa [Rρ,ReadyInput.reinput,InitialFlatLaw.reinputInitialAttempt] using ha)
    have hb : (choice.exceptions (refinedCutoffK c)).card *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N-(C ρ).used := by
      have hused := (C ρ).used_le
      have he' := Nat.mul_le_mul_right
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) he
      omega
    exact hpacked choice q (N-(C ρ).used) L hrep hb f repairCost hrepair
  have hsampler := sampler_failure_count_of_conditional R hcap
    (by have := R.hnB; omega) hn (by omega) hper hmass C
    samplerFinal samplerCost hrun' hafter
  have hr : A.card/(4*c^2) ≤ n :=
    (Nat.div_le_self _ _).trans (by simpa using Finset.card_le_card R.I.hA)
  exact hsampler.trans (Nat.mul_le_mul_right _ (by nlinarith :
    n*(A.card/(4*c^2)+n)+1+(n*(n*n)+n) ≤
      n*(2*n)+n*(n*n)+1+n))

end Lax457868Proofs.RefinedRoundFailure
