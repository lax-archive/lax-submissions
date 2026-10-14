import Lax457868Proofs.SamplerInitialProbability
import Lax457868Proofs.SamplerWeightedRetries
import Mathlib.Tactic

/-!
The actual hierarchical initial-attempt law as normalized rational weights on
one finite outcome type.  This lets the weighted retry lemmas apply to the
same decoded choices and selector predicate used by the finite sampler.
-/

namespace Lax457868Proofs.SamplerInitialRetries

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerFiniteMean
open Lax457868Proofs.SamplerRetries
open Lax457868Proofs.SamplerWeightedRetries
open Lax457868Proofs.SamplerTwinSuppression

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- One full initial attempt: ordered draws, then independent choices of one
representative inside each resulting trace class. -/
abbrev InitialOutcome (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) :=
  Σ draw : Fin r → A, RepChoices A B N draw

/-- Its decoded legal attempt. -/
noncomputable def outcomeChoice (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ)
    (ω : InitialOutcome A B N r) : InitialChoice A B N r :=
  decodeChoice A B N ω.1 ω.2

/-- Hierarchical probability weight of one outcome. -/
noncomputable def outcomeWeight (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ)
    (ω : InitialOutcome A B N r) : ℚ :=
  1 / ((A.card ^ r : ℚ) *
    (Fintype.card (RepChoices A B N ω.1) : ℚ))

/-- The actual exception-cap predicate on a decoded attempt. -/
noncomputable def outcomeBad (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r threshold cap : ℕ)
    (ω : InitialOutcome A B N r) : Bool :=
  decide (cap < ((outcomeChoice A B N r ω).exceptions threshold).card)

omit [DecidableEq β] in
lemma outcomeWeight_nonneg (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ)
    (ω : InitialOutcome A B N r) :
    0 ≤ outcomeWeight A B N r ω := by
  unfold outcomeWeight
  positivity

omit [DecidableEq β] in
lemma outcomeWeight_sum_eq_hierarchical (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ)
    (f : InitialOutcome A B N r → ℚ) :
    (∑ ω : InitialOutcome A B N r,
      outcomeWeight A B N r ω * f ω) =
    finiteMean (fun draw : Fin r → A =>
      finiteMean (fun reps : RepChoices A B N draw => f ⟨draw, reps⟩)) := by
  classical
  unfold finiteMean
  rw [Fintype.sum_sigma, card_draws]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro draw hdraw
  unfold outcomeWeight
  calc
    (∑ reps : RepChoices A B N draw,
      1 / ((A.card ^ r : ℚ) *
        (Fintype.card (RepChoices A B N draw) : ℚ)) * f ⟨draw, reps⟩) =
        (1 / ((A.card ^ r : ℚ) *
          (Fintype.card (RepChoices A B N draw) : ℚ))) *
          ∑ reps : RepChoices A B N draw, f ⟨draw, reps⟩ := by
            exact (Finset.mul_sum Finset.univ
              (fun reps : RepChoices A B N draw => f ⟨draw, reps⟩)
              (1 / ((A.card ^ r : ℚ) *
                (Fintype.card (RepChoices A B N draw) : ℚ)))).symm
    _ = _ := by
      simp only [Nat.cast_pow]
      ring

private lemma finiteMean_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    finiteMean (fun _ : Ω => (1 : ℚ)) = 1 := by
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  simp [finiteMean, hcard]

omit [DecidableEq β] in
lemma outcomeWeight_normalized (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) (hA : A.Nonempty) :
    (∑ ω : InitialOutcome A B N r, outcomeWeight A B N r ω) = 1 := by
  classical
  have hRep (draw : Fin r → A) : Nonempty (RepChoices A B N draw) :=
    ⟨fun T => Classical.choice (repFiberNonempty A B N draw T)⟩
  have hdraw : Nonempty (Fin r → A) :=
    ⟨fun _ => ⟨Classical.choose hA, Classical.choose_spec hA⟩⟩
  have h := outcomeWeight_sum_eq_hierarchical A B N r
    (fun _ => (1 : ℚ))
  simp only [mul_one] at h
  rw [h]
  have hinner (draw : Fin r → A) :
      finiteMean (fun _ : RepChoices A B N draw => (1 : ℚ)) = 1 := by
    exact @finiteMean_one (RepChoices A B N draw) _ (hRep draw)
  simp only [hinner]
  exact @finiteMean_one (Fin r → A) _ hdraw

lemma outcomeBad_mass_eq_initialRejectProbability
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r threshold cap : ℕ) :
    badMass (outcomeWeight A B N r)
        (outcomeBad A B N r threshold cap) =
      initialRejectProbability A B N r threshold cap := by
  classical
  unfold badMass
  have h := outcomeWeight_sum_eq_hierarchical A B N r
    (fun ω => if outcomeBad A B N r threshold cap ω = true then (1 : ℚ) else 0)
  have hleft :
      (∑ ω : InitialOutcome A B N r,
        if outcomeBad A B N r threshold cap ω = true then
          outcomeWeight A B N r ω else 0) =
      (∑ ω : InitialOutcome A B N r,
        outcomeWeight A B N r ω *
          (if outcomeBad A B N r threshold cap ω = true then (1 : ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs <;> ring
  rw [hleft, h]
  unfold initialRejectProbability conditionalRejectProbability outcomeBad outcomeChoice
  simp

lemma outcomeBad_mass_le_half (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (B.image N) S).card ≤ c * S.card) :
    badMass
      (outcomeWeight A B N (A.card / (4 * c ^ 2)))
      (outcomeBad A B N (A.card / (4 * c ^ 2))
        (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))) ≤
      (1 / 2 : ℚ) := by
  rw [outcomeBad_mass_eq_initialRejectProbability]
  exact initialRejectProbability_le_half A B N c hA hN hc hB hlinear

lemma initialWeightedMeanAttempts_le_two (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c t : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (B.image N) S).card ≤ c * S.card) :
    weightedMeanAttempts
      (outcomeWeight A B N (A.card / (4 * c ^ 2)))
      (outcomeBad A B N (A.card / (4 * c ^ 2))
        (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))) t ≤ 2 := by
  apply weightedMeanAttempts_le_two
  · exact outcomeWeight_nonneg A B N _
  · exact outcomeWeight_normalized A B N _ hA
  · exact outcomeBad_mass_le_half A B N c hA hN hc hB hlinear

lemma initialWeightedAllBad_mass_le (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c t : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (B.image N) S).card ≤ c * S.card) :
    (∑ tape : Tape (InitialOutcome A B N (A.card / (4 * c ^ 2))) t,
      if ∀ i, outcomeBad A B N (A.card / (4 * c ^ 2))
          (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
          (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))
          (tape i) = true
      then tapeWeight (outcomeWeight A B N (A.card / (4 * c ^ 2))) tape
      else 0) ≤ (1 / 2 : ℚ) ^ t := by
  apply weighted_allBad_mass_le
  · exact outcomeWeight_nonneg A B N _
  · exact outcomeBad_mass_le_half A B N c hA hN hc hB hlinear

/-- The all-bad tape event is exactly failure of the concrete initial
selector on the decoded list of attempts. -/
lemma outcomeTape_selector_failure_iff (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r t threshold cap : ℕ)
    (tape : Tape (InitialOutcome A B N r) t) :
    chooseInitialAttempt
        (List.ofFn fun i : Fin t => outcomeChoice A B N r (tape i))
        threshold cap = none ↔
      ∀ i, outcomeBad A B N r threshold cap (tape i) = true := by
  classical
  rw [SamplerRetries.initialTape_selector_failure_iff
    (decode := outcomeChoice A B N r) tape threshold cap]
  simp [outcomeBad]

/-- The actual selector's exhaustion probability is bounded by `2^{-t}`. -/
lemma initialSelectorFailure_mass_le (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c t : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (B.image N) S).card ≤ c * S.card) :
    (∑ tape : Tape (InitialOutcome A B N (A.card / (4 * c ^ 2))) t,
      if chooseInitialAttempt
          (List.ofFn fun i : Fin t =>
            outcomeChoice A B N (A.card / (4 * c ^ 2)) (tape i))
          (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
          (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) = none
      then tapeWeight (outcomeWeight A B N (A.card / (4 * c ^ 2))) tape
      else 0) ≤ (1 / 2 : ℚ) ^ t := by
  have h := initialWeightedAllBad_mass_le A B N c t hA hN hc hB hlinear
  convert h using 1
  apply Finset.sum_congr rfl
  intro tape htape
  have heq := outcomeTape_selector_failure_iff A B N
    (A.card / (4 * c ^ 2)) t
    (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
    (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) tape
  by_cases hf : chooseInitialAttempt
      (List.ofFn fun i : Fin t =>
        outcomeChoice A B N (A.card / (4 * c ^ 2)) (tape i))
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) = none
  · simp [hf, heq.mp hf]
  · have hnot : ¬ ∀ i, outcomeBad A B N (A.card / (4 * c ^ 2))
        (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) (tape i) = true :=
      fun hall => hf (heq.mpr hall)
    simp [hf, hnot]

omit [DecidableEq β] in
/-- The decoded initial selector needs at most two attempts on average after
removing neighborhood twins, under only the original subset trace bound. -/
lemma deduplicated_initialWeightedMeanAttempts_le_two
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (c t : ℕ) (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c)
    (htrace : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    weightedMeanAttempts
      (outcomeWeight A (B.image N) id (A.card / (4 * c ^ 2)))
      (outcomeBad A (B.image N) id (A.card / (4 * c ^ 2))
        (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))) t ≤ 2 := by
  have hN' := image_neighborhoods_subset_of A B N hN
  have hB' : (B.image N).card ≤ c * A.card :=
    deduplicated_neighborhoods_card_le A B N c hN
      (htrace A Finset.Subset.rfl hA)
  have hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (((B.image N).image id)) S).card ≤
        c * S.card := by
    simpa using deduplicated_linear_trace_bound A B N c hN hc htrace
  exact initialWeightedMeanAttempts_le_two A (B.image N) id c t
    hA hN' hc hB' hlinear

omit [DecidableEq β] in
/-- The same decoded selector exhausts all `t` attempts with probability at
most `2^{-t}`, expressed as its exact weighted tape failure event. -/
lemma deduplicated_initialSelectorFailure_mass_le
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (c t : ℕ) (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c)
    (htrace : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    (∑ tape : Tape (InitialOutcome A (B.image N) id
        (A.card / (4 * c ^ 2))) t,
      if chooseInitialAttempt
          (List.ofFn fun i : Fin t =>
            outcomeChoice A (B.image N) id (A.card / (4 * c ^ 2)) (tape i))
          (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
          (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) = none
      then tapeWeight
        (outcomeWeight A (B.image N) id (A.card / (4 * c ^ 2))) tape
      else 0) ≤ (1 / 2 : ℚ) ^ t := by
  have hN' := image_neighborhoods_subset_of A B N hN
  have hB' : (B.image N).card ≤ c * A.card :=
    deduplicated_neighborhoods_card_le A B N c hN
      (htrace A Finset.Subset.rfl hA)
  have hlinear : ∀ S : Finset α, S.Nonempty →
      (SamplerVCDimension.traceFamily (((B.image N).image id)) S).card ≤
        c * S.card := by
    simpa using deduplicated_linear_trace_bound A B N c hN hc htrace
  exact initialSelectorFailure_mass_le A (B.image N) id c t
    hA hN' hc hB' hlinear

end Lax457868Proofs.SamplerInitialRetries
