import Mathlib.Tactic
import Lax457868Proofs.SamplerRetries

/-!
Finite independent retries under a nonuniform finite outcome law. The law is
given explicitly by nonnegative rational weights summing to one.
-/

namespace Lax457868Proofs.SamplerWeightedRetries

open Lax457868Proofs.SamplerRetries

/-- Product probability of one independent finite tape. -/
def tapeWeight {Ω : Type*} (w : Ω → ℚ) {t : ℕ} (tape : Tape Ω t) : ℚ :=
  ∏ i, w (tape i)

/-- Total product weight of all tapes of a fixed length. -/
def weightedTapeMass {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (t : ℕ) : ℚ :=
  ∑ tape : Tape Ω t, tapeWeight w tape

/-- Weighted mean of the actual number of attempts inspected by the retry
selector on an independent finite tape. -/
def weightedMeanAttempts {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (bad : Ω → Bool) (t : ℕ) : ℚ :=
  ∑ tape : Tape Ω t,
    tapeWeight w tape * (attemptsUsed bad (List.ofFn tape) : ℚ)

/-- Total one-draw weight assigned to rejected outcomes. -/
def badMass {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (bad : Ω → Bool) : ℚ :=
  ∑ a, (if bad a = true then w a else 0)

private lemma tapeWeight_cons {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (a : Ω) {t : ℕ} (tail : Tape Ω t) :
    tapeWeight w (Fin.consEquiv (fun _ : Fin (t + 1) => Ω) (a, tail)) =
      w a * tapeWeight w tail := by
  classical
  simp [tapeWeight, Fin.consEquiv, Fin.prod_univ_succ]

private lemma attemptsUsed_cons {Ω : Type*} (bad : Ω → Bool)
    (a : Ω) {t : ℕ} (tail : Tape Ω t) :
    attemptsUsed bad (List.ofFn (Fin.consEquiv (fun _ : Fin (t + 1) => Ω) (a, tail))) =
      if bad a then attemptsUsed bad (List.ofFn tail) + 1 else 1 := by
  by_cases h : bad a = true <;>
    simp [Fin.consEquiv, attemptsUsed, List.ofFn_succ, h]

/-- The sum of all length-`t` product weights is the `t`th power of the
one-draw weight sum. -/
lemma weightedTapeMass_eq_pow_sum {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (t : ℕ) :
    weightedTapeMass w t = (∑ a, w a) ^ t := by
  classical
  induction t with
  | zero => simp [weightedTapeMass, tapeWeight]
  | succ t ih =>
      let e : Ω × Tape Ω t ≃ Tape Ω (t + 1) :=
        Fin.consEquiv (fun _ : Fin (t + 1) => Ω)
      calc
        weightedTapeMass w (t + 1) =
            ∑ a : Ω, ∑ tail : Tape Ω t, w a * tapeWeight w tail := by
              unfold weightedTapeMass
              rw [← Fintype.sum_equiv e
                (fun pair => tapeWeight w (e pair)) (fun tape => tapeWeight w tape)
                (by intro pair; rfl)]
              rw [Fintype.sum_prod_type]
              apply Fintype.sum_congr
              intro a
              apply Fintype.sum_congr
              intro tail
              exact tapeWeight_cons w a tail
        _ = (∑ a, w a) ^ (t + 1) := by
              calc
                (∑ a, ∑ tail : Tape Ω t, w a * tapeWeight w tail) =
                    ∑ a, w a * (∑ tail : Tape Ω t, tapeWeight w tail) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      exact (Finset.mul_sum _ _ _).symm
                _ = (∑ a, w a) * weightedTapeMass w t := by
                      rw [← Finset.sum_mul]
                      rfl
                _ = (∑ a, w a) ^ (t + 1) := by
                      rw [ih, pow_succ]
                      ring

/-- Normalized one-draw weights induce total mass one on every finite tape
space. -/
lemma weightedTapeMass_eq_one {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (hnorm : ∑ a, w a = 1) (t : ℕ) :
    weightedTapeMass w t = 1 := by
  rw [weightedTapeMass_eq_pow_sum, hnorm, one_pow]

/-- The weighted mass of tapes whose every draw is bad is the bad-outcome
mass raised to the tape length. -/
lemma weighted_allBad_mass {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (bad : Ω → Bool) (t : ℕ) :
    (∑ tape : Tape Ω t,
      if ∀ i, bad (tape i) = true then tapeWeight w tape else 0) =
      (∑ a, if bad a = true then w a else 0) ^ t := by
  classical
  let wBad : Ω → ℚ := fun a => if bad a = true then w a else 0
  have hweight (tape : Tape Ω t) :
      (if ∀ i, bad (tape i) = true then tapeWeight w tape else 0) =
        tapeWeight wBad tape := by
    by_cases hall : ∀ i, bad (tape i) = true
    · simp only [if_pos hall, tapeWeight]
      apply Finset.prod_congr rfl
      intro i _
      simp [wBad, hall i]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hzero : wBad (tape i) = 0 := by simp [wBad, hi]
      have hprod : (∏ j : Fin t, wBad (tape j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [hall, tapeWeight, wBad, hprod]
  calc
    _ = weightedTapeMass wBad t := by
          unfold weightedTapeMass
          apply Finset.sum_congr rfl
          intro tape _
          exact hweight tape
    _ = badMass w bad ^ t := by
          rw [weightedTapeMass_eq_pow_sum]
          rfl

/-- Under normalized weights, the mean actual attempt count obeys the exact
recurrence `E[t+1] = 1 + badMass * E[t]`. -/
lemma weightedMeanAttempts_succ {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (bad : Ω → Bool) (t : ℕ)
    (hnorm : ∑ a, w a = 1) :
    weightedMeanAttempts w bad (t + 1) =
      1 + badMass w bad * weightedMeanAttempts w bad t := by
  classical
  let e : Ω × Tape Ω t ≃ Tape Ω (t + 1) :=
    Fin.consEquiv (fun _ : Fin (t + 1) => Ω)
  have hpoint (a : Ω) (tail : Tape Ω t) :
      tapeWeight w (e (a, tail)) *
          (attemptsUsed bad (List.ofFn (e (a, tail))) : ℚ) =
        w a * tapeWeight w tail *
          (if bad a = true then
            (attemptsUsed bad (List.ofFn tail) : ℚ) + 1 else 1) := by
    dsimp only [e]
    rw [tapeWeight_cons, attemptsUsed_cons]
    split_ifs <;> push_cast <;> ring
  have hinner (a : Ω) :
      (∑ tail : Tape Ω t,
        w a * tapeWeight w tail *
          (if bad a = true then
            (attemptsUsed bad (List.ofFn tail) : ℚ) + 1 else 1)) =
        if bad a = true then
          w a * (weightedMeanAttempts w bad t + weightedTapeMass w t)
        else w a * weightedTapeMass w t := by
    by_cases h : bad a = true
    · simp only [h, if_true]
      calc
        (∑ tail : Tape Ω t,
          w a * tapeWeight w tail *
            ((attemptsUsed bad (List.ofFn tail) : ℚ) + 1)) =
          ∑ tail : Tape Ω t,
            w a * (tapeWeight w tail * ((attemptsUsed bad (List.ofFn tail) : ℚ) + 1)) := by
              apply Finset.sum_congr rfl
              intro tail _
              ring
        _ = w a * ∑ tail : Tape Ω t,
            tapeWeight w tail * ((attemptsUsed bad (List.ofFn tail) : ℚ) + 1) := by
              rw [← Finset.mul_sum]
        _ = w a * (weightedMeanAttempts w bad t + weightedTapeMass w t) := by
              congr 1
              calc
                (∑ tail : Tape Ω t,
                    tapeWeight w tail * ((attemptsUsed bad (List.ofFn tail) : ℚ) + 1)) =
                    (∑ tail : Tape Ω t,
                      tapeWeight w tail * (attemptsUsed bad (List.ofFn tail) : ℚ)) +
                      ∑ tail : Tape Ω t, tapeWeight w tail := by
                        rw [← Finset.sum_add_distrib]
                        apply Finset.sum_congr rfl
                        intro tail _
                        ring
                _ = weightedMeanAttempts w bad t + weightedTapeMass w t := by
                      simp only [weightedMeanAttempts, weightedTapeMass]
    · have hfalse : bad a ≠ true := h
      simp only [hfalse]
      calc
        (∑ tail : Tape Ω t,
          w a * tapeWeight w tail * 1) =
          ∑ tail : Tape Ω t, w a * tapeWeight w tail := by
              apply Finset.sum_congr rfl
              intro tail _
              ring
        _ = w a * ∑ tail : Tape Ω t, tapeWeight w tail := by
              rw [← Finset.mul_sum]
        _ = w a * weightedTapeMass w t := by rfl
  calc
    weightedMeanAttempts w bad (t + 1) =
        ∑ a : Ω, ∑ tail : Tape Ω t,
          w a * tapeWeight w tail *
            (if bad a = true then
              (attemptsUsed bad (List.ofFn tail) : ℚ) + 1 else 1) := by
          unfold weightedMeanAttempts
          rw [← Fintype.sum_equiv e
            (fun pair => tapeWeight w (e pair) *
              (attemptsUsed bad (List.ofFn (e pair)) : ℚ))
            (fun tape => tapeWeight w tape *
              (attemptsUsed bad (List.ofFn tape) : ℚ))
            (by intro pair; rfl)]
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro tail _
          exact hpoint a tail
    _ = ∑ a, if bad a = true then
          w a * (weightedMeanAttempts w bad t + weightedTapeMass w t)
        else w a * weightedTapeMass w t := by
          apply Finset.sum_congr rfl
          intro a _
          exact hinner a
    _ = 1 + badMass w bad * weightedMeanAttempts w bad t := by
          calc
            (∑ a, if bad a = true then
                w a * (weightedMeanAttempts w bad t + weightedTapeMass w t)
              else w a * weightedTapeMass w t) =
                (∑ a, w a * weightedTapeMass w t) +
                  (∑ a, (if bad a = true then w a else 0) * weightedMeanAttempts w bad t) := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro a _
                    by_cases h : bad a = true
                    · simp [h]
                      ring
                    · simp [h]
            _ = (∑ a, w a) * weightedTapeMass w t +
                  badMass w bad * weightedMeanAttempts w bad t := by
                    rw [← Finset.sum_mul, ← Finset.sum_mul]
                    rfl
            _ = 1 + badMass w bad * weightedMeanAttempts w bad t := by
                    rw [hnorm, weightedTapeMass_eq_one w hnorm]
                    ring

/-- Under a normalized nonnegative finite law with bad mass at most one half,
the mean actual number of inspected attempts on every finite tape is at most
two. -/
lemma weightedMeanAttempts_le_two {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (bad : Ω → Bool) (t : ℕ)
    (hw : ∀ a, 0 ≤ w a) (hnorm : ∑ a, w a = 1)
    (hbad : badMass w bad ≤ 1 / 2) :
    weightedMeanAttempts w bad t ≤ 2 := by
  have hnonneg : 0 ≤ badMass w bad := by
    unfold badMass
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> [exact hw a; norm_num]
  have hrec (n : ℕ) : 0 ≤ weightedMeanAttempts w bad n ∧
      weightedMeanAttempts w bad n ≤ 2 := by
    induction n with
    | zero => constructor <;> simp [weightedMeanAttempts, tapeWeight, attemptsUsed, List.ofFn]
    | succ n ih =>
        rw [weightedMeanAttempts_succ w bad n hnorm]
        constructor
        · nlinarith [mul_nonneg hnonneg ih.1]
        · have hprod₁ : badMass w bad * weightedMeanAttempts w bad n ≤
              badMass w bad * 2 := mul_le_mul_of_nonneg_left ih.2 hnonneg
          have hprod₂ : badMass w bad * 2 ≤ (1 / 2) * 2 :=
            mul_le_mul_of_nonneg_right hbad (by norm_num)
          have hprod : badMass w bad * weightedMeanAttempts w bad n ≤
              (1 / 2) * 2 := le_trans hprod₁ hprod₂
          nlinarith
  exact (hrec t).2

/-- The exact all-bad product mass is at most a `2^t` fraction when bad mass
is at most one half. -/
lemma weighted_allBad_mass_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (bad : Ω → Bool) (t : ℕ)
    (hw : ∀ a, 0 ≤ w a) (hbad : badMass w bad ≤ 1 / 2) :
    (∑ tape : Tape Ω t,
      if ∀ i, bad (tape i) = true then tapeWeight w tape else 0) ≤ (1 / 2 : ℚ) ^ t := by
  rw [weighted_allBad_mass]
  have hbad_nonneg : 0 ≤ badMass w bad := by
    unfold badMass
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> [exact hw a; norm_num]
  exact pow_le_pow_left₀ hbad_nonneg hbad t

end Lax457868Proofs.SamplerWeightedRetries
