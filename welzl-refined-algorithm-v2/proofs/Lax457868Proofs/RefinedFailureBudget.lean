import Lax457868Proofs.AlgorithmRounds
import Lax457868Proofs.SaturatedCutoff
import Mathlib.Tactic

/-! Numerical budget for union-bounding capped selectors and exhausted
trials on the large-input branch. Actual event counts are separate source
obligations; these inequalities do not assert those events are independent. -/
namespace Lax457868Proofs.RefinedFailureBudget

lemma fourth_power_step {n : ℕ} (hn : 8 ≤ n) :
    (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
  have h : 8 * (n + 1) ≤ 9 * n := by omega
  have hp := Nat.pow_le_pow_left h 4
  simp only [mul_pow] at hp
  norm_num at hp
  omega

/-- Thirty-two is a sufficient explicit starting point for the polynomial
union bound; the subsequent inequality is preserved by doubling. -/
lemma polynomial_failure_budget {n : ℕ} (hn : 32 ≤ n) :
    24 * n ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp := fourth_power_step (by omega : 8 ≤ n)
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]
    omega

lemma large_input_ge_32 {c n : ℕ} (hc : 2 ≤ c)
    (hlarge : 2 * refinedCutoffK c < n) : 32 ≤ n := by
  have hk := AlgorithmRounds.refined_cutoff_ge_six_sq c hc
  change 6 * c ^ 2 ≤ refinedCutoffK c at hk
  have hc2 : 4 ≤ c ^ 2 := by nlinarith
  omega

/-- Over at most `n` rounds, initial attempts have at most `2n` selector
calls and local attempts at most `n` calls per exception. Retry exhaustion
adds one event per initial loop and per exception loop. -/
lemma failure_opportunities_le {n : ℕ} (hn : 2 ≤ n) :
    n * (n * (2 * n) + n * (n * n) + 1 + n) ≤ 4 * n ^ 4 := by
  have h2 : 2 * n ^ 3 ≤ n ^ 4 := by
    calc
      2 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
      _ = n ^ 4 := by ring
  have hsq : 2 ≤ n ^ 2 := by nlinarith
  have h3 : n ^ 2 + n ≤ n ^ 4 := by
    calc
      n ^ 2 + n ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul_right _ hsq
      _ = n ^ 4 := by ring
  have heq : n * (n * (2 * n) + n * (n * n) + 1 + n) =
      2 * n ^ 3 + n ^ 4 + (n ^ 2 + n) := by ring
  rw [heq]
  omega

lemma opportunities_fit_sixth {c n : ℕ} (hc : 2 ≤ c)
    (hlarge : 2 * refinedCutoffK c < n) :
    6 * (n * (n * (2 * n) + n * (n * n) + 1 + n)) ≤ 2 ^ n := by
  have hn := large_input_ge_32 hc hlarge
  have hcount := failure_opportunities_le (by omega : 2 ≤ n)
  have hbudget := polynomial_failure_budget hn
  nlinarith

end Lax457868Proofs.RefinedFailureBudget
