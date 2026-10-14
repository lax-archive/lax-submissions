import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Finite counting lemmas for the initial-attempt acceptance probability. The
expectation bound on the exceptional count is an explicit hypothesis here.
-/

namespace Lax457868Proofs.SamplerAcceptance

open Finset

/-- Outcomes whose exceptional count exceeds the natural-number threshold
`n / D`, expressed without division as `n < D * q`. -/
def rejected {Ω : Type*} [Fintype Ω] (q : Ω → ℕ) (n D : ℕ) : Finset Ω :=
  Finset.univ.filter fun ω => n < D * q ω

/-- Summing a pointwise exceptional-count estimate preserves its coefficient. -/
lemma sum_mul_le_sum_mul {Ω : Type*} [Fintype Ω] (k : ℕ)
    (q Z : Ω → ℕ) (h : ∀ ω, k * q ω ≤ 3 * Z ω) :
    k * (∑ ω, q ω) ≤ 3 * (∑ ω, Z ω) := by
  calc
    k * (∑ ω, q ω) = ∑ ω, k * q ω := by simp [Finset.mul_sum]
    _ ≤ ∑ ω, 3 * Z ω := Finset.sum_le_sum fun ω _ => h ω
    _ = 3 * (∑ ω, Z ω) := by simp [Finset.mul_sum]

/-- Finite Markov bound: if twice the total weighted exceptional count is at
most `n` times the number of outcomes, at most half the outcomes exceed the
threshold `n / D`. -/
lemma twice_rejected_card_le {Ω : Type*} [Fintype Ω]
    (q : Ω → ℕ) (n D : ℕ) (hn : 0 < n)
    (hbound : 2 * D * (∑ ω, q ω) ≤ n * Fintype.card Ω) :
    2 * (rejected q n D).card ≤ Fintype.card Ω := by
  classical
  let R := rejected q n D
  have hsumSubset : (∑ ω ∈ R, q ω) ≤ ∑ ω, q ω := by
    calc
      (∑ ω ∈ R, q ω) = ∑ ω ∈ Finset.univ, if ω ∈ R then q ω else 0 := by
        simp
      _ ≤ ∑ ω ∈ Finset.univ, q ω := by
        apply Finset.sum_le_sum
        intro ω hω
        split_ifs <;> omega
  have hweighted : R.card * n ≤ D * (∑ ω, q ω) := by
    calc
      R.card * n = ∑ _ω ∈ R, n := by simp
      _ ≤ ∑ ω ∈ R, D * q ω := by
        apply Finset.sum_le_sum
        intro ω hω
        have hω' : n < D * q ω := (Finset.mem_filter.mp hω).2
        exact Nat.le_of_lt hω'
      _ = D * (∑ ω ∈ R, q ω) := by simp [Finset.mul_sum]
      _ ≤ D * (∑ ω, q ω) := Nat.mul_le_mul_left D hsumSubset
  have hmul : n * (2 * R.card) ≤ n * Fintype.card Ω := by
    calc
      n * (2 * R.card) = 2 * (R.card * n) := by ring
      _ ≤ 2 * (D * (∑ ω, q ω)) := Nat.mul_le_mul_left 2 hweighted
      _ = 2 * D * (∑ ω, q ω) := by ring
      _ ≤ n * Fintype.card Ω := hbound
  have hcard : 2 * R.card ≤ Fintype.card Ω :=
    Nat.le_of_mul_le_mul_left hmul hn
  simpa [R] using hcard

/-- Pointwise exceptional counts yield the aggregate hypothesis needed by
`twice_rejected_card_le`, provided the expected distance bound is supplied. -/
lemma twice_D_sum_q_le_of_distance_bound {Ω : Type*} [Fintype Ω]
    (q Z : Ω → ℕ) (n D k : ℕ) (hk : 0 < k)
    (hq : ∀ ω, k * q ω ≤ 3 * Z ω)
    (hZ : 6 * D * (∑ ω, Z ω) ≤ n * k * Fintype.card Ω) :
    2 * D * (∑ ω, q ω) ≤ n * Fintype.card Ω := by
  have hsum := sum_mul_le_sum_mul k q Z hq
  have hmul : k * (2 * D * (∑ ω, q ω)) ≤ k * (n * Fintype.card Ω) := by
    calc
      k * (2 * D * (∑ ω, q ω)) = 2 * D * (k * (∑ ω, q ω)) := by ring
      _ ≤ 2 * D * (3 * (∑ ω, Z ω)) := Nat.mul_le_mul_left (2 * D) hsum
      _ = 6 * D * (∑ ω, Z ω) := by ring
      _ ≤ n * k * Fintype.card Ω := hZ
      _ = k * (n * Fintype.card Ω) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hk

/-- Acceptance probability is at least one half under the stated distance
bound. This is only the finite counting step; it does not establish the
sampler's expected-distance hypothesis. -/
lemma twice_rejected_card_le_of_distance_bound {Ω : Type*} [Fintype Ω]
    (q Z : Ω → ℕ) (n D k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hq : ∀ ω, k * q ω ≤ 3 * Z ω)
    (hZ : 6 * D * (∑ ω, Z ω) ≤ n * k * Fintype.card Ω) :
    2 * (rejected q n D).card ≤ Fintype.card Ω := by
  apply twice_rejected_card_le q n D hn
  exact twice_D_sum_q_le_of_distance_bound q Z n D k hk hq hZ

end Lax457868Proofs.SamplerAcceptance
