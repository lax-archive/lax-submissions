import Lax457868Proofs.ReductionPath

/-! Aggregate active-set work across the actual successful reduction path.
The linear scans use the round bound; random draws use the shrinking active
sizes, avoiding an extra logarithm in their total charge. -/

namespace Lax457868Proofs.RefinedRoundCost

open Lax457868Proofs.AlgorithmRounds
open Lax457868Proofs.ReductionPath
open Lax457868Proofs.ReductionPath.SuccessfulReductionPath
open Lax195003.WelzlOrdersNeighborhoodComplexity
open scoped BigOperators

/-- Above the stopping threshold, the additive contraction recurrence gives
a uniform two-thirds contraction. -/
lemma active_size_contracts {a b c k : ℕ}
    (hstep : 2 * b ≤ a + 2 * c ^ 2)
    (hk : 6 * c ^ 2 ≤ k) (hcontinue : 2 * k < a) :
    3 * b ≤ 2 * a := by
  nlinarith

/-- Telescope the contraction, retaining the terminal potential. -/
lemma active_size_sum_potential (a : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ i < r, 3 * a (i + 1) ≤ 2 * a i) :
    (∑ i ∈ Finset.range r, a i) + 3 * a r ≤ 3 * a 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    have hl := hstep r (by omega)
    rw [Finset.sum_range_succ]
    omega

/-- The active sizes actually sampled on a successful path sum to at most
three times the initial ground-set size. -/
lemma successful_path_size_sum {n c k : ℕ} {G : SimpleGraph (Fin n)}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A C : Finset (Fin n)} (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (path : SuccessfulReductionPath G c k hG A C) :
    (∑ i ∈ Finset.range (rounds path), activeGroundSize path i) ≤ 3 * A.card := by
  have hp := active_size_sum_potential (activeGroundSize path) (rounds path)
    (fun i hi => active_size_contracts (active_ground_recurrence hc path i hi)
      hk (active_ground_guard path i hi))
  simp only [activeGroundSize] at hp
  omega

/-- Combine full-input scans with active-size draw costs. The coefficients
are supplied by the checked component costs, not chosen independently. -/
lemma successful_path_total_charge {n c k M D ℓ : ℕ}
    {G : SimpleGraph (Fin n)}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A C : Finset (Fin n)} (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (hA : 2 ≤ A.card) (hinput : n ≤ ℓ + 1)
    (path : SuccessfulReductionPath G c k hG A C) :
    (∑ i ∈ Finset.range (rounds path),
      (M * (ℓ + 1) + D * activeGroundSize path i * (Nat.clog 2 n + 1))) ≤
      (M + 3 * D) * (ℓ + 1) * (Nat.clog 2 n + 1) := by
  have hcard : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hsum := successful_path_size_sum hc hk path
  have hr := successful_path_round_bound hc hk hA path
  have hlog : Nat.clog 2 A.card ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hcard
  have hrounds : rounds path ≤ Nat.clog 2 n + 1 := by omega
  have hs : (∑ i ∈ Finset.range (rounds path), activeGroundSize path i) ≤
      3 * (ℓ + 1) := by omega
  calc
    _ = rounds path * (M * (ℓ + 1)) +
        D * (∑ i ∈ Finset.range (rounds path), activeGroundSize path i) *
          (Nat.clog 2 n + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    _ ≤ (Nat.clog 2 n + 1) * (M * (ℓ + 1)) +
        D * (3 * (ℓ + 1)) * (Nat.clog 2 n + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hrounds)
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D hs))
    _ = _ := by ring

end Lax457868Proofs.RefinedRoundCost
