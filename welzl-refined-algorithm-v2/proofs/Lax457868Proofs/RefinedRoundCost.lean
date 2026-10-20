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

/-- The shifted halving potential is preserved by each accepted source
round, including a final round whose active set falls below the shift. -/
lemma round_potential_step {a b c r n : ℕ}
    (hstep : 2 * b ≤ a + 2 * c ^ 2)
    (hpot : 2 ^ r * (a - 2 * c ^ 2) ≤ n) :
    2 ^ (r + 1) * (b - 2 * c ^ 2) ≤ n := by
  by_cases hb : b ≤ 2 * c ^ 2
  · simp [Nat.sub_eq_zero_of_le hb]
  · have ha : 2 * c ^ 2 ≤ a := by omega
    have hsub : 2 * (b - 2 * c ^ 2) ≤ a - 2 * c ^ 2 := by omega
    calc
      _ = 2 ^ r * (2 * (b - 2 * c ^ 2)) := by rw [pow_succ]; ring
      _ ≤ 2 ^ r * (a - 2 * c ^ 2) := Nat.mul_le_mul_left _ hsub
      _ ≤ n := hpot

/-- A true guard leaves enough shifted active size to force the next round
counter below the original logarithmic bound. -/
lemma round_counter_after_guard {a c k r n : ℕ}
    (hc : 1 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (hguard : 2 * k < a)
    (hpot : 2 ^ r * (a - 2 * c ^ 2) ≤ n) :
    r + 1 ≤ Nat.clog 2 n := by
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hshift : 2 ≤ a - 2 * c ^ 2 := by omega
  have hp : 0 < 2 ^ r := by positivity
  have hpn : 2 ^ r < n := by nlinarith
  exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide)).mpr hpn)

/-- Reserve the terminal reconstruction contribution as well as the round
just executed. A true guard leaves more than two units of shifted mass. -/
lemma round_counter_with_terminal_after_guard {a c k r n : ℕ}
    (hc : 1 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (hguard : 2 * k < a)
    (hpot : 2 ^ r * (a - 2 * c ^ 2) ≤ n) :
    r + 2 ≤ Nat.clog 2 n := by
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hshift : 3 ≤ a - 2 * c ^ 2 := by omega
  have hp : 0 < 2 ^ r := by positivity
  have hpn : 2 ^ (r + 1) < n := by
    rw [pow_succ]
    nlinarith
  exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide)).mpr hpn)

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

/-- Aggregate per-round source means over complete tapes. Stopped paths are
padded with zero active size and zero cost. No independence between rounds,
or conditioning on a successful path, is assumed. -/
lemma expected_total_charge {Ω : Type*} [Fintype Ω]
    (active charge : Ω → ℕ → ℕ) (R M D ℓ L : ℕ)
    (hrounds : R ≤ L + 1)
    (hfirst : ∀ ρ, active ρ 0 ≤ ℓ + 1)
    (hstep : ∀ ρ i, i < R → 3 * active ρ (i + 1) ≤ 2 * active ρ i)
    (hmean : ∀ i < R, (∑ ρ, charge ρ i) ≤
      ∑ ρ, (M * (ℓ + 1) + D * active ρ i * (L + 1))) :
    (∑ ρ, ∑ i ∈ Finset.range R, charge ρ i) ≤
      (M + 3 * D) * (ℓ + 1) * (L + 1) * Fintype.card Ω := by
  have hp (ρ : Ω) :
      (∑ i ∈ Finset.range R, (M * (ℓ + 1) + D * active ρ i * (L + 1))) ≤
        (M + 3 * D) * (ℓ + 1) * (L + 1) := by
    have hsum := active_size_sum_potential (active ρ) R (hstep ρ)
    have hs : (∑ i ∈ Finset.range R, active ρ i) ≤ 3 * (ℓ + 1) := by
      have hf := hfirst ρ
      omega
    calc
      _ = R * (M * (ℓ + 1)) +
          D * (∑ i ∈ Finset.range R, active ρ i) * (L + 1) := by
        simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
      _ ≤ (L + 1) * (M * (ℓ + 1)) + D * (3 * (ℓ + 1)) * (L + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hrounds)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D hs))
      _ = _ := by ring
  calc
    _ = ∑ i ∈ Finset.range R, ∑ ρ, charge ρ i := Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range R, ∑ ρ,
        (M * (ℓ + 1) + D * active ρ i * (L + 1)) :=
      Finset.sum_le_sum fun i hi => hmean i (Finset.mem_range.mp hi)
    _ = ∑ ρ, ∑ i ∈ Finset.range R,
        (M * (ℓ + 1) + D * active ρ i * (L + 1)) := Finset.sum_comm
    _ ≤ ∑ _ρ : Ω, (M + 3 * D) * (ℓ + 1) * (L + 1) :=
      Finset.sum_le_sum fun ρ _ => hp ρ
    _ = _ := by simp [Nat.mul_comm]

end Lax457868Proofs.RefinedRoundCost
