import Lax235315Proofs.Construction.ReadKeys
import Mathlib.Tactic

/-! Amortized active-set charges. Reading random keys costs logarithmic time
per active vertex, while scanning inactive vertices has constant cost. -/

namespace Lax235315Proofs.Construction.CostAccounting
open Finset

/-- Halving with an additive rounding allowance bounds the total mass of all
pre-reduction active sets by twice the initial mass plus the allowances. -/
lemma sum_active_le (a : ℕ → ℕ) (d R : ℕ)
    (hstep : ∀ i < R, 2 * a (i + 1) ≤ a i + d) :
    (∑ i ∈ range R, a i) ≤ 2 * a 0 + d * R := by
  have hsum := Finset.sum_le_sum (s := range R)
    (fun i hi => hstep i (mem_range.mp hi))
  have hshift : (∑ i ∈ range R, a (i + 1)) + a 0 =
      (∑ i ∈ range R, a i) + a R := by
    rw [← sum_range_succ', sum_range_succ]
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul,
    ← mul_sum] at hsum
  nlinarith

/-- The paper's guarded regime absorbs the accumulated rounding allowances. -/
lemma sum_active_le_three_initial {a : ℕ → ℕ} {n c L R : ℕ}
    (hzero : a 0 ≤ n) (hrounds : R ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n)
    (hstep : ∀ i < R, a (i + 1) ≤ a i / 2 + c ^ 2) :
    (∑ i ∈ range R, a i) ≤ 3 * n := by
  have htwice : ∀ i < R, 2 * a (i + 1) ≤ a i + 2 * c ^ 2 := by
    intro i hi
    have hs := hstep i hi
    have hd : a i / 2 * 2 ≤ a i := Nat.div_mul_le_self _ _
    omega
  have hs := sum_active_le a (2 * c ^ 2) R htwice
  have hr := Nat.mul_le_mul_left (2 * c ^ 2) hrounds
  nlinarith

/-- The exact sharpened readKeys charges sum to a near-linear bound. -/
lemma total_key_reading_cost_le {a : ℕ → ℕ} {n c L R : ℕ}
    (hzero : a 0 ≤ n) (hrounds : R ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n)
    (hstep : ∀ i < R, a (i + 1) ≤ a i / 2 + c ^ 2) :
    (∑ i ∈ range R, (120 * n + 120 * L * a i + 8)) ≤
      488 * (n + 1) * (L + 1) := by
  have hs := sum_active_le_three_initial hzero hrounds hguard hstep
  have hscaled := Nat.mul_le_mul_left (120 * L) hs
  have hscan := Nat.mul_le_mul_left (120 * n + 8) hrounds
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul,
    ← mul_sum]
  nlinarith

/-- Eight L-bit digits per active vertex fit in a near-linear total bit budget. -/
lemma total_key_bits_le {a : ℕ → ℕ} {n c L R : ℕ}
    (hzero : a 0 ≤ n) (hrounds : R ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n)
    (hstep : ∀ i < R, a (i + 1) ≤ a i / 2 + c ^ 2) :
    (∑ i ∈ range R, 8 * L * a i) ≤ 24 * n * L := by
  have hs := sum_active_le_three_initial hzero hrounds hguard hstep
  rw [← mul_sum]
  nlinarith [Nat.mul_le_mul_left (8 * L) hs]

/-- A final failed round has no successor contraction. Charging it separately
still leaves the same near-linear asymptotic bound. -/
lemma total_key_reading_with_failure_le {a : ℕ → ℕ} {n c L R last : ℕ}
    (hzero : a 0 ≤ n) (hrounds : R ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n) (hlast : last ≤ n)
    (hstep : ∀ i < R, a (i + 1) ≤ a i / 2 + c ^ 2) :
    (∑ i ∈ range R, (120 * n + 120 * L * a i + 8)) +
      (120 * n + 120 * L * last + 8) ≤
      736 * (n + 1) * (L + 1) := by
  have hs := total_key_reading_cost_le hzero hrounds hguard hstep
  have hl := Nat.mul_le_mul_left (120 * L) hlast
  nlinarith

/-- A rejected final round also consumes only one additional active-set block. -/
lemma total_key_bits_with_failure_le {a : ℕ → ℕ} {n c L R last : ℕ}
    (hzero : a 0 ≤ n) (hrounds : R ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n) (hlast : last ≤ n)
    (hstep : ∀ i < R, a (i + 1) ≤ a i / 2 + c ^ 2) :
    (∑ i ∈ range R, 8 * L * a i) + 8 * L * last ≤ 32 * n * L := by
  have hs := total_key_bits_le hzero hrounds hguard hstep
  have hl := Nat.mul_le_mul_left (8 * L) hlast
  nlinarith

end Lax235315Proofs.Construction.CostAccounting
