import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
Numeric arithmetic for the failure coefficient in the paper's local repair
trial bound. This module proves only the coefficient inequality; it does not
formalize the epsilon-net estimate that supplies that coefficient.
-/

namespace Lax457868Proofs.SamplerTrialBound

/-- Every natural number is bounded by the corresponding power of two. -/
lemma le_two_pow (L : ℕ) : L ≤ 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by omega)
      omega

/-- Generic integral form of the strict trial-coefficient bound. -/
lemma trial_coefficient_lt {c L : ℕ} (hL : 1 ≤ L) (hc : c ≤ 2 ^ L) :
    8 * c * (64 * L) < 2 ^ (16 * L) := by
  have hLpow := le_two_pow L
  have hmul₁ : 8 * c * (64 * L) ≤ 512 * (2 ^ L) * L := by
    calc
      8 * c * (64 * L) = 512 * c * L := by ring
      _ = c * (512 * L) := by ring
      _ ≤ (2 ^ L) * (512 * L) := Nat.mul_le_mul_right _ hc
      _ = 512 * (2 ^ L) * L := by ring
  have hmul₂ : 512 * (2 ^ L) * L ≤ 2 ^ (9 + 2 * L) := by
    calc
      512 * (2 ^ L) * L ≤ 512 * (2 ^ L) * (2 ^ L) :=
        Nat.mul_le_mul_left (512 * (2 ^ L)) hLpow
      _ = 2 ^ (9 + 2 * L) := by
        rw [show 512 = 2 ^ 9 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
  have hexp : 9 + 2 * L < 16 * L := by omega
  have hpow : 2 ^ (9 + 2 * L) < 2 ^ (16 * L) := by
    exact Nat.pow_lt_pow_right (by omega) hexp
  exact (hmul₁.trans hmul₂).trans_lt hpow

/-- For `c ≥ 2`, choosing the integral sample size parameter
`s = 64 * Nat.clog 2 c` makes the paper's coefficient strictly less than
one half, after clearing its denominator: `8*c*s < 2^(s/4)`. -/
lemma clog_trial_coefficient_lt_half {c : ℕ} (hc : 2 ≤ c) :
    8 * c * (64 * Nat.clog 2 c) < 2 ^ (16 * Nat.clog 2 c) := by
  apply trial_coefficient_lt
  · exact Nat.clog_pos (by omega) hc
  · exact Nat.le_pow_clog (by omega) c

end Lax457868Proofs.SamplerTrialBound
