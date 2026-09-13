import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Lax17Proofs.Source.CrossbarPower

namespace Lax17Proofs

universe u v w

/-!
# Arithmetic for the polynomial grid-minor proof

This file collects small natural-number facts used to pass between arbitrary
grid orders and the power-of-two parameters used in Chuzhoy--Tan's proof.
-/

namespace SimpleGraph
namespace GridMinorArithmetic

/-- The largest power of two controlled by `Nat.log 2 n`. -/
def powTwoFloor (n : ℕ) : ℕ :=
  2 ^ Nat.log 2 n

/-- `powTwoFloor n` is an integral power of two. -/
theorem isPowerOfTwo_powTwoFloor (n : ℕ) :
    CrossbarContract.IsPowerOfTwo (powTwoFloor n) :=
  ⟨Nat.log 2 n, rfl⟩

/-- Rounding a power of two down to the nearest power of two leaves it
unchanged. -/
@[simp] theorem powTwoFloor_two_pow (r : ℕ) :
    powTwoFloor (2 ^ r) = 2 ^ r := by
  simp [powTwoFloor, Nat.log_pow (by decide : 1 < 2)]

/-- Power of a power of two, with the exponent multiplied out. -/
theorem two_pow_pow (m a : ℕ) :
    (2 ^ m) ^ a = 2 ^ (m * a) := by
  simpa using (Nat.pow_mul 2 m a).symm

/-- Every natural number is bounded by the corresponding power of two. -/
theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n :=
          Nat.add_le_add_left (Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))) _
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

/-- From exponent four onward, `2^q` dominates `3*q`.  This lightweight
growth lemma is useful for comparing cubic powers of `2^q` with `2^(2^q)`. -/
theorem three_mul_le_two_pow_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    3 * q ≤ 2 ^ q := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hfour : 4 ≤ q
      · have htwo_le_q : 2 ≤ q := le_trans (by decide : 2 ≤ 4) hfour
        have hpow_ge_three : 3 ≤ 2 ^ q := by
          exact le_trans (by decide : 3 ≤ 2 ^ 2)
            (Nat.pow_le_pow_right (by decide : 0 < 2) htwo_le_q)
        calc
          3 * (q + 1) = 3 * q + 3 := by omega
          _ ≤ 2 ^ q + 2 ^ q := Nat.add_le_add (ih hfour) hpow_ge_three
          _ = 2 ^ (q + 1) := by
            rw [Nat.pow_succ]
            omega
      · have hq_eq_three : q = 3 := by omega
        subst q
        decide

/-- A cubic power of `2^q` is bounded by `2^(2^q)` once `q >= 4`. -/
theorem two_pow_cube_le_two_pow_two_pow_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    (2 ^ q) ^ 3 ≤ 2 ^ (2 ^ q) := by
  calc
    (2 ^ q) ^ 3 = 2 ^ (q * 3) := GridMinorArithmetic.two_pow_pow q 3
    _ = 2 ^ (3 * q) := by rw [Nat.mul_comm q 3]
    _ ≤ 2 ^ (2 ^ q) :=
      Nat.pow_le_pow_right (by decide : 0 < 2)
        (three_mul_le_two_pow_of_four_le hq)

/-- From exponent five onward, `2^q` dominates `3*q + 2`.  This variant is
used when a cubic comparison carries an extra factor `4 = 2^2`. -/
theorem two_add_three_mul_le_two_pow_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    2 + 3 * q ≤ 2 ^ q := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hfive : 5 ≤ q
      · have htwo_le_q : 2 ≤ q := le_trans (by decide : 2 ≤ 5) hfive
        have hpow_ge_three : 3 ≤ 2 ^ q := by
          exact le_trans (by decide : 3 ≤ 2 ^ 2)
            (Nat.pow_le_pow_right (by decide : 0 < 2) htwo_le_q)
        calc
          2 + 3 * (q + 1) = (2 + 3 * q) + 3 := by omega
          _ ≤ 2 ^ q + 2 ^ q := Nat.add_le_add (ih hfive) hpow_ge_three
          _ = 2 ^ (q + 1) := by
            rw [Nat.pow_succ]
            omega
      · have hq_eq_four : q = 4 := by omega
        subst q
        decide

/-- A cubic power of `2^q`, with an extra factor `4`, is still bounded by
`2^(2^q)` once `q >= 5`. -/
theorem four_mul_two_pow_cube_le_two_pow_two_pow_of_five_le {q : ℕ}
    (hq : 5 ≤ q) :
    4 * (2 ^ q) ^ 3 ≤ 2 ^ (2 ^ q) := by
  calc
    4 * (2 ^ q) ^ 3 = 2 ^ (2 + q * 3) := by
      rw [show 4 = 2 ^ 2 by rfl]
      rw [GridMinorArithmetic.two_pow_pow]
      rw [← pow_add]
    _ = 2 ^ (2 + 3 * q) := by rw [Nat.mul_comm q 3]
    _ ≤ 2 ^ (2 ^ q) :=
      Nat.pow_le_pow_right (by decide : 0 < 2)
        (two_add_three_mul_le_two_pow_of_five_le hq)

/-- Strict cubic domination by `2^(2^q)` once `q >= 5`. -/
theorem two_pow_cube_lt_two_pow_two_pow_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    (2 ^ q) ^ 3 < 2 ^ (2 ^ q) := by
  have hpos : 0 < (2 ^ q) ^ 3 :=
    Nat.pow_pos (Nat.pow_pos (by decide : 0 < 2))
  have hlt_four : (2 ^ q) ^ 3 < 4 * (2 ^ q) ^ 3 := by
    calc
      (2 ^ q) ^ 3 = 1 * (2 ^ q) ^ 3 := by simp
      _ < 4 * (2 ^ q) ^ 3 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4) hpos
  exact lt_of_lt_of_le hlt_four
    (four_mul_two_pow_cube_le_two_pow_two_pow_of_five_le hq)

/-- A small polynomial estimate used in the exponent bookkeeping for
threshold coefficients. -/
theorem add_succ_mul_self_le_cube {s : ℕ} (hs : 2 ≤ s) :
    s + (s + 1) * s ≤ s ^ 3 := by
  have htwo_mul_le_sq : 2 * s ≤ s * s :=
    Nat.mul_le_mul_right s hs
  have hsum_le_sq : s + s ≤ s * s := by
    calc
      s + s = 2 * s := by omega
      _ ≤ s * s := htwo_mul_le_sq
  have htwo_sq_le_cube : 2 * (s * s) ≤ s * (s * s) :=
    Nat.mul_le_mul_right (s * s) hs
  calc
    s + (s + 1) * s = s * s + (s + s) := by
      rw [Nat.add_mul, one_mul]
      ac_rfl
    _ ≤ s * s + s * s := Nat.add_le_add_left hsum_le_sq (s * s)
    _ = 2 * (s * s) := by omega
    _ ≤ s * (s * s) := htwo_sq_le_cube
    _ = s ^ 3 := by
      rw [show (3 : ℕ) = 1 + 2 by decide, pow_add]
      simp [pow_two]

/-- The binary ceiling power is within a factor of two of its argument. -/
theorem two_pow_clog_le_two_mul {n : ℕ} (hn : 1 < n) :
    2 ^ Nat.clog 2 n ≤ 2 * n := by
  have hclog_pos : 0 < Nat.clog 2 n := by
    by_contra hnot
    have hzero : Nat.clog 2 n = 0 := Nat.eq_zero_of_not_pos hnot
    have hnle : n ≤ 1 := by
      simpa [hzero] using Nat.le_pow_clog (by decide : 1 < 2) n
    omega
  have hpred :
      2 ^ (Nat.clog 2 n - 1) < n :=
    Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  calc
    2 ^ Nat.clog 2 n =
        2 ^ ((Nat.clog 2 n - 1) + 1) := by
          rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hclog_pos)]
    _ = 2 ^ (Nat.clog 2 n - 1) * 2 := by
      rw [Nat.pow_succ]
    _ ≤ n * 2 := Nat.mul_le_mul_right 2 hpred.le
    _ = 2 * n := by omega

/-- Powers of the binary ceiling power are controlled by the corresponding
power of twice the original number. -/
theorem two_pow_clog_pow_le_two_mul_pow {n a : ℕ} (hn : 1 < n) :
    (2 ^ Nat.clog 2 n) ^ a ≤ (2 * n) ^ a :=
  Nat.pow_le_pow_left (two_pow_clog_le_two_mul hn) a

/-- The binary ceiling logarithm of a number at least two is positive. -/
theorem clog_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < Nat.clog 2 n := by
  by_contra hnot
  have hzero : Nat.clog 2 n = 0 := Nat.eq_zero_of_not_pos hnot
  have hnle : n ≤ 1 := by
    simpa [hzero] using Nat.le_pow_clog (by decide : 1 < 2) n
  omega

/-- The binary ceiling logarithm is at most one more than the floor
logarithm. -/
theorem clog_le_log_succ (n : ℕ) :
    Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
  Nat.clog_le_of_le_pow
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le

/-- The binary ceiling logarithm of the binary logarithm is bounded by that
logarithm itself. -/
theorem clog_log_le_log (n : ℕ) :
    Nat.clog 2 (Nat.log 2 n) ≤ Nat.log 2 n :=
  Nat.clog_le_of_le_pow (self_le_two_pow (Nat.log 2 n))

/-- The ceiling binary logarithm of a fixed polynomial is at most linear in
the variable.  The intentionally coarse bound is convenient when constants are
kept in `ℕ`: `C * t^a <= 2^(C + t*a) <= 2^((C+a)*t)` for `t >= 1`. -/
theorem clog_mul_pow_le_linear {C t a : ℕ} (ht : 1 ≤ t) :
    Nat.clog 2 (C * t ^ a) ≤ (C + a) * t := by
  have hC : C ≤ 2 ^ C := self_le_two_pow C
  have ht_pow : t ^ a ≤ (2 ^ t) ^ a :=
    Nat.pow_le_pow_left (self_le_two_pow t) a
  have hmul : C * t ^ a ≤ 2 ^ (C + t * a) := by
    calc
      C * t ^ a ≤ 2 ^ C * (2 ^ t) ^ a :=
        Nat.mul_le_mul hC ht_pow
      _ = 2 ^ C * 2 ^ (t * a) := by
        rw [two_pow_pow]
      _ = 2 ^ (C + t * a) := by
        rw [← pow_add]
  have hclog : Nat.clog 2 (C * t ^ a) ≤ C + t * a :=
    Nat.clog_le_of_le_pow hmul
  have hlinear : C + t * a ≤ (C + a) * t := by
    have hC_le : C ≤ C * t := by
      simpa using Nat.mul_le_mul_left C ht
    calc
      C + t * a ≤ C * t + t * a :=
        Nat.add_le_add_right hC_le _
      _ = (C + a) * t := by
        rw [Nat.add_mul]
        ac_rfl
  exact le_trans hclog hlinear

/-- For `2 <= n`, the logarithmic power of two is at least `2`. -/
theorem two_le_powTwoFloor {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ powTwoFloor n := by
  have hlog : 0 < Nat.log 2 n := Nat.log_pos Nat.one_lt_two hn
  have hpow : 2 ^ 1 ≤ 2 ^ Nat.log 2 n :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  simpa [powTwoFloor] using hpow

/-- The logarithmic power of two is bounded by the original number. -/
theorem powTwoFloor_le_self {n : ℕ} (hn : 2 ≤ n) :
    powTwoFloor n ≤ n := by
  have hn0 : n ≠ 0 := by omega
  simpa [powTwoFloor] using Nat.pow_log_le_self 2 hn0

/-- Every positive integer is strictly below twice its logarithmic power of two. -/
theorem self_lt_two_mul_powTwoFloor {n : ℕ} :
    n < 2 * powTwoFloor n := by
  have h := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  simpa [powTwoFloor, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- For `2 <= n`, the logarithmic power of two is positive. -/
theorem powTwoFloor_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < powTwoFloor n :=
  lt_of_lt_of_le (by decide : 0 < 2) (two_le_powTwoFloor hn)

/-- The logarithmic power of two is within a factor of two of `n`. -/
theorem self_le_two_mul_powTwoFloor {n : ℕ} :
    n ≤ 2 * powTwoFloor n :=
  (self_lt_two_mul_powTwoFloor (n := n)).le

/-- If `2 * a <= n`, then `a` is at most the logarithmic power of two below
`n`. -/
theorem le_powTwoFloor_of_two_mul_le {a n : ℕ} (h : 2 * a ≤ n) :
    a ≤ powTwoFloor n := by
  have htwo : 0 < (2 : ℕ) := by decide
  exact Nat.le_of_mul_le_mul_left
    (le_trans h (self_le_two_mul_powTwoFloor (n := n))) htwo

/-- The logarithm of the rounded-down power of two is no larger than the
logarithm of the original scale. -/
theorem log_powTwoFloor_le_log {n : ℕ} (hn : 2 ≤ n) :
    Nat.log 2 (powTwoFloor n) ≤ Nat.log 2 n :=
  Nat.log_mono_right (powTwoFloor_le_self hn)

/-- Powers of the rounded-down power of two are bounded by the corresponding
powers of the original scale. -/
theorem pow_powTwoFloor_le_pow {n m : ℕ} (hn : 2 ≤ n) :
    (powTwoFloor n) ^ m ≤ n ^ m :=
  Nat.pow_le_pow_left (powTwoFloor_le_self hn) m

/-- If a scale `n` is at least twice a direct-branch requirement computed with
`log n`, then the rounded-down power of two below `n` satisfies the direct
branch requirement computed with its own logarithm. -/
theorem direct_bound_powTwoFloor_of_two_mul_le
    {c target n : ℕ} (hn : 2 ≤ n)
    (h : 2 * (c * target * (Nat.log 2 n) ^ 2) ≤ n) :
    c * target * (Nat.log 2 (powTwoFloor n)) ^ 2 ≤ powTwoFloor n := by
  have hlog_sq :
      (Nat.log 2 (powTwoFloor n)) ^ 2 ≤ (Nat.log 2 n) ^ 2 :=
    Nat.pow_le_pow_left (log_powTwoFloor_le_log hn) 2
  have hreq :
      c * target * (Nat.log 2 (powTwoFloor n)) ^ 2 ≤
        c * target * (Nat.log 2 n) ^ 2 := by
    calc
      c * target * (Nat.log 2 (powTwoFloor n)) ^ 2 =
          (c * target) * (Nat.log 2 (powTwoFloor n)) ^ 2 := by
        ac_rfl
      _ ≤ (c * target) * (Nat.log 2 n) ^ 2 :=
        Nat.mul_le_mul_left _ hlog_sq
      _ = c * target * (Nat.log 2 n) ^ 2 := by
        ac_rfl
  exact le_trans hreq (le_powTwoFloor_of_two_mul_le h)

/-- If `a` is at most the rounded-down power of two below `n`, then for
`2 <= n` it is also at most the square of that power. -/
theorem le_powTwoFloor_sq_of_two_mul_le {a n : ℕ}
    (_hn : 2 ≤ n) (h : 2 * a ≤ n) :
    a ≤ (powTwoFloor n) ^ 2 := by
  have hle : a ≤ powTwoFloor n := le_powTwoFloor_of_two_mul_le h
  exact le_trans hle
    (Nat.le_self_pow (a := powTwoFloor n) (by decide : (2 : ℕ) ≠ 0))

/-- A sharper square-form rounding lemma.  Since `n <= 2 * powTwoFloor n`,
the hypothesis `4 * a <= n^2` implies `a <= powTwoFloor n^2`.  This is the
form needed to keep the crossbar scale linear in the target grid order. -/
theorem le_powTwoFloor_sq_of_four_mul_le_sq {a n : ℕ}
    (h : 4 * a ≤ n ^ 2) :
    a ≤ (powTwoFloor n) ^ 2 := by
  have hn_sq : n ^ 2 ≤ (2 * powTwoFloor n) ^ 2 :=
    Nat.pow_le_pow_left (self_le_two_mul_powTwoFloor (n := n)) 2
  have hfour_floor :
      (2 * powTwoFloor n) ^ 2 = 4 * (powTwoFloor n) ^ 2 := by
    rw [mul_pow]
    rfl
  have hscaled : 4 * a ≤ 4 * (powTwoFloor n) ^ 2 := by
    exact le_trans h (by simpa [hfour_floor] using hn_sq)
  exact Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < 4)

end GridMinorArithmetic
end SimpleGraph

end Lax17Proofs
