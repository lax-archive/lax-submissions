import Lax17Proofs.Source.Exponent8.GlobalDichotomy

namespace Lax17Proofs

/-!
# Closed numerical endpoint for the exponent-eight-and-a-half experiment

This file chooses the remaining parameters in
`containsGridMinor_of_treewidth_parameters85`.  The resulting treewidth
threshold is

`K * target^8 * (sqrt(target) + 1) * (log₂ target)^b`.

The harmless `+ 1` makes the natural-number square-root estimate uniform.
For `target >= 2` this is at most a constant multiple of
`target^(8 + 1/2) * polylog(target)`.
-/

namespace SimpleGraph
namespace Exponent8

universe u

/-- The isolated exponent-eight-and-a-half treewidth threshold. -/
def polynomialGridMinorTreewidthBound85
    (K b target : ℕ) : ℕ :=
  K * target ^ 8 * (Nat.sqrt target + 1) *
    (Nat.log 2 target) ^ b

/-- Exact `target^8 * sqrt(target) * polylog(target)` form. -/
def polynomialGridMinorTreewidthBoundEightAndHalf
    (K b target : ℕ) : ℕ :=
  K * target ^ 8 * Nat.sqrt target *
    (Nat.log 2 target) ^ b

/-- The canonical hairy-system width at an unrounded crossbar scale. -/
def widthScale85 (n : ℕ) : ℕ :=
  max 2
    (max ((GridMinorArithmetic.powTwoFloor n) ^ 2)
      (exponentEightLocalThreshold e8Constant 1
        (GridMinorArithmetic.powTwoFloor n)))

theorem widthScale85_gt_one (n : ℕ) :
    1 < widthScale85 n :=
  lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 _)

theorem widthScale85_grid_width (n : ℕ) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ widthScale85 n :=
  le_trans (le_max_left _ _) (le_max_right 2 _)

theorem widthScale85_crossbar_width (n : ℕ) :
    exponentEightLocalThreshold e8Constant 1
        (GridMinorArithmetic.powTwoFloor n) ≤
      widthScale85 n :=
  le_trans (le_max_right _ _) (le_max_right 2 _)

/-- The rounded local threshold is bounded by the same expression at the
unrounded scale. -/
theorem rounded_exponentEightLocalThreshold_le
    {n : ℕ} (hn : 2 ≤ n) :
    exponentEightLocalThreshold e8Constant 1
        (GridMinorArithmetic.powTwoFloor n) ≤
      exponentEightLocalThreshold e8Constant 1 n := by
  have hfloor :
      GridMinorArithmetic.powTwoFloor n ≤ n :=
    GridMinorArithmetic.powTwoFloor_le_self hn
  simp only [exponentEightLocalThreshold, pow_one]
  gcongr

theorem two_le_exponentEightLocalThreshold
    {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ exponentEightLocalThreshold e8Constant 1 n := by
  have hnpos : 0 < n := by omega
  have hsqrt : 1 ≤ Nat.sqrt n :=
    ThreeRoundParameters.e8_sqrt_pos hn
  have hlog : 1 ≤ Nat.log 2 n + 1 := by omega
  calc
    2 ≤ e8Constant := by norm_num [e8Constant]
    _ = e8Constant * 1 * 1 * 1 := by simp
    _ ≤ e8Constant * n ^ 8 * Nat.sqrt n *
          (Nat.log 2 n + 1) := by
      gcongr
      exact Nat.succ_le_of_lt (Nat.pow_pos hnpos)
    _ = exponentEightLocalThreshold e8Constant 1 n := by
      simp [exponentEightLocalThreshold]

theorem square_le_exponentEightLocalThreshold
    {n : ℕ} (hn : 2 ≤ n) :
    n ^ 2 ≤ exponentEightLocalThreshold e8Constant 1 n := by
  have hnpos : 0 < n := by omega
  have hsqrt : 1 ≤ Nat.sqrt n :=
    ThreeRoundParameters.e8_sqrt_pos hn
  have hlog : 1 ≤ Nat.log 2 n + 1 := by omega
  have hp : n ^ 2 ≤ n ^ 8 :=
    Nat.pow_le_pow_right hnpos (by omega)
  calc
    n ^ 2 ≤ n ^ 8 := hp
    _ = 1 * n ^ 8 * 1 * 1 := by simp
    _ ≤ e8Constant * n ^ 8 * Nat.sqrt n *
          (Nat.log 2 n + 1) := by
      gcongr
      norm_num [e8Constant]
    _ = exponentEightLocalThreshold e8Constant 1 n := by
      simp [exponentEightLocalThreshold]

/-- `widthScale85` has the unrounded `n^8 sqrt(n) log(n)` upper bound. -/
theorem widthScale85_le_unrounded
    {n : ℕ} (hn : 2 ≤ n) :
    widthScale85 n ≤
      exponentEightLocalThreshold e8Constant 1 n := by
  rw [widthScale85]
  apply max_le
  · exact two_le_exponentEightLocalThreshold hn
  · apply max_le
    · exact le_trans
        (GridMinorArithmetic.pow_powTwoFloor_le_pow
          (m := 2) hn)
        (square_le_exponentEightLocalThreshold hn)
    · exact rounded_exponentEightLocalThreshold_le hn

/-- Constant factor in the normalized hairy-system size estimate. -/
def exponent85HairyConstant (cHair cGrid : ℕ) : ℕ :=
  cHair * e8Constant * (max 2 cGrid) ^ 50

set_option maxHeartbeats 800000 in
/-- The exact hairy-system size is bounded without losing the square-root
factor in the crossbar scale. -/
theorem hairy_size85_le_normalized
    (cHair cHairLog cGrid k n : ℕ) (hn : 2 ≤ n) :
    cHair * widthScale85 n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      exponent85HairyConstant cHair cGrid *
        n ^ 8 * (Nat.sqrt n + 1) *
        (Nat.log 2 n + 1) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw :
      widthScale85 n ≤
        e8Constant * n ^ 8 * Nat.sqrt n *
          (Nat.log 2 n + 1) := by
    simpa [exponentEightLocalThreshold] using
      widthScale85_le_unrounded hn
  have hell :
      PolynomialGridMinor.lengthScale cGrid n ≤
        max 2 cGrid * (Nat.log 2 n + 1) := by
    calc
      PolynomialGridMinor.lengthScale cGrid n ≤
          PolynomialGridMinor.coarseLengthScale cGrid n :=
        PolynomialGridMinor.lengthScale_le_unrounded cGrid n hn
      _ ≤ max 2 cGrid * Nat.log 2 n :=
        PolynomialGridMinor.coarseLengthScale_le_logarithmic cGrid hn
      _ ≤ max 2 cGrid * (Nat.log 2 n + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hsqrt : Nat.sqrt n ≤ Nat.sqrt n + 1 := Nat.le_add_right _ _
  calc
    cHair * widthScale85 n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog
        ≤
      cHair *
          (e8Constant * n ^ 8 * Nat.sqrt n *
            (Nat.log 2 n + 1)) *
        (max 2 cGrid * (Nat.log 2 n + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
          gcongr
    _ ≤
      cHair *
          (e8Constant * n ^ 8 * (Nat.sqrt n + 1) *
            (Nat.log 2 n + 1)) *
        (max 2 cGrid * (Nat.log 2 n + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
          gcongr
    _ =
      exponent85HairyConstant cHair cGrid *
        n ^ 8 * (Nat.sqrt n + 1) *
        (Nat.log 2 n + 1) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
      rw [mul_pow]
      have hpow :
          (Nat.log 2 n + 1) * (Nat.log 2 n + 1) ^ 50 =
            (Nat.log 2 n + 1) ^ 51 := by
        rw [show (51 : ℕ) = 1 + 50 by decide, pow_add, pow_one]
      calc
        cHair *
              (e8Constant * n ^ 8 * (Nat.sqrt n + 1) *
                (Nat.log 2 n + 1)) *
            ((max 2 cGrid) ^ 50 * (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog
            =
          (cHair * e8Constant * (max 2 cGrid) ^ 50) *
            n ^ 8 * (Nat.sqrt n + 1) *
            ((Nat.log 2 n + 1) *
              (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog := by ring
        _ =
          exponent85HairyConstant cHair cGrid *
            n ^ 8 * (Nat.sqrt n + 1) *
            (Nat.log 2 n + 1) ^ 51 *
            (Nat.log 2 k) ^ cHairLog := by
          rw [hpow, exponent85HairyConstant]

/-- A log-product scale preserves the target square root, at the price of one
additional copy of its logarithmic factor. -/
theorem sqrt_logProductScale_add_one_le
    {C p target : ℕ} (hC : 1 ≤ C) (htarget : 2 ≤ target) :
    Nat.sqrt (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (C + 1) * (Nat.sqrt target + 1) *
        (Nat.log 2 target) ^ p := by
  let L := Nat.log 2 target
  let LP := L ^ p
  let S := Nat.sqrt target + 1
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLP : 1 ≤ LP :=
    Nat.succ_le_of_lt (Nat.pow_pos hLpos)
  have hS : 1 ≤ S := by simp [S]
  have hC_sq : C ≤ C * C := by
    calc
      C = C * 1 := by simp
      _ ≤ C * C := Nat.mul_le_mul_left C hC
  have ht_sq : target ≤ S * S := by
    simpa [S, Nat.pow_two] using
      Nat.le_of_lt (Nat.lt_succ_sqrt' target)
  have hLP_sq : LP ≤ LP * LP := by
    calc
      LP = LP * 1 := by simp
      _ ≤ LP * LP := Nat.mul_le_mul_left LP hLP
  have hscale_sq :
      PolynomialGridMinor.logProductScale C p target ≤
        (C * S * LP) * (C * S * LP) := by
    calc
      PolynomialGridMinor.logProductScale C p target =
          C * target * LP := by
        simp [PolynomialGridMinor.logProductScale, L, LP]
      _ ≤ (C * C) * (S * S) * (LP * LP) := by
        gcongr
      _ = (C * S * LP) * (C * S * LP) := by
        ac_rfl
  have hsqrt :
      Nat.sqrt (PolynomialGridMinor.logProductScale C p target) ≤
        C * S * LP := by
    calc
      Nat.sqrt (PolynomialGridMinor.logProductScale C p target) ≤
          Nat.sqrt ((C * S * LP) * (C * S * LP)) :=
        Nat.sqrt_le_sqrt hscale_sq
      _ = C * S * LP := Nat.sqrt_eq _
  calc
    Nat.sqrt (PolynomialGridMinor.logProductScale C p target) + 1
        ≤ C * S * LP + 1 := Nat.add_le_add_right hsqrt 1
    _ ≤ C * S * LP + S * LP := by
      exact Nat.add_le_add_left (by
        simpa using Nat.mul_le_mul hS hLP) _
    _ = (C + 1) * S * LP := by ring
    _ = (C + 1) * (Nat.sqrt target + 1) *
          (Nat.log 2 target) ^ p := by
      simp [S, LP, L]

theorem log_logProductScale_add_one_le
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (Nat.clog 2 C + p + 2 + 1) * Nat.log 2 target := by
  let L := Nat.log 2 target
  have hL : 1 ≤ L := by
    exact Nat.succ_le_of_lt
      (by
        simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget)
  calc
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1
        ≤ (Nat.clog 2 C + p + 2) * L + 1 :=
      Nat.add_le_add_right
        (by
          simpa [L] using
            PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
              C p htarget)
        1
    _ ≤ (Nat.clog 2 C + p + 2) * L + L := by
      gcongr
    _ = (Nat.clog 2 C + p + 2 + 1) * L := by
      ring
    _ = (Nat.clog 2 C + p + 2 + 1) *
          Nat.log 2 target := by rfl

theorem polynomialGridMinorTreewidthBound85_le_monomial
    {K b target : ℕ} (htarget : 2 ≤ target) :
    polynomialGridMinorTreewidthBound85 K b target ≤
      PolynomialGridMinor.monomialLogScale K 9 b target := by
  have hsqrt : Nat.sqrt target + 1 ≤ target :=
    Nat.succ_le_of_lt (Nat.sqrt_lt_self (by omega))
  simp only [polynomialGridMinorTreewidthBound85,
    PolynomialGridMinor.monomialLogScale]
  calc
    K * target ^ 8 * (Nat.sqrt target + 1) *
        (Nat.log 2 target) ^ b
        ≤ K * target ^ 8 * target *
          (Nat.log 2 target) ^ b := by
      gcongr
    _ = K * target ^ 9 * (Nat.log 2 target) ^ b := by
      rw [show (9 : ℕ) = 8 + 1 by decide, pow_add, pow_one]
      ac_rfl

theorem log_polynomialGridMinorTreewidthBound85_le
    (K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (polynomialGridMinorTreewidthBound85 K b target) ≤
      (Nat.clog 2 K + 2 * 9 + b) * Nat.log 2 target := by
  exact le_trans
    (Nat.log_mono_right
      (polynomialGridMinorTreewidthBound85_le_monomial htarget))
    (PolynomialGridMinor.log_monomialLogScale_le_clog_const_mul_log
      K 9 b htarget)

theorem polynomialGridMinorTreewidthBound85_gt_one
    {K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBound85 K b target := by
  have htarget_pos : 0 < target := by omega
  have hlog_pos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have htwo : 2 ≤ target ^ 8 := by
    calc
      2 ≤ 2 ^ 8 := by decide
      _ ≤ target ^ 8 := Nat.pow_le_pow_left htarget 8
  have hsqrt : 1 ≤ Nat.sqrt target + 1 := by omega
  have hlog : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog_pos)
  have :
      2 ≤ K * target ^ 8 * (Nat.sqrt target + 1) *
        (Nat.log 2 target) ^ b := by
    calc
      2 = 1 * 2 * 1 * 1 := by norm_num
      _ ≤ K * target ^ 8 * (Nat.sqrt target + 1) *
          (Nat.log 2 target) ^ b := by
        gcongr
  exact lt_of_lt_of_le (by decide : 1 < 2) (by
    simpa [polynomialGridMinorTreewidthBound85] using this)

/-- For nontrivial targets, doubling the coefficient absorbs the auxiliary
`+ 1` used in the natural-number square-root estimate. -/
theorem polynomialGridMinorTreewidthBound85_le_eightAndHalf
    (K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    polynomialGridMinorTreewidthBound85 K b target ≤
      polynomialGridMinorTreewidthBoundEightAndHalf (2 * K) b target := by
  have hsqrt_one : 1 ≤ Nat.sqrt target :=
    ThreeRoundParameters.e8_sqrt_pos htarget
  have hsqrt : Nat.sqrt target + 1 ≤ 2 * Nat.sqrt target := by
    omega
  simp only [polynomialGridMinorTreewidthBound85,
    polynomialGridMinorTreewidthBoundEightAndHalf]
  calc
    K * target ^ 8 * (Nat.sqrt target + 1) *
        (Nat.log 2 target) ^ b
        ≤ K * target ^ 8 * (2 * Nat.sqrt target) *
          (Nat.log 2 target) ^ b := by
      gcongr
    _ = (2 * K) * target ^ 8 * Nat.sqrt target *
          (Nat.log 2 target) ^ b := by ring

/-- Coefficient and exponent budgets imply the normalized hairy inequality at
the exponent-eight-and-a-half threshold. -/
theorem hairy_large_threshold85_of_coeff
    {cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 9 + 51 + cHairLog ≤ b)
    (hcoeff :
      exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
        Dn ^ 51 * Dk ^ cHairLog < K) :
    exponent85HairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        ((C + 1) * (Nat.sqrt target + 1) *
          (Nat.log 2 target) ^ p) *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog <
      polynomialGridMinorTreewidthBound85 K b target := by
  let L := Nat.log 2 target
  let S := Nat.sqrt target + 1
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htpos : 0 < target := by omega
  have hmult_pos :
      0 < target ^ 8 * S * L ^ b := by
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos htpos) (by simp [S]))
      (Nat.pow_pos hLpos)
  have hLp8 :
      (L ^ p) ^ 8 = L ^ (p * 8) := by
    simpa using (Nat.pow_mul L p 8).symm
  have hleft_eq :
      exponent85HairyConstant cHair cGrid *
          (PolynomialGridMinor.logProductScale C p target) ^ 8 *
          ((C + 1) * S * L ^ p) *
          (Dn * L) ^ 51 *
          (Dk * L) ^ cHairLog =
        (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
          Dn ^ 51 * Dk ^ cHairLog) *
          target ^ 8 * S *
          L ^ (p * 9 + 51 + cHairLog) := by
    calc
      exponent85HairyConstant cHair cGrid *
          (PolynomialGridMinor.logProductScale C p target) ^ 8 *
          ((C + 1) * S * L ^ p) *
          (Dn * L) ^ 51 *
          (Dk * L) ^ cHairLog
          =
        exponent85HairyConstant cHair cGrid *
          (C ^ 8 * target ^ 8 * (L ^ p) ^ 8) *
          ((C + 1) * S * L ^ p) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
            rw [PolynomialGridMinor.logProductScale]
            repeat rw [mul_pow]
      _ =
        exponent85HairyConstant cHair cGrid *
          (C ^ 8 * target ^ 8 * L ^ (p * 8)) *
          ((C + 1) * S * L ^ p) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
            rw [hLp8]
      _ =
        (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
          Dn ^ 51 * Dk ^ cHairLog) *
          target ^ 8 * S *
          (L ^ (p * 8) * L ^ p * L ^ 51 * L ^ cHairLog) := by
            ac_rfl
      _ =
        (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
          Dn ^ 51 * Dk ^ cHairLog) *
          target ^ 8 * S *
          L ^ (p * 9 + 51 + cHairLog) := by
            have hp : p * 8 + p = p * 9 := by omega
            rw [← pow_add, hp, ← pow_add, ← pow_add]
  have hpow :
      L ^ (p * 9 + 51 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    exponent85HairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        ((C + 1) * (Nat.sqrt target + 1) *
          (Nat.log 2 target) ^ p) *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog
        =
      (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
        Dn ^ 51 * Dk ^ cHairLog) *
        target ^ 8 * S *
        L ^ (p * 9 + 51 + cHairLog) := by
          simpa [L, S] using hleft_eq
    _ ≤
      (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
        Dn ^ 51 * Dk ^ cHairLog) *
        target ^ 8 * S * L ^ b := by
          gcongr
    _ < K * target ^ 8 * S * L ^ b := by
      calc
        (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
          Dn ^ 51 * Dk ^ cHairLog) *
            target ^ 8 * S * L ^ b
            =
          (exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
            Dn ^ 51 * Dk ^ cHairLog) *
            (target ^ 8 * S * L ^ b) := by ac_rfl
        _ < K * (target ^ 8 * S * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmult_pos
        _ = K * target ^ 8 * S * L ^ b := by ac_rfl
    _ = polynomialGridMinorTreewidthBound85 K b target := by
      simp [polynomialGridMinorTreewidthBound85, L, S]

/-- Numerical package consumed by the graph-theoretic exponent-eight-and-a-half
parameter theorem. -/
structure ParameterChoice85
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  ell : ℕ
  w : ℕ
  k : ℕ
  g : ℕ
  r : ℕ
  ell_gt_one : 1 < ell
  w_gt_one : 1 < w
  k_gt_one : 1 < k
  k_le_treewidth : k ≤ tw
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  g_ge_two : 2 ≤ g
  r_ge_two : 2 ≤ r
  g_powerOfTwo : CrossbarContract.IsPowerOfTwo g
  grid_length : cGrid * Nat.log 2 g ≤ ell
  grid_width : g ^ 2 ≤ w
  crossbar_width :
    exponentEightLocalThreshold e8Constant 1 g ≤ w
  strong_scale : cCross * r ^ 2 ≤ g ^ 2
  target_direct : cGrid * target * (Nat.log 2 g) ^ 2 ≤ g
  target_strong : cStrong * target ≤ r

/-- Target-independent coefficient package for the closed endpoint. -/
structure PolynomialThresholdTemplate85
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  K : ℕ
  b : ℕ
  C : ℕ
  p : ℕ
  K_pos : 0 < K
  b_pos : 0 < b
  C_pos : 1 ≤ C
  p_ge_two : 2 ≤ p
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  hairy_exponent : p * 9 + 51 + cHairLog ≤ b
  hairy_coeff :
    exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
      (Nat.clog 2 C + p + 2 + 1) ^ 51 *
      (Nat.clog 2 K + 2 * 9 + b) ^ cHairLog < K

namespace PolynomialThresholdTemplate85

/-- A coefficient template gives the exact parameters at every target. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (T : PolynomialThresholdTemplate85
      cHair cHairLog cCross cGrid cStrong)
    (target : ℕ) (htarget : 2 ≤ target) :
    ParameterChoice85 cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound85 T.K T.b target) := by
  let n := PolynomialGridMinor.logProductScale T.C T.p target
  let k := polynomialGridMinorTreewidthBound85 T.K T.b target
  let Dn := Nat.clog 2 T.C + T.p + 2
  let Dk := Nat.clog 2 T.K + 2 * 9 + T.b
  refine
    { ell := PolynomialGridMinor.lengthScale cGrid n
      w := widthScale85 n
      k := k
      g := GridMinorArithmetic.powTwoFloor n
      r := PolynomialGridMinor.strongScale cStrong target
      ell_gt_one := PolynomialGridMinor.lengthScale_gt_one cGrid n
      w_gt_one := widthScale85_gt_one n
      k_gt_one := ?_
      k_le_treewidth := le_rfl
      hairy_large := ?_
      g_ge_two := ?_
      r_ge_two := PolynomialGridMinor.strongScale_ge_two cStrong target
      g_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor n
      grid_length := PolynomialGridMinor.lengthScale_grid_length cGrid n
      grid_width := widthScale85_grid_width n
      crossbar_width := widthScale85_crossbar_width n
      strong_scale := ?_
      target_direct := ?_
      target_strong :=
        PolynomialGridMinor.target_le_strongScale cStrong target }
  · exact polynomialGridMinorTreewidthBound85_gt_one
      (Nat.succ_le_of_lt T.K_pos) htarget
  · have hn : 2 ≤ n :=
      PolynomialGridMinor.two_le_logProductScale T.C_pos htarget
    apply lt_of_le_of_lt
      (hairy_size85_le_normalized cHair cHairLog cGrid k n hn)
    have hsqrt :
        Nat.sqrt n + 1 ≤
          (T.C + 1) * (Nat.sqrt target + 1) *
            (Nat.log 2 target) ^ T.p := by
      simpa [n] using sqrt_logProductScale_add_one_le T.C_pos htarget
    have hlogn :
        Nat.log 2 n + 1 ≤
          (Dn + 1) * Nat.log 2 target := by
      simpa [n, Dn, Nat.add_assoc] using
        log_logProductScale_add_one_le T.C T.p htarget
    have hlogk :
        Nat.log 2 k ≤ Dk * Nat.log 2 target := by
      simpa [k, Dk] using
        log_polynomialGridMinorTreewidthBound85_le T.K T.b htarget
    have hthreshold :
        exponent85HairyConstant cHair cGrid *
            n ^ 8 *
            ((T.C + 1) * (Nat.sqrt target + 1) *
              (Nat.log 2 target) ^ T.p) *
            ((Dn + 1) * Nat.log 2 target) ^ 51 *
            (Dk * Nat.log 2 target) ^ cHairLog <
          k := by
      simpa [n, k, Dn, Dk, Nat.add_assoc] using
        hairy_large_threshold85_of_coeff htarget T.hairy_exponent
          T.hairy_coeff
    exact lt_of_le_of_lt (by gcongr) hthreshold
  · exact GridMinorArithmetic.two_le_powTwoFloor
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · apply GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
    simpa [n] using
      PolynomialGridMinor.strong_scale_logProduct_sq_of_coeff
        htarget T.strong_coeff
  · have hlog_n :
        Nat.log 2 n ≤ Dn * Nat.log 2 target := by
      simpa [n, Dn] using
        PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
          T.C T.p htarget
    have hlog_sq :
        (Nat.log 2 n) ^ 2 ≤
          (Dn * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left hlog_n 2
    apply GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
    calc
      2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤
          2 * (cGrid * target *
            (Dn * Nat.log 2 target) ^ 2) := by
        gcongr
      _ ≤ n := by
        simpa [n, Dn] using
          PolynomialGridMinor.target_direct_logProduct_of_coeff
            htarget T.p_ge_two T.direct_coeff

/-- Canonical, target-independent constants satisfying every coefficient
budget. -/
def canonical
    (cHair cHairLog cCross cGrid cStrong : ℕ) :
    PolynomialThresholdTemplate85 cHair cHairLog cCross cGrid cStrong := by
  let C := PolynomialGridMinor.crossbarCoefficient cCross cGrid cStrong
  let b := 2 * 9 + 51 + cHairLog
  let A :=
    exponent85HairyConstant cHair cGrid * C ^ 8 * (C + 1) *
      (Nat.clog 2 C + 2 + 2 + 1) ^ 51
  let E := 2 * 9 + b
  refine
    { K := PolynomialGridMinor.thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      K_pos := ?_
      b_pos := ?_
      C_pos := ?_
      p_ge_two := le_rfl
      strong_coeff := ?_
      direct_coeff := ?_
      hairy_exponent := ?_
      hairy_coeff := ?_ }
  · dsimp [PolynomialGridMinor.thresholdCoefficient]
    exact Nat.pow_pos (by decide : 0 < 2)
  · omega
  · dsimp [C, PolynomialGridMinor.crossbarCoefficient]
    exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
  · simpa [C] using
      PolynomialGridMinor.strong_coeff_crossbarCoefficient
        cCross cGrid cStrong
  · simpa [C] using
      PolynomialGridMinor.direct_coeff_crossbarCoefficient
        cCross cGrid cStrong
  · omega
  · simpa [A, E, Nat.add_assoc] using
      PolynomialGridMinor.coeff_mul_clog_thresholdCoefficient_add_pow_lt
        A cHairLog E

end PolynomialThresholdTemplate85

/-- Consume a bundled numerical choice with the fully proved graph theorem. -/
theorem containsGridMinor_of_parameterChoice85 :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice85 cHair cHairLog cCross cGrid cStrong
                target (treewidth G) →
                ContainsGridMinor G target := by
  rcases containsGridMinor_of_treewidth_parameters85 with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
    P.hairy_large P.g_ge_two P.r_ge_two P.g_powerOfTwo P.grid_length
    P.grid_width P.crossbar_width P.strong_scale P.target_direct
    P.target_strong

/-- Closed exponent-eight-and-a-half excluded-grid theorem.  This remains
isolated from the public degree-ten endpoint. -/
theorem polynomial_grid_minor_theorem85 :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound85 K b target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases containsGridMinor_of_parameterChoice85 with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  let T :=
    PolynomialThresholdTemplate85.canonical
      cHair cHairLog cCross cGrid cStrong
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P :=
    T.toParameterChoice target htarget
  exact hmain G target
    { P with
      k_le_treewidth := le_trans P.k_le_treewidth htw }

/-- Closed experimental excluded-grid theorem with the exact exponent
`8 + 1/2` in the displayed natural-number threshold. -/
theorem polynomial_grid_minor_theorem_exponentEightAndHalf :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBoundEightAndHalf
                K b target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases polynomial_grid_minor_theorem85 with
    ⟨K, b, hK, hb, hmain⟩
  refine ⟨2 * K, b, Nat.mul_pos (by decide) hK, hb, ?_⟩
  intro V _ _ G target htarget htw
  exact hmain G htarget
    (le_trans
      (polynomialGridMinorTreewidthBound85_le_eightAndHalf
        K b htarget)
      htw)

end Exponent8
end SimpleGraph

end Lax17Proofs
