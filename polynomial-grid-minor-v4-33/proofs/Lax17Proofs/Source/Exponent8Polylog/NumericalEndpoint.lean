import Lax17Proofs.Source.Exponent8Polylog.GlobalDichotomy

namespace Lax17Proofs

/-!
# Exact exponent-eight numerical endpoint

The local threshold

$$
2^{37} q^8 (\log_2 q + 1)^3
$$

is propagated through the hairy Path-of-Sets and grid constructions. The final
theorem has the natural-number form

$$
K g^8 (\log_2 g)^b \leq \operatorname{tw}(G).
$$

The constants and logarithmic exponent are explicit.
-/

namespace SimpleGraph
namespace Exponent8Polylog

universe u

/-- Exact exponent-eight treewidth threshold. -/
def polynomialGridMinorTreewidthBound8
    (K b target : ℕ) : ℕ :=
  K * target ^ 8 * (Nat.log 2 target) ^ b

/-- Unrounded width that dominates both the rounded local threshold and the
rounded crossbar width. -/
def exponentEightPolylogNormalizedLocalThreshold (n : ℕ) : ℕ :=
  (2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3

/-- The rounded local threshold is bounded by the unrounded monomial. -/
theorem rounded_exponentEightPolylogLocalThreshold_le
    {n : ℕ} (hn : 2 ≤ n) :
    exponentEightPolylogLocalThreshold
        (GridMinorArithmetic.powTwoFloor n) ≤
      exponentEightPolylogNormalizedLocalThreshold n := by
  let q := GridMinorArithmetic.powTwoFloor n
  have hqpos : 0 < q := by
    have : 2 ≤ q := GridMinorArithmetic.two_le_powTwoFloor hn
    omega
  have hq : q ≤ n :=
    GridMinorArithmetic.powTwoFloor_le_self hn
  have hlog :
      Nat.log 2 q + 1 ≤ Nat.log 2 n + 1 :=
    Nat.add_le_add_right
      (GridMinorArithmetic.log_powTwoFloor_le_log hn) 1
  calc
    exponentEightPolylogLocalThreshold q ≤
        exponentEightPolylogLocalConstant * q ^ 8 *
          (Nat.log 2 q + 1) ^ 3 :=
      exponentEightPolylogLocalThreshold_le hqpos
    _ ≤ exponentEightPolylogLocalConstant * n ^ 8 *
          (Nat.log 2 n + 1) ^ 3 := by
      gcongr
    _ ≤ (2 ^ 38) * n ^ 8 *
          (Nat.log 2 n + 1) ^ 3 := by
      have hcoeff : exponentEightPolylogLocalConstant ≤ 2 ^ 38 := by
        norm_num [exponentEightPolylogLocalConstant]
      gcongr
    _ = exponentEightPolylogNormalizedLocalThreshold n := rfl

/-- The normalized width is nontrivial. -/
theorem exponentEightPolylogNormalizedLocalThreshold_gt_one
    {n : ℕ} (hn : 2 ≤ n) :
    1 < exponentEightPolylogNormalizedLocalThreshold n := by
  have hn8 : 2 ≤ n ^ 8 := by
    calc
      2 ≤ 2 ^ 8 := by decide
      _ ≤ n ^ 8 := Nat.pow_le_pow_left hn 8
  have hlog : 1 ≤ (Nat.log 2 n + 1) ^ 3 :=
    Nat.one_le_pow 3 _ (by omega)
  have :
      2 ≤ (2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3 := by
    calc
      2 = 1 * 2 * 1 := by norm_num
      _ ≤ (2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3 := by
        gcongr
        norm_num
  simpa [exponentEightPolylogNormalizedLocalThreshold] using this

/-- The normalized local width also dominates the rounded crossbar width. -/
theorem powTwoFloor_sq_le_exponentEightPolylogNormalizedLocalThreshold
    {n : ℕ} (hn : 2 ≤ n) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤
      exponentEightPolylogNormalizedLocalThreshold n := by
  have hfloor :
      (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ n ^ 2 :=
    GridMinorArithmetic.pow_powTwoFloor_le_pow hn
  have hnPow : n ^ 2 ≤ n ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hrest :
      1 ≤ (2 ^ 38) * (Nat.log 2 n + 1) ^ 3 := by
    have : 0 < (2 ^ 38) * (Nat.log 2 n + 1) ^ 3 := by
      positivity
    omega
  calc
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ n ^ 2 := hfloor
    _ ≤ n ^ 8 := hnPow
    _ ≤ (2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3 := by
      have := Nat.le_mul_of_pos_left (n ^ 8) hrest
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = exponentEightPolylogNormalizedLocalThreshold n := rfl

/-- Constant in the normalized hairy-system size estimate. -/
def exponentEightPolylogHairyConstant (cHair cGrid : ℕ) : ℕ :=
  cHair * (2 ^ 38) * (max 2 cGrid) ^ 50

/-- The normalized local width together with the standard hairy-system
length has polynomial part `n^8`. -/
theorem hairy_size8_le_normalized
    (cHair cHairLog cGrid k n : ℕ)
    (hn : 2 ≤ n) :
    cHair * exponentEightPolylogNormalizedLocalThreshold n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      exponentEightPolylogHairyConstant cHair cGrid *
        n ^ 8 * (Nat.log 2 n + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
  have hell :
      PolynomialGridMinor.lengthScale cGrid n ≤
        max 2 cGrid * (Nat.log 2 n + 1) := by
    calc
      PolynomialGridMinor.lengthScale cGrid n ≤
          PolynomialGridMinor.coarseLengthScale cGrid n :=
        PolynomialGridMinor.lengthScale_le_unrounded cGrid n hn
      _ ≤ max 2 cGrid * Nat.log 2 n :=
        PolynomialGridMinor.coarseLengthScale_le_logarithmic cGrid hn
      _ ≤ max 2 cGrid * (Nat.log 2 n + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  calc
    cHair * exponentEightPolylogNormalizedLocalThreshold n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog
        ≤
      cHair *
          ((2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3) *
        (max 2 cGrid * (Nat.log 2 n + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
          simp only [exponentEightPolylogNormalizedLocalThreshold]
          gcongr
    _ =
      exponentEightPolylogHairyConstant cHair cGrid *
        n ^ 8 * (Nat.log 2 n + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
      rw [mul_pow]
      have hpow :
          (Nat.log 2 n + 1) ^ 3 *
              (Nat.log 2 n + 1) ^ 50 =
            (Nat.log 2 n + 1) ^ 53 := by
        rw [← pow_add]
      simp only [exponentEightPolylogHairyConstant]
      calc
        cHair *
              ((2 ^ 38) * n ^ 8 * (Nat.log 2 n + 1) ^ 3) *
            ((max 2 cGrid) ^ 50 *
              (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog
            =
          (cHair * (2 ^ 38) * (max 2 cGrid) ^ 50) *
            n ^ 8 *
            ((Nat.log 2 n + 1) ^ 3 *
              (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog := by ring
        _ =
          (cHair * (2 ^ 38) * (max 2 cGrid) ^ 50) *
            n ^ 8 * (Nat.log 2 n + 1) ^ 53 *
            (Nat.log 2 k) ^ cHairLog := by rw [hpow]

/-- The logarithm of a log-product scale, including the additive one in the
local threshold. -/
theorem log_logProductScale_add_one_le8
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (Nat.clog 2 C + p + 3) * Nat.log 2 target := by
  let L := Nat.log 2 target
  have hL : 1 ≤ L := by
    exact Nat.succ_le_of_lt
      (by
        simpa [L] using
          Nat.log_pos (by decide : 1 < 2) htarget)
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
    _ = (Nat.clog 2 C + p + 3) * L := by ring
    _ = (Nat.clog 2 C + p + 3) * Nat.log 2 target := rfl

/-- The logarithm of the exponent-eight threshold is linear in the target
logarithm. -/
theorem log_polynomialGridMinorTreewidthBound8_le
    (K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (polynomialGridMinorTreewidthBound8 K b target) ≤
      (Nat.clog 2 K + 2 * 8 + b) * Nat.log 2 target := by
  change
    Nat.log 2 (PolynomialGridMinor.monomialLogScale K 8 b target) ≤ _
  exact
    PolynomialGridMinor.log_monomialLogScale_le_clog_const_mul_log
      K 8 b htarget

/-- The exponent-eight threshold is nontrivial. -/
theorem polynomialGridMinorTreewidthBound8_gt_one
    {K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBound8 K b target := by
  have hlogPos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlogPos)
  have ht8 : 2 ≤ target ^ 8 := by
    calc
      2 ≤ 2 ^ 8 := by decide
      _ ≤ target ^ 8 := Nat.pow_le_pow_left htarget 8
  have :
      2 ≤ K * target ^ 8 * (Nat.log 2 target) ^ b := by
    calc
      2 = 1 * 2 * 1 := by norm_num
      _ ≤ K * target ^ 8 * (Nat.log 2 target) ^ b := by
        gcongr
  simpa [polynomialGridMinorTreewidthBound8] using this

/-- Coefficient and exponent budgets imply the hairy-system inequality at
the exponent-eight threshold. -/
theorem hairy_large_threshold8_of_coeff
    {cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 8 + 53 + cHairLog ≤ b)
    (hcoeff :
      exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
        Dn ^ 53 * Dk ^ cHairLog < K) :
    exponentEightPolylogHairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        (Dn * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog <
      polynomialGridMinorTreewidthBound8 K b target := by
  let L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htpos : 0 < target := by omega
  have hmultPos : 0 < target ^ 8 * L ^ b :=
    Nat.mul_pos (Nat.pow_pos htpos) (Nat.pow_pos hLpos)
  have hLp8 : (L ^ p) ^ 8 = L ^ (p * 8) := by
    simpa using (Nat.pow_mul L p 8).symm
  have hLcombine :
      L ^ (p * 8) * L ^ 53 * L ^ cHairLog =
        L ^ (p * 8 + 53 + cHairLog) := by
    rw [← pow_add, ← pow_add]
  have hleft :
      exponentEightPolylogHairyConstant cHair cGrid *
          (PolynomialGridMinor.logProductScale C p target) ^ 8 *
          (Dn * L) ^ 53 * (Dk * L) ^ cHairLog =
        (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
            Dn ^ 53 * Dk ^ cHairLog) *
          target ^ 8 * L ^ (p * 8 + 53 + cHairLog) := by
    rw [PolynomialGridMinor.logProductScale]
    repeat rw [mul_pow]
    rw [hLp8]
    calc
      exponentEightPolylogHairyConstant cHair cGrid *
            (C ^ 8 * target ^ 8 * L ^ (p * 8)) *
            (Dn ^ 53 * L ^ 53) *
            (Dk ^ cHairLog * L ^ cHairLog)
          =
        (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
            Dn ^ 53 * Dk ^ cHairLog) * target ^ 8 *
          (L ^ (p * 8) * L ^ 53 * L ^ cHairLog) := by ring
      _ =
        (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
            Dn ^ 53 * Dk ^ cHairLog) * target ^ 8 *
          L ^ (p * 8 + 53 + cHairLog) := by rw [hLcombine]
  have hpow :
      L ^ (p * 8 + 53 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    exponentEightPolylogHairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        (Dn * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog
        =
      (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
          Dn ^ 53 * Dk ^ cHairLog) * target ^ 8 *
        L ^ (p * 8 + 53 + cHairLog) := by
          simpa [L] using hleft
    _ ≤
      (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
          Dn ^ 53 * Dk ^ cHairLog) * target ^ 8 * L ^ b := by
      gcongr
    _ < K * target ^ 8 * L ^ b := by
      calc
        (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
            Dn ^ 53 * Dk ^ cHairLog) * target ^ 8 * L ^ b
            =
          (exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
            Dn ^ 53 * Dk ^ cHairLog) * (target ^ 8 * L ^ b) := by
              ring
        _ < K * (target ^ 8 * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmultPos
        _ = K * target ^ 8 * L ^ b := by ring
    _ = polynomialGridMinorTreewidthBound8 K b target := by
      simp [polynomialGridMinorTreewidthBound8, L]

/-- Numerical parameters for the global graph theorem. -/
structure ParameterChoice8
    (cHair cHairLog cGrid cStrong target tw : ℕ) where
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
  target_ge_two : 2 ≤ target
  grid_length : cGrid * Nat.log 2 g ≤ ell
  grid_width : g ^ 2 ≤ w
  local_width : exponentEightPolylogLocalThreshold g ≤ w
  strong_scale : 20000 * r ^ 2 ≤ g ^ 2
  target_direct : cGrid * target * (Nat.log 2 g) ^ 2 ≤ g
  target_strong : cStrong * target ≤ r

/-- Target-independent coefficients for the exponent-eight endpoint. -/
structure PolynomialThresholdTemplate8
    (cHair cHairLog cGrid cStrong : ℕ) where
  K : ℕ
  b : ℕ
  C : ℕ
  p : ℕ
  K_pos : 0 < K
  b_pos : 0 < b
  C_pos : 1 ≤ C
  p_ge_two : 2 ≤ p
  strong_coeff :
    4 * 20000 * (max 2 cStrong) ^ 2 ≤ C ^ 2
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  hairy_exponent : p * 8 + 53 + cHairLog ≤ b
  hairy_coeff :
    exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
      (Nat.clog 2 C + p + 3) ^ 53 *
      (Nat.clog 2 K + 2 * 8 + b) ^ cHairLog < K

namespace PolynomialThresholdTemplate8

/-- A coefficient template gives all graph-theoretic parameters at every
target order. -/
def toParameterChoice
    {cHair cHairLog cGrid cStrong : ℕ}
    (T : PolynomialThresholdTemplate8 cHair cHairLog cGrid cStrong)
    (target : ℕ) (htarget : 2 ≤ target) :
    ParameterChoice8 cHair cHairLog cGrid cStrong target
      (polynomialGridMinorTreewidthBound8 T.K T.b target) := by
  let n := PolynomialGridMinor.logProductScale T.C T.p target
  let k := polynomialGridMinorTreewidthBound8 T.K T.b target
  let Dn := Nat.clog 2 T.C + T.p + 3
  let Dlog := Nat.clog 2 T.C + T.p + 2
  let Dk := Nat.clog 2 T.K + 2 * 8 + T.b
  refine
    { ell := PolynomialGridMinor.lengthScale cGrid n
      w := exponentEightPolylogNormalizedLocalThreshold n
      k := k
      g := GridMinorArithmetic.powTwoFloor n
      r := PolynomialGridMinor.strongScale cStrong target
      ell_gt_one := PolynomialGridMinor.lengthScale_gt_one cGrid n
      w_gt_one := ?_
      k_gt_one := ?_
      k_le_treewidth := le_rfl
      hairy_large := ?_
      g_ge_two := ?_
      r_ge_two := PolynomialGridMinor.strongScale_ge_two cStrong target
      g_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor n
      target_ge_two := htarget
      grid_length := PolynomialGridMinor.lengthScale_grid_length cGrid n
      grid_width := ?_
      local_width := ?_
      strong_scale := ?_
      target_direct := ?_
      target_strong :=
        PolynomialGridMinor.target_le_strongScale cStrong target }
  · exact exponentEightPolylogNormalizedLocalThreshold_gt_one
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · exact polynomialGridMinorTreewidthBound8_gt_one
      (Nat.succ_le_of_lt T.K_pos) htarget
  · have hn : 2 ≤ n :=
      PolynomialGridMinor.two_le_logProductScale T.C_pos htarget
    apply lt_of_le_of_lt
      (hairy_size8_le_normalized cHair cHairLog cGrid k n hn)
    have hlogn :
        Nat.log 2 n + 1 ≤ Dn * Nat.log 2 target := by
      simpa [n, Dn, Nat.add_assoc] using
        log_logProductScale_add_one_le8 T.C T.p htarget
    have hlogk :
        Nat.log 2 k ≤ Dk * Nat.log 2 target := by
      simpa [k, Dk] using
        log_polynomialGridMinorTreewidthBound8_le T.K T.b htarget
    have hthreshold :
        exponentEightPolylogHairyConstant cHair cGrid * n ^ 8 *
            (Dn * Nat.log 2 target) ^ 53 *
            (Dk * Nat.log 2 target) ^ cHairLog < k := by
      simpa [n, k, Dn, Dk, Nat.add_assoc] using
        hairy_large_threshold8_of_coeff
          htarget T.hairy_exponent T.hairy_coeff
    exact lt_of_le_of_lt (by gcongr) hthreshold
  · exact GridMinorArithmetic.two_le_powTwoFloor
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · exact
      powTwoFloor_sq_le_exponentEightPolylogNormalizedLocalThreshold
        (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · exact rounded_exponentEightPolylogLocalThreshold_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · apply GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
    simpa [n] using
      PolynomialGridMinor.strong_scale_logProduct_sq_of_coeff
        htarget T.strong_coeff
  · have hlogn :
        Nat.log 2 n ≤ Dlog * Nat.log 2 target := by
      simpa [n, Dlog] using
        PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
          T.C T.p htarget
    have hlogSq :
        (Nat.log 2 n) ^ 2 ≤
          (Dlog * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left hlogn 2
    apply GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
    calc
      2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤
          2 * (cGrid * target *
            (Dlog * Nat.log 2 target) ^ 2) := by
        gcongr
      _ ≤ n := by
        simpa [n, Dlog] using
          PolynomialGridMinor.target_direct_logProduct_of_coeff
            htarget T.p_ge_two T.direct_coeff

/-- Fixed constants satisfying every coefficient budget. -/
def canonical
    (cHair cHairLog cGrid cStrong : ℕ) :
    PolynomialThresholdTemplate8 cHair cHairLog cGrid cStrong := by
  let C :=
    PolynomialGridMinor.crossbarCoefficient 20000 cGrid cStrong
  let b := 2 * 8 + 53 + cHairLog
  let A :=
    exponentEightPolylogHairyConstant cHair cGrid * C ^ 8 *
      (Nat.clog 2 C + 2 + 3) ^ 53
  let E := 2 * 8 + b
  refine
    { K := PolynomialGridMinor.thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      K_pos := by
        dsimp [PolynomialGridMinor.thresholdCoefficient]
        positivity
      b_pos := by omega
      C_pos := by
        dsimp [C, PolynomialGridMinor.crossbarCoefficient]
        exact Nat.succ_le_of_lt (Nat.pow_pos (by norm_num))
      p_ge_two := le_rfl
      strong_coeff := ?_
      direct_coeff := ?_
      hairy_exponent := by omega
      hairy_coeff := ?_ }
  · simpa [C] using
      PolynomialGridMinor.strong_coeff_crossbarCoefficient
        20000 cGrid cStrong
  · simpa [C] using
      PolynomialGridMinor.direct_coeff_crossbarCoefficient
        20000 cGrid cStrong
  · simpa [A, E, Nat.add_assoc] using
      PolynomialGridMinor.coeff_mul_clog_thresholdCoefficient_add_pow_lt
        A cHairLog E

end PolynomialThresholdTemplate8

/-- Apply the graph theorem to a bundled numerical choice. -/
theorem containsGridMinor_of_parameterChoice8 :
    ∃ cHair cHairLog cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (target : ℕ),
          ParameterChoice8 cHair cHairLog cGrid cStrong
            target (treewidth G) →
            ContainsGridMinor G target := by
  rcases containsGridMinor_of_treewidth_parameters8 with
    ⟨cHair, cHairLog, cGrid, cStrong,
      hcHair, hcHairLog, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cGrid, cStrong,
    hcHair, hcHairLog, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one
    P.k_le_treewidth P.hairy_large P.g_ge_two P.r_ge_two
    P.g_powerOfTwo P.grid_length P.grid_width P.local_width
    P.strong_scale P.target_direct P.target_strong

/-- Excluded-grid theorem with polynomial exponent eight. -/
theorem polynomial_grid_minor_theorem_exponentEightPolylog :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound8 K b target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases containsGridMinor_of_parameterChoice8 with
    ⟨cHair, cHairLog, cGrid, cStrong,
      hcHair, hcHairLog, hcGrid, hcStrong, hmain⟩
  let T :=
    PolynomialThresholdTemplate8.canonical
      cHair cHairLog cGrid cStrong
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P := T.toParameterChoice target htarget
  exact hmain G target
    { P with
      k_le_treewidth := le_trans P.k_le_treewidth htw }

end Exponent8Polylog
end SimpleGraph

end Lax17Proofs
