import Lax17Proofs.Source.Exponent7.GlobalDichotomy
import Lax17Proofs.Source.GridMinorArithmetic

namespace Lax17Proofs

/-!
# Numerical bounds for the exponent-seven local threshold

The amortized controller has a row-independent number of initial slices. Its
complete local cost is bounded by

`2^37 * q^6 * ell * (log_2 q + 1)^3`.

At a rounded scale `q = powTwoFloor n` and requested length `ell = 2*g`, the
normalization

`2^38 * n^6 * g * (log_2 n + 1)^3`

suffices for the local theorem.
-/

namespace SimpleGraph
namespace Exponent7

/-- Convenient power-of-two coefficient for the exact local-cost estimate. -/
def exponentSevenLocalConstant : ℕ := 2 ^ 37

/-- Unrounded local width used in the global numerical endpoint. -/
def exponentSevenNormalizedLocalThreshold (n g : ℕ) : ℕ :=
  (2 ^ 38) * n ^ 6 * g * (Nat.log 2 n + 1) ^ 3

/-- The uniform initial slice count is cubic in the binary logarithm. -/
theorem exponentSevenUniformSlices_le
    (q ell : ℕ) :
    exponentSevenUniformSlices q ell ≤
      (2 ^ 26) * ell * (Nat.log 2 q + 1) ^ 3 := by
  let L := Nat.log 2 q + 1
  have hL : 1 ≤ L := by simp [L]
  have hdepth :
      exponentSevenUniformDepth q = 6 * L := by
    simp [exponentSevenUniformDepth, L]
  have hsucc : 6 * L + 1 ≤ 7 * L := by omega
  rw [exponentSevenUniformSlices, hdepth]
  calc
    (16 * (6 * L + 1) * (2048 * (6 * L))) *
          (32 * ell * L)
        ≤
      (16 * (7 * L) * (2048 * (6 * L))) *
          (32 * ell * L) := by
            gcongr
    _ = 44040192 * ell * L ^ 3 := by ring
    _ ≤ (2 ^ 26) * ell * L ^ 3 := by
      gcongr
      norm_num
    _ = (2 ^ 26) * ell *
          (Nat.log 2 q + 1) ^ 3 := by rfl

/-- Exact exponent-seven upper bound for the local pseudo-grid threshold. -/
theorem exponentSevenLocalThreshold_le
    {q ell : ℕ} (hell : 0 < ell) :
    exponentSevenLocalThreshold q ell ≤
      exponentSevenLocalConstant * q ^ 6 * ell *
        (Nat.log 2 q + 1) ^ 3 := by
  let M := exponentSevenUniformSlices q ell
  let L := Nat.log 2 q + 1
  have hMpos : 0 < M := by
    exact exponentSevenUniformSlices_pos hell
  have hM :
      M ≤ (2 ^ 26) * ell * L ^ 3 := by
    simpa [M, L] using exponentSevenUniformSlices_le q ell
  have hlinear : 2 * M + 1 ≤ 3 * M := by omega
  calc
    exponentSevenLocalThreshold q ell
        = 512 * q ^ 6 * (2 * M + 1) := by
          simp [exponentSevenLocalThreshold,
            exponentSevenLocalCost, M]
          ring
    _ ≤ 512 * q ^ 6 * (3 * M) := by
      gcongr
    _ ≤ 512 * q ^ 6 *
          (3 * ((2 ^ 26) * ell * L ^ 3)) := by
      gcongr
    _ ≤ (2 ^ 37) * q ^ 6 * ell * L ^ 3 := by
      have hcoeff : 512 * 3 * (2 ^ 26) ≤ 2 ^ 37 := by
        norm_num
      calc
        512 * q ^ 6 *
              (3 * ((2 ^ 26) * ell * L ^ 3))
            =
          (512 * 3 * (2 ^ 26)) * q ^ 6 * ell * L ^ 3 := by
            ring
        _ ≤ (2 ^ 37) * q ^ 6 * ell * L ^ 3 := by
          gcongr
    _ = exponentSevenLocalConstant * q ^ 6 * ell *
          (Nat.log 2 q + 1) ^ 3 := by
      simp [exponentSevenLocalConstant, L]

/-- Rounding the internal scale down to a power of two preserves the
normalized local-width bound. -/
theorem rounded_exponentSevenLocalThreshold_le
    {n g : ℕ} (hn : 2 ≤ n) (hg : 0 < g) :
    exponentSevenLocalThreshold
        (GridMinorArithmetic.powTwoFloor n) (2 * g) ≤
      exponentSevenNormalizedLocalThreshold n g := by
  let q := GridMinorArithmetic.powTwoFloor n
  have hq : q ≤ n :=
    GridMinorArithmetic.powTwoFloor_le_self hn
  have hlog :
      Nat.log 2 q + 1 ≤ Nat.log 2 n + 1 :=
    Nat.add_le_add_right
      (GridMinorArithmetic.log_powTwoFloor_le_log hn) 1
  calc
    exponentSevenLocalThreshold q (2 * g)
        ≤ exponentSevenLocalConstant * q ^ 6 * (2 * g) *
            (Nat.log 2 q + 1) ^ 3 :=
      exponentSevenLocalThreshold_le (by omega)
    _ ≤ exponentSevenLocalConstant * n ^ 6 * (2 * g) *
          (Nat.log 2 n + 1) ^ 3 := by
      gcongr
    _ = exponentSevenNormalizedLocalThreshold n g := by
      simp [exponentSevenLocalConstant,
        exponentSevenNormalizedLocalThreshold]
      ring

/-- The normalized width is nontrivial. -/
theorem exponentSevenNormalizedLocalThreshold_gt_one
    {n g : ℕ} (hn : 2 ≤ n) (hg : 2 ≤ g) :
    1 < exponentSevenNormalizedLocalThreshold n g := by
  have hn6 : 2 ≤ n ^ 6 := by
    calc
      2 ≤ 2 ^ 6 := by decide
      _ ≤ n ^ 6 := Nat.pow_le_pow_left hn 6
  have hlog : 1 ≤ (Nat.log 2 n + 1) ^ 3 :=
    Nat.one_le_pow 3 _ (by omega)
  have :
      2 ≤ (2 ^ 38) * n ^ 6 * g *
          (Nat.log 2 n + 1) ^ 3 := by
    calc
      2 = 1 * 2 * 1 * 1 := by norm_num
      _ ≤ (2 ^ 38) * n ^ 6 * g *
          (Nat.log 2 n + 1) ^ 3 := by
        gcongr <;> omega
  simpa [exponentSevenNormalizedLocalThreshold] using this

/-- The normalized local threshold also dominates the rounded crossbar
width. -/
theorem powTwoFloor_sq_le_normalizedLocalThreshold
    {n g : ℕ} (hn : 2 ≤ n) (hg : 2 ≤ g) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤
      exponentSevenNormalizedLocalThreshold n g := by
  have hfloor :
      (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ n ^ 2 :=
    GridMinorArithmetic.pow_powTwoFloor_le_pow hn
  have hnPow : n ^ 2 ≤ n ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hrest :
      1 ≤ (2 ^ 38) * g * (Nat.log 2 n + 1) ^ 3 := by
    have : 0 < (2 ^ 38) * g * (Nat.log 2 n + 1) ^ 3 := by
      positivity
    omega
  calc
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ n ^ 2 := hfloor
    _ ≤ n ^ 6 := hnPow
    _ ≤ (2 ^ 38) * n ^ 6 * g *
          (Nat.log 2 n + 1) ^ 3 := by
      have := Nat.le_mul_of_pos_left (n ^ 6) hrest
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = exponentSevenNormalizedLocalThreshold n g := rfl

end Exponent7
end SimpleGraph

end Lax17Proofs
