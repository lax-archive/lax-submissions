import Mathlib.Tactic

/-!
Arithmetic support for translating the sampler's near-twin parameter into
the explicit natural-log crossing bound in the new concept.
-/

namespace Lax457868Proofs.ParameterBounds

/-- The refined sampler's parameter gives the claimed asymptotic crossing
bound after the reconstruction adds at most `2 * k` per round. -/
theorem refinedCrossingBound
    (C Lc Ln k : ℕ) (hC : 1 ≤ C) (hLc : 1 ≤ Lc) (hLn : 1 ≤ Ln)
    (hk : k ≤ 768 * C * (64 * Lc + 1) * Lc + 1) :
    2 * k * Ln ≤ 100000 * C * (Lc + 1) ^ 2 * (Ln + 1) := by
  have h64 : 64 * Lc + 1 ≤ 65 * Lc := by omega
  have hCL : 1 ≤ C * Lc ^ 2 := by nlinarith
  have hprod : Ln ≤ C * Lc ^ 2 * Ln := by
    calc
      Ln = 1 * Ln := by omega
      _ ≤ (C * Lc ^ 2) * Ln := Nat.mul_le_mul_right Ln hCL
  calc
    2 * k * Ln ≤ 2 * (768 * C * (64 * Lc + 1) * Lc + 1) * Ln := by
      gcongr
    _ ≤ 2 * (768 * C * (65 * Lc) * Lc + 1) * Ln := by
      gcongr
    _ = 99840 * C * Lc ^ 2 * Ln + 2 * Ln := by ring
    _ ≤ 99842 * C * Lc ^ 2 * Ln := by nlinarith [hprod]
    _ ≤ 100000 * C * Lc ^ 2 * Ln := by nlinarith
    _ ≤ 100000 * C * (Lc + 1) ^ 2 * (Ln + 1) := by
      gcongr <;> omega

end Lax457868Proofs.ParameterBounds
