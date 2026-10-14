import Mathlib.Tactic

/-!
Arithmetic support for translating Lemma 18's rounded sampler parameter
into the crossing bound from Theorem 20.
-/

namespace Lax457868Proofs.ParameterBounds

/-- Lemma 18's sampler parameter, followed by the reconstruction's `2 * k`
contribution per round, gives the explicit displayed bound. -/
lemma refinedCrossingBound
    (C Lc Ln k : ℕ)
    (hk : k ≤ 768 * C * (64 * Lc + 1) * Lc + 1) :
    2 * k * Ln ≤
      2 * (768 * C * (64 * Lc + 1) * Lc + 1) * Ln := by
  calc
    2 * k * Ln = (2 * Ln) * k := by ring
    _ ≤ (2 * Ln) * (768 * C * (64 * Lc + 1) * Lc + 1) :=
      Nat.mul_le_mul_left (2 * Ln) hk
    _ = 2 * (768 * C * (64 * Lc + 1) * Lc + 1) * Ln := by ring

end Lax457868Proofs.ParameterBounds
