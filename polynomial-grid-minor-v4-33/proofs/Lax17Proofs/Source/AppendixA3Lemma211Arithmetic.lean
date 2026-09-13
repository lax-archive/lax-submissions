import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Arithmetic core of Chuzhoy Lemma 2.11

This module isolates the common estimate in both cases of the minimum
balanced-cut bandwidth proof.  All quantities are natural and all ratios are
denominator-cleared.
-/

namespace SimpleGraph
namespace AppendixA3Lemma211

/-- If old well-linkedness pays for retained terminals using an internal cut
and one external edge family, and that external family is no larger than the
internal cut, then the new terminal side has bandwidth
`alphaNum / (2 * alphaDen + alphaNum)`. -/
theorem new_terminal_side_scaled_bound
    {alphaNum alphaDen retained newEndpoints internalCut externalCut
      newTerminalSide : ℕ}
    (hold :
      alphaNum * retained ≤
        alphaDen * (internalCut + externalCut))
    (hexternal : externalCut ≤ internalCut)
    (hendpoints : newEndpoints ≤ externalCut)
    (hnew : newTerminalSide ≤ retained + newEndpoints) :
    alphaNum * newTerminalSide ≤
      (2 * alphaDen + alphaNum) * internalCut := by
  calc
    alphaNum * newTerminalSide ≤
        alphaNum * (retained + newEndpoints) :=
      Nat.mul_le_mul_left alphaNum hnew
    _ = alphaNum * retained + alphaNum * newEndpoints := by ring
    _ ≤ alphaDen * (internalCut + externalCut) +
        alphaNum * externalCut :=
      Nat.add_le_add hold (Nat.mul_le_mul_left alphaNum hendpoints)
    _ = alphaDen * internalCut +
        (alphaDen + alphaNum) * externalCut := by ring
    _ ≤ alphaDen * internalCut +
        (alphaDen + alphaNum) * internalCut :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (alphaDen + alphaNum) hexternal) _
    _ = (2 * alphaDen + alphaNum) * internalCut := by ring

/-- Bounding either side of a partition suffices for the minimum-side
well-linkedness inequality. -/
theorem scaled_min_bound_of_left
    {alphaNum alphaDen left right internalCut : ℕ}
    (hleft :
      alphaNum * left ≤
        (2 * alphaDen + alphaNum) * internalCut) :
    alphaNum * min left right ≤
      (2 * alphaDen + alphaNum) * internalCut :=
  (Nat.mul_le_mul_left alphaNum (Nat.min_le_left left right)).trans hleft

/-- Symmetric minimum-side wrapper for a bound on the right side. -/
theorem scaled_min_bound_of_right
    {alphaNum alphaDen left right internalCut : ℕ}
    (hright :
      alphaNum * right ≤
        (2 * alphaDen + alphaNum) * internalCut) :
    alphaNum * min left right ≤
      (2 * alphaDen + alphaNum) * internalCut :=
  (Nat.mul_le_mul_left alphaNum (Nat.min_le_right left right)).trans hright

end AppendixA3Lemma211
end SimpleGraph

end Lax17Proofs
