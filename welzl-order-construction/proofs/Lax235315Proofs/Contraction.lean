import Lax235315
import Mathlib.Tactic

namespace Lax235315Proofs

/--
---
conclusion: Lax235315.ContractionRecurrence.size_after_rounds
---
The additive rounding error remains bounded by twice its per-round value
after any number of halvings.

# Proof strategy

Induct on the number of rounds. Monotonicity of natural division propagates
the inductive bound through the next halving; the exact quotient identity
for adding a multiple of two absorbs the new error term.

# Attribution

The induction and quotient calculation adapt the arithmetic argument in
`Lax195003Proofs.Iterations.ShrinkingRun.value_le`, specialized to the
single-sequence statement here.
-/
lemma size_after_rounds (a : ℕ → ℕ) (q : ℕ)
    (step : ∀ i, a (i + 1) ≤ a i / 2 + q) (i : ℕ) :
    a i ≤ a 0 / 2 ^ i + 2 * q := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc
        a (i + 1) ≤ a i / 2 + q := step i
        _ ≤ (a 0 / 2 ^ i + 2 * q) / 2 + q := by
          exact Nat.add_le_add_right (Nat.div_le_div_right ih) q
        _ = a 0 / 2 ^ (i + 1) + 2 * q := by
          rw [show 2 * q = q * 2 by omega]
          rw [Nat.add_mul_div_right (a 0 / 2 ^ i) q (by omega)]
          rw [Nat.div_div_eq_div_mul, pow_succ]
          omega

end Lax235315Proofs
