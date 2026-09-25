import Mathlib.Data.Nat.Log

/-!
---
title: Geometric contraction with an additive rounding error
type: lemma
---
If the size after a round is at most half the preceding size plus q, then
after i rounds it is at most the initial size divided by 2^i, plus 2q.
This accommodates the ceiling in Algorithm 1's sample size, with q = c².

# Formalization notes

All divisions are natural-number divisions. This arithmetic statement is
separate from proving that the actual twin-partition rounds satisfy its
hypothesis. The later stopping proof must also use the algorithm's threshold
and handle input sizes zero and one.
-/

namespace Lax235315.ContractionRecurrence

/-- Iterated halving accumulates less than twice the per-round additive error. -/
axiom size_after_rounds (a : ℕ → ℕ) (q : ℕ)
    (step : ∀ i, a (i + 1) ≤ a i / 2 + q) (i : ℕ) :
    a i ≤ a 0 / 2 ^ i + 2 * q

end Lax235315.ContractionRecurrence
