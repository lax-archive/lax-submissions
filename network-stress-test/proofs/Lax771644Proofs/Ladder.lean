import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Lax771644.Foundations

/-!
Helpers shared by every proof of this submission. Neither declaration carries
frontmatter, so both are helpers the archive ignores.
-/

namespace Lax771644Proofs.Ladder

open Lax771644.Foundations

/-- Weakening: a number divisible by `2 ^ a` is divisible by `2 ^ b` whenever
`b ≤ a`. -/
theorem weaken (a b : ℕ) (h : b ≤ a) {n : ℕ} (hn : Stage a n) : Stage b n :=
  dvd_trans (pow_dvd_pow 2 h) hn

/-- Every descent down the ladder holds outright. -/
theorem descent (a b : ℕ) (h : b ≤ a) : Descent a b :=
  fun _ hn => weaken a b h hn

end Lax771644Proofs.Ladder
