import Mathlib.Algebra.Ring.Parity
import Lax242665.Primes

/-!
---
title: Every prime other than 2 is odd
type: lemma
---
Every prime number $p \neq 2$ is odd.
-/

namespace Lax242665.OddPrimes

/-- A prime `p` other than `2` is odd. -/
axiom odd_of_prime : ∀ p : ℕ, Primes.Prime p → p ≠ 2 → Odd p

end Lax242665.OddPrimes
