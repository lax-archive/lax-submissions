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

/-- A prime other than `2` is odd. -/
axiom odd_of_prime (p : ℕ) (hp : Primes.Prime p) (h2 : p ≠ 2) : Odd p

end Lax242665.OddPrimes
