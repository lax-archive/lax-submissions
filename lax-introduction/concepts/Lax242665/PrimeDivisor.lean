import Lax242665.Primes

/-!
---
title: Every number greater than 1 has a prime divisor
type: lemma
---
Every natural number greater than $1$ has a prime divisor.
-/

namespace Lax242665.PrimeDivisor

/-- Every natural number `n > 1` has a prime divisor. -/
axiom exists_prime_dvd : ∀ n : ℕ, 1 < n → ∃ p : ℕ, Primes.Prime p ∧ p ∣ n

end Lax242665.PrimeDivisor
