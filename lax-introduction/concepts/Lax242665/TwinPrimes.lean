import Lax242665.Primes

/-!
---
title: The twin prime conjecture
type: conjecture
---
For every natural number $n$ there is a prime number $p > n$ such that
$p + 2$ is prime as well.
-/

namespace Lax242665.TwinPrimes

/-- Beyond every natural number `n` lies a prime `p` with `p + 2` prime as
well. -/
axiom exists_twin_prime_gt :
    ∀ n : ℕ, ∃ p : ℕ, Primes.Prime p ∧ Primes.Prime (p + 2) ∧ n < p

end Lax242665.TwinPrimes
