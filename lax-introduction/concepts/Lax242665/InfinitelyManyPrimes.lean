import Lax242665.Primes

/-!
---
title: There are infinitely many primes
type: theorem
---
For every natural number $n$ there is a prime number $p > n$.
-/

namespace Lax242665.InfinitelyManyPrimes

/-- Beyond every natural number `n` lies a prime `p`. -/
axiom exists_prime_gt : ∀ n : ℕ, ∃ p : ℕ, Primes.Prime p ∧ n < p

end Lax242665.InfinitelyManyPrimes
