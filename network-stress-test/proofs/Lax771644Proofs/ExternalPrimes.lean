import Lax771644.ExternalPrimes
import Lax242665.PrimeDivisor
import Lax242665.InfinitelyManyPrimes

/-!
Proofs for the concept `Lax771644.ExternalPrimes`. Each one is the corresponding
statement of `lax-242665` verbatim, which is the whole point: the proof network
of this submission then contains external nodes owned by another record.
-/

namespace Lax771644Proofs.ExternalPrimes

/--
---
conclusion: Lax771644.ExternalPrimes.e1_has_prime_divisor
assumptions:
  - Lax242665.PrimeDivisor.exists_prime_dvd
---
Restates the prime-divisor claim of *An Introduction to Lax*.

# Proof strategy

Apply `Lax242665.PrimeDivisor.exists_prime_dvd`; the two statements have the
same type.

# Attribution

The mathematics belongs to `lax-242665`; this submission only re-exports it so
that the benchmark drawing contains an external assumption node.
-/
theorem e1_has_prime_divisor :
    ∀ n : ℕ, 1 < n → ∃ p : ℕ, Lax242665.Primes.Prime p ∧ p ∣ n :=
  Lax242665.PrimeDivisor.exists_prime_dvd

/--
---
conclusion: Lax771644.ExternalPrimes.e2_has_larger_prime
assumptions:
  - Lax242665.InfinitelyManyPrimes.exists_prime_gt
---
Restates the infinitude-of-primes claim of *An Introduction to Lax*.

# Proof strategy

Apply `Lax242665.InfinitelyManyPrimes.exists_prime_gt`; the two statements have
the same type.

# Attribution

The mathematics belongs to `lax-242665`; this submission only re-exports it so
that the benchmark drawing contains an external assumption node.
-/
theorem e2_has_larger_prime :
    ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p :=
  Lax242665.InfinitelyManyPrimes.exists_prime_gt

end Lax771644Proofs.ExternalPrimes
