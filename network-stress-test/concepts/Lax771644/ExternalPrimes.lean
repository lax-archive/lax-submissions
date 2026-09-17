import Mathlib.Data.Nat.Notation
import Lax242665.Primes

/-!
---
title: Primality claims restated from lax-242665
type: theorem
---
Two statements phrased over the notion of primality of *An Introduction to
Lax* (`lax-242665`), each discharged by the corresponding statement of that
submission. They exist so that this submission's proof network contains external
nodes belonging to another archive record.

# Formalization notes

The statements are verbatim copies of `lax-242665`'s two claims, so each
proof is the foreign statement itself. Importing `Lax242665.Primes` in the
concept package also puts an external node into the concept DAG.
-/

namespace Lax771644.ExternalPrimes

/-- Every natural number greater than `1` has a prime divisor, in the sense of
`lax-242665`. -/
axiom e1_has_prime_divisor : ∀ n : ℕ, 1 < n → ∃ p : ℕ, Lax242665.Primes.Prime p ∧ p ∣ n

/-- Beyond every natural number lies a prime, in the sense of `lax-242665`. -/
axiom e2_has_larger_prime : ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p

end Lax771644.ExternalPrimes
