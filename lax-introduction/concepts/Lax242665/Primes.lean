import Mathlib.Data.Nat.Notation

/-!
---
title: Prime numbers
type: definition
---
A natural number greater than 1 is *prime* if it is divisible only by 1 and
by itself.
-/

namespace Lax242665.Primes

/-- `n` is prime: it is greater than 1, and its only divisors are 1 and `n`
itself. -/
def Prime (n : ℕ) : Prop :=
  1 < n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

end Lax242665.Primes
