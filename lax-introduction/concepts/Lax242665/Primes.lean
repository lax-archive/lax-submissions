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

/-- `n` is prime: it is greater than 1, and every divisor `d` of `n` is
`1` or `n` itself. -/
def Prime (n : ℕ) : Prop :=
  1 < n ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n

end Lax242665.Primes
