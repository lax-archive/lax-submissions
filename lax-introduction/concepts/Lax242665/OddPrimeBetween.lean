import Mathlib.Algebra.Ring.Parity
import Lax242665.Primes

/-!
---
title: An odd prime between n and 2n
type: theorem
---
For every natural number $n \geq 2$ there is an odd prime number $p$ with
$n < p \leq 2n$.
-/

namespace Lax242665.OddPrimeBetween

/-- Between `n ≥ 2` and `2n` there is always an odd prime. -/
axiom exists_odd_prime_between (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, Primes.Prime p ∧ Odd p ∧ n < p ∧ p ≤ 2 * n

end Lax242665.OddPrimeBetween
