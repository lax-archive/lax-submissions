import Lax242665.Primes

/-!
---
title: Bertrand's postulate
type: lemma
---
For every natural number $n \geq 1$ there is a prime number $p$ with
$n < p \leq 2n$.
-/

namespace Lax242665.BertrandPostulate

/-- Between `n` and `2n` there is always a prime. -/
axiom exists_prime_between (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, Primes.Prime p ∧ n < p ∧ p ≤ 2 * n

end Lax242665.BertrandPostulate
