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

/-- For every `n ≥ 1` there is a prime `p` with `n < p ≤ 2n`. -/
axiom exists_prime_between :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Primes.Prime p ∧ n < p ∧ p ≤ 2 * n

end Lax242665.BertrandPostulate
