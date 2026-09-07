import Lax242665.OddPrimeBetween
import Lax242665.BertrandPostulate
import Lax242665.OddPrimes

namespace Lax242665Proofs.OddPrimeBetween

/--
---
conclusion: Lax242665.OddPrimeBetween.exists_odd_prime_between
assumptions:
  - Lax242665.BertrandPostulate.exists_prime_between
  - Lax242665.OddPrimes.odd_of_prime
---
Bertrand's postulate gives a prime `p` with `n < p ≤ 2n`. Since `n ≥ 2`, this
prime is not `2`, hence odd.
-/
theorem exists_odd_prime_between (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, Lax242665.Primes.Prime p ∧ Odd p ∧ n < p ∧ p ≤ 2 * n := by
  obtain ⟨p, hp, hnp, hp2n⟩ :=
    Lax242665.BertrandPostulate.exists_prime_between n (by omega)
  exact ⟨p, hp, Lax242665.OddPrimes.odd_of_prime p hp (by omega), hnp, hp2n⟩

end Lax242665Proofs.OddPrimeBetween
