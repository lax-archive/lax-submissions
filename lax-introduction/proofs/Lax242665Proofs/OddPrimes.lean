import Mathlib.Algebra.Ring.Parity
import Lax242665.OddPrimes

namespace Lax242665Proofs.OddPrimes

/--
---
conclusion: Lax242665.OddPrimes.odd_of_prime
---
An even prime is divisible by `2`, so `2` is `1` or the prime itself.
-/
theorem odd_of_prime (p : ℕ) (hp : Lax242665.Primes.Prime p) (h2 : p ≠ 2) : Odd p := by
  obtain ⟨hp1, hdiv⟩ := hp
  rw [Nat.odd_iff]
  by_contra h
  have h2p : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
  rcases hdiv 2 h2p with h | h
  · omega
  · exact h2 h.symm

end Lax242665Proofs.OddPrimes
