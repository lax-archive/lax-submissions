import Mathlib.Data.Nat.Prime.Basic
import Lax242665.PrimeDivisor

/-!
The least divisor greater than 1 is prime, for the submission's own notion of
primality.
-/

namespace Lax242665Proofs.PrimeDivisor

/-- A prime in mathlib's sense is a prime in the sense of `Lax242665.Primes`. -/
theorem prime_of_natPrime {p : ℕ} (hp : Nat.Prime p) : Lax242665.Primes.Prime p :=
  ⟨hp.one_lt, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/--
---
conclusion: Lax242665.PrimeDivisor.exists_prime_dvd
---
The least divisor of `n` greater than `1` is prime and divides `n`.
-/
theorem exists_prime_dvd :
    ∀ n : ℕ, 1 < n → ∃ p : ℕ, Lax242665.Primes.Prime p ∧ p ∣ n := by
  intro n hn
  exact ⟨Nat.minFac n, prime_of_natPrime (Nat.minFac_prime (by omega)), Nat.minFac_dvd n⟩

end Lax242665Proofs.PrimeDivisor
