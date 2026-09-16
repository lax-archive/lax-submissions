import Mathlib.Data.Nat.Factorial.Basic
import Lax242665.InfinitelyManyPrimes
import Lax242665.PrimeDivisor

/-!
Euclid's proof that there are infinitely many primes.
-/

namespace Lax242665Proofs.InfinitelyManyPrimes

/--
---
conclusion: Lax242665.InfinitelyManyPrimes.exists_prime_gt
assumptions:
  - Lax242665.PrimeDivisor.exists_prime_dvd
---
Euclid's argument: a prime divisor `p` of `n! + 1` cannot be at most `n`,
because then `p` would divide `n!` and hence divide `1`.
-/
theorem exists_prime_gt : ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p := by
  intro n
  have hpos := Nat.factorial_pos n
  obtain ⟨p, hp, hdvd⟩ :=
    Lax242665.PrimeDivisor.exists_prime_dvd (n.factorial + 1) (by omega)
  refine ⟨p, hp, ?_⟩
  have h1 : 1 < p := hp.1
  by_contra hle
  rw [Nat.not_lt] at hle
  have hdvd_fact : p ∣ n.factorial := Nat.dvd_factorial (by omega) hle
  have hdvd_one : p ∣ 1 := (Nat.dvd_add_right hdvd_fact).mp hdvd
  have := Nat.le_of_dvd Nat.one_pos hdvd_one
  omega

end Lax242665Proofs.InfinitelyManyPrimes
