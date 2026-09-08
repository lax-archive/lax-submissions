import Mathlib.Data.Nat.Prime.Factorial
import Lax242665.InfinitelyManyPrimes

/-!
Euclid's proof that there are infinitely many primes, for the submission's
own notion of primality.
-/

namespace Lax242665Proofs.InfinitelyManyPrimes

/-- A prime in mathlib's sense is a prime in the sense of `Lax242665.Primes`. -/
theorem prime_of_natPrime {p : ℕ} (hp : Nat.Prime p) : Lax242665.Primes.Prime p :=
  ⟨hp.one_lt, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/--
---
conclusion: Lax242665.InfinitelyManyPrimes.exists_prime_gt
---
Euclid's argument: the smallest prime factor `p` of `n! + 1` cannot be at
most `n`, because then `p` would divide `n!` and hence divide `1`.
-/
theorem exists_prime_gt : ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p := by
  intro n
  have hne : n.factorial + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  have hprime : Nat.Prime (Nat.minFac (n.factorial + 1)) := Nat.minFac_prime hne
  refine ⟨Nat.minFac (n.factorial + 1), prime_of_natPrime hprime, ?_⟩
  by_contra hle
  rw [Nat.not_lt] at hle
  have hdvd_fact : Nat.minFac (n.factorial + 1) ∣ n.factorial :=
    hprime.dvd_factorial.mpr hle
  have hdvd_succ : Nat.minFac (n.factorial + 1) ∣ n.factorial + 1 := Nat.minFac_dvd _
  have hdvd_one : Nat.minFac (n.factorial + 1) ∣ 1 :=
    (Nat.dvd_add_right hdvd_fact).mp hdvd_succ
  exact hprime.one_lt.ne' (Nat.dvd_one.mp hdvd_one)

end Lax242665Proofs.InfinitelyManyPrimes
