import Mathlib.Tactic

set_option maxHeartbeats 500000

/-!
Finite adaptive processes which draw a fresh, possibly different-length,
uniform bit block at each query. Each continuation is selected by the block
just read, so later block lengths can depend on the observed history. The
failure mass is an exact rational finite probability; it does not pad every
round to the largest block size.
-/

namespace Lax235315Proofs.Construction.AdaptiveBitBlocks

/-- A protocol with at most `R` queries. A query draws `k` fresh bits and
chooses its continuation from the observed block. -/
inductive Protocol : ℕ → Type
  | stop (R : ℕ) : Protocol R
  | query {R k : ℕ} (bad : Finset (Fin k → Bool))
      (next : (Fin k → Bool) → Protocol R) : Protocol (R + 1)

/-- Maximum number of bits consumed along any execution path. The maximum
is taken over the finitely many blocks at the current query; no bits are
charged for rounds after a path stops. -/
def maxConsumedBits : {R : ℕ} → Protocol R → ℕ
  | _, .stop _ => 0
  | _, .query (k := k) _ next =>
      k + (Finset.univ.sup fun bits => maxConsumedBits (next bits))

/-- Exact failure probability under independent uniform choices at each
query. The finite sum is over the good blocks; a bad block terminates with
failure immediately. -/
def failureMass : {R : ℕ} → Protocol R → ℚ
  | _, .stop _ => 0
  | _, .query (R := R) (k := k) bad next =>
      ((bad.card : ℚ) +
        ∑ bits : Fin k → Bool,
          if bits ∈ bad then 0 else failureMass (next bits)) /
        (2 : ℚ) ^ k

/-- Every reachable query has at most an `ε` fraction of bad blocks, and
the same bound holds recursively after every good block. -/
def LocallyBounded (ε : ℚ) : {R : ℕ} → Protocol R → Prop
  | _, .stop _ => True
  | _, .query (R := R) (k := k) bad next =>
      (bad.card : ℚ) ≤ ε * (2 : ℚ) ^ k ∧
        ∀ bits, bits ∉ bad → LocallyBounded ε (next bits)

/-- The probability of failure over an adaptive protocol is at most the
number of queries times the uniform per-query bad fraction. Query widths and
continuations may vary with the history. -/
lemma failureMass_le {R : ℕ} (p : Protocol R) (ε : ℚ)
    (hε : 0 ≤ ε) (hvalid : LocallyBounded ε p) :
    failureMass p ≤ (R : ℚ) * ε := by
  induction p with
  | stop r =>
      simp only [failureMass]
      exact mul_nonneg (Nat.cast_nonneg _) hε
  | @query r k bad next ih =>
      simp only [LocallyBounded] at hvalid
      rcases hvalid with ⟨hbad, hnext⟩
      simp only [failureMass]
      let n : ℚ := (2 : ℚ) ^ k
      have hn : 0 < n := by positivity
      have hrounds : 0 ≤ (r : ℚ) * ε := by positivity
      have hchildren :
          (∑ bits : Fin k → Bool,
            if bits ∈ bad then 0 else failureMass (next bits)) ≤
            n * ((r : ℚ) * ε) := by
        calc
          (∑ bits : Fin k → Bool,
              if bits ∈ bad then 0 else failureMass (next bits)) ≤
              ∑ bits : Fin k → Bool, (r : ℚ) * ε := by
                apply Finset.sum_le_sum
                intro bits _
                by_cases hmem : bits ∈ bad
                · simp [hmem, hrounds]
                · simpa [hmem] using ih bits (hnext bits hmem)
          _ = n * ((r : ℚ) * ε) := by
                simp [n, Fintype.card_fin, Fintype.card_bool,
                  Finset.sum_const, mul_comm]
      have htotal :
          (bad.card : ℚ) +
              (∑ bits : Fin k → Bool,
                if bits ∈ bad then 0 else failureMass (next bits)) ≤
            ε * n + n * ((r : ℚ) * ε) := by
        exact add_le_add (by simpa [n] using hbad) hchildren
      apply (div_le_iff₀ hn).2
      calc
        (bad.card : ℚ) +
            (∑ bits : Fin k → Bool,
              if bits ∈ bad then 0 else failureMass (next bits)) ≤
            ε * n + n * ((r : ℚ) * ε) := htotal
        _ = ((r + 1 : ℕ) : ℚ) * ε * n := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring

end Lax235315Proofs.Construction.AdaptiveBitBlocks
