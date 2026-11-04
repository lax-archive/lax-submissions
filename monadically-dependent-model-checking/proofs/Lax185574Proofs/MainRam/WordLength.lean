import Lax185574Proofs.MainRam.Arith

/-!
Word-length bookkeeping for thm:main: a thread runs at
`w - i - K`, and a quantity fits below `2 ^ (w - i - K - 8)` when it
fits below `2 ^ w` after multiplication by `2 ^ (i + K + 8)`.
-/

namespace Lax185574Proofs.MainRam

theorem le_two_pow_sub {B m w : ℕ} (h : B * 2 ^ m ≤ 2 ^ w) (hm : m ≤ w) : B ≤ 2 ^ (w - m) := by
  have e : 2 ^ w = 2 ^ (w - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
  rw [e] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem le_of_two_pow_le {a w : ℕ} (h : 2 ^ a ≤ 2 ^ w) : a ≤ w :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- The good thread: a bound below `2 ^ w` divided by `2 ^ (i + K + k)`
fits at the thread's word length minus `k`. -/
theorem good_fits {B i K k w : ℕ} (h : B * 2 ^ (i + K + k) ≤ 2 ^ w) :
    B ≤ 2 ^ (w - i - K - k) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · exact Nat.zero_le _
  have hle : i + K + k ≤ w := le_of_two_pow_le (le_trans (Nat.le_mul_of_pos_left _ hB) h)
  have := le_two_pow_sub h hle
  rwa [show w - (i + K + k) = w - i - K - k by omega] at this

theorem triR_le (i : ℕ) : triR i ≤ i :=
  le_trans (Nat.unpair_left_le _) (Nat.unpair_left_le i)

theorem triD_le (i : ℕ) : triD i ≤ i :=
  le_trans (Nat.unpair_right_le _) (Nat.unpair_left_le i)

theorem triJ_le (i : ℕ) : triJ i ≤ i + 1 := by
  have := Nat.unpair_right_le i
  simp only [triJ]; omega

theorem triWord_le (i : ℕ) : ∀ v ∈ triWord i, v ≤ i + 1 := by
  intro v hv
  simp only [triWord, List.mem_cons, List.not_mem_nil, or_false] at hv
  have := triR_le i; have := triD_le i; have := triJ_le i
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The time of the program of thm:skel-few-types, coarsely. -/
theorem floor_le_pow_four {cF n : ℕ} {δ : ℝ} (hδ : δ ≤ 1) :
    ⌊(cF : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ)⌋₊ ≤ cF * (n + 1) ^ 4 := by
  apply Nat.floor_le_of_le
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have : ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) ≤ ((n : ℝ) + 1) ^ ((4 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
  rw [Real.rpow_natCast] at this
  push_cast
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

/-- An accepting thread: if `2 ^ i' ≤ D` and `B 2^(K+8) D` fits below
`2 ^ w`, then `B` fits below `2 ^ (w - i' - K - 8)`, and the thread's
word length is at least twenty when `2 ^ 12 ≤ B`. -/
theorem sound_fits {B D i K w : ℕ} (hi : i + K < w) (hD : 2 ^ i ≤ D) (hB : 2 ^ 12 ≤ B)
    (h : B * 2 ^ (K + 8) * D ≤ 2 ^ w) : 20 ≤ w - i - K ∧ B ≤ 2 ^ (w - i - K - 8) := by
  have e : 2 ^ w = 2 ^ (w - i - K) * 2 ^ i * 2 ^ K := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have h20 : 20 ≤ w - i - K := by
    by_contra hc
    have h1 : 2 ^ (w - i - K) < 2 ^ 20 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ w < 2 ^ 20 * D * 2 ^ K := by
      rw [e]
      calc 2 ^ (w - i - K) * 2 ^ i * 2 ^ K ≤ 2 ^ (w - i - K) * D * 2 ^ K := by gcongr
        _ < 2 ^ 20 * D * 2 ^ K := by
          apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
          exact Nat.mul_lt_mul_of_pos_right h1 hDpos
    have h3 : 2 ^ 20 * D * 2 ^ K ≤ B * 2 ^ (K + 8) * D := by
      have : 2 ^ 20 * D * 2 ^ K = 2 ^ 12 * 2 ^ (K + 8) * D := by
        rw [show (2 : ℕ) ^ 20 = 2 ^ 12 * 2 ^ 8 by norm_num, pow_add]; ring
      rw [this]
      gcongr
    omega
  refine ⟨h20, ?_⟩
  have e' : 2 ^ (w - i - K) = 2 ^ (w - i - K - 8) * 2 ^ 8 := by
    rw [← pow_add]; congr 1; omega
  have h4 : B * 2 ^ (K + 8) * 2 ^ i ≤ 2 ^ (w - i - K - 8) * 2 ^ (K + 8) * 2 ^ i := by
    calc B * 2 ^ (K + 8) * 2 ^ i ≤ B * 2 ^ (K + 8) * D := Nat.mul_le_mul_left _ hD
      _ ≤ 2 ^ w := h
      _ = 2 ^ (w - i - K - 8) * 2 ^ (K + 8) * 2 ^ i := by rw [e, e', pow_add]; ring
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right h4 (by positivity))
    (by positivity)

end Lax185574Proofs.MainRam
