import Mathlib.Tactic

/-!
The ruler sequence: the exponent of two in a positive number. A
dovetailer gives slot `j` to thread `ruler j`, so thread `i` gets every
`2 ^ (i + 1)`-th slot, the first at `2 ^ i`. Computing `ruler j` by
halving costs `ruler j + 1` steps, which is `O(1)` amortized.
-/

namespace Lax185574Proofs.Ruler

/-- The exponent of two in `j`, with `ruler 0 = 0`. -/
def ruler (j : ℕ) : ℕ :=
  if h : j ≠ 0 ∧ j % 2 = 0 then ruler (j / 2) + 1 else 0
termination_by j
decreasing_by omega

theorem ruler_odd {j : ℕ} (h : j % 2 = 1) : ruler j = 0 := by
  rw [ruler, dif_neg (by omega)]

theorem ruler_zero : ruler 0 = 0 := by rw [ruler, dif_neg (by omega)]

theorem ruler_even {j : ℕ} (h0 : j ≠ 0) (h : j % 2 = 0) : ruler j = ruler (j / 2) + 1 := by
  rw [ruler, dif_pos ⟨h0, h⟩]

theorem ruler_two_mul {m : ℕ} (h : m ≠ 0) : ruler (2 * m) = ruler m + 1 := by
  rw [ruler_even (by omega) (by omega), Nat.mul_div_cancel_left _ (by norm_num)]

/-- `ruler j = i` exactly for the odd multiples of `2 ^ i`. -/
theorem ruler_pow_mul_odd (i m : ℕ) : ruler (2 ^ i * (2 * m + 1)) = i := by
  induction i with
  | zero => simp only [pow_zero, one_mul]; exact ruler_odd (by omega)
  | succ i ih =>
      rw [pow_succ, mul_comm (2 ^ i) 2, mul_assoc, ruler_two_mul (by positivity), ih]

/-- The ruler function is unchanged by reduction modulo `2 ^ w`, unless
the result is zero. -/
theorem ruler_mod {j w : ℕ} (h : j % 2 ^ w ≠ 0) : ruler (j % 2 ^ w) = ruler j := by
  induction w generalizing j with
  | zero => exact absurd (by simp [Nat.mod_one] : j % 2 ^ 0 = 0) h
  | succ w ih =>
      by_cases hj : j % 2 = 1
      · rw [ruler_odd hj, ruler_odd]
        rw [pow_succ, Nat.mod_mul_left_mod]; exact hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have h2 : 2 * m % 2 ^ (w + 1) = 2 * (m % 2 ^ w) := by
          rw [pow_succ, mul_comm (2 ^ w) 2, Nat.mul_mod_mul_left]
        rw [h2] at h ⊢
        have hm : m % 2 ^ w ≠ 0 := by omega
        rw [ruler_two_mul hm, ruler_two_mul (by rintro rfl; simp at hm), ih hm]

/-- The sum of `ruler` over the first `n` positive numbers is at most `n`. -/
theorem sum_ruler_half (n : ℕ) : ∑ j ∈ Finset.range n, ruler (j + 1) =
    ∑ j ∈ Finset.range (n / 2), ruler (j + 1) + n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [ruler_odd (by omega), show (m + m) / 2 = m by omega,
          show (m + m + 1) / 2 = m by omega, Nat.add_zero]
      · rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
          Finset.sum_range_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
          ruler_two_mul (by omega)]
        omega

theorem sum_ruler_le (n : ℕ) : ∑ j ∈ Finset.range n, ruler (j + 1) ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [sum_ruler_half]
        have := ih (n / 2) (by omega)
        omega

theorem le_ruler_of_dvd {j w : ℕ} (h0 : j ≠ 0) (h : 2 ^ w ∣ j) : w ≤ ruler j := by
  induction w generalizing j with
  | zero => omega
  | succ w ih =>
      obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by
        have := Nat.dvd_trans (dvd_pow_self 2 (by omega : w + 1 ≠ 0)) h; omega⟩
      rw [ruler_two_mul (by omega)]
      have : 2 ^ w ∣ m := by
        rw [pow_succ, mul_comm] at h; exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
      have := ih (by omega) this
      omega

/-- The number of slots before `j` that go to thread `i`. -/
def count (i j : ℕ) : ℕ := ((Finset.range j).filter (fun j' => j' ≠ 0 ∧ ruler j' = i)).card

theorem count_succ (i j : ℕ) :
    count i (j + 1) = count i j + if j ≠ 0 ∧ ruler j = i then 1 else 0 := by
  simp only [count, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- By slot `2 ^ i * (2 c + 1)` thread `i` has had `c + 1` slots. -/
theorem count_ge (i c : ℕ) : c + 1 ≤ count i (2 ^ i * (2 * c + 1) + 1) := by
  have hsub : (Finset.range (c + 1)).image (fun m => 2 ^ i * (2 * m + 1)) ⊆
      (Finset.range (2 ^ i * (2 * c + 1) + 1)).filter (fun j' => j' ≠ 0 ∧ ruler j' = i) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, by positivity, ruler_pow_mul_odd i m⟩
    have : 2 ^ i * (2 * m + 1) ≤ 2 ^ i * (2 * c + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h; omega), Finset.card_range] at this
  exact this

/-- `2 ^ ruler j` divides `j`. -/
theorem pow_ruler_dvd (j : ℕ) : 2 ^ ruler j ∣ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      by_cases h : j ≠ 0 ∧ j % 2 = 0
      · rw [ruler_even h.1 h.2, pow_succ]
        have := ih (j / 2) (by omega)
        obtain ⟨k, hk⟩ := this
        exact ⟨k, by rw [mul_comm (2 ^ ruler (j / 2)) 2, mul_assoc]; omega⟩
      · rw [ruler, dif_neg h]; exact one_dvd j

/-- Thread `i` has had at most `j / 2 ^ i` of the slots before `j`. -/
theorem pow_mul_count_le (i j : ℕ) : 2 ^ i * count i j ≤ j := by
  have hP : 0 < 2 ^ i := by positivity
  have hmaps : ∀ j' ∈ (Finset.range j).filter (fun j' => j' ≠ 0 ∧ ruler j' = i),
      j' / 2 ^ i - 1 ∈ Finset.range (j / 2 ^ i) := by
    intro j' hj'
    simp only [Finset.mem_filter, Finset.mem_range] at hj' ⊢
    obtain ⟨hlt, h0, hr⟩ := hj'
    obtain ⟨k, hk⟩ := pow_ruler_dvd j'
    rw [hr] at hk
    have hk0 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk; omega
      · exact h
    have e1 : j' / 2 ^ i = k := by rw [hk, Nat.mul_div_cancel_left _ hP]
    have e2 : 2 ^ i * k < j := by rw [← hk]; exact hlt
    have e4 : k ≤ j / 2 ^ i := by
      rw [Nat.le_div_iff_mul_le hP, mul_comm]; omega
    omega
  have hinj : Set.InjOn (fun j' => j' / 2 ^ i - 1)
      ((Finset.range j).filter (fun j' => j' ≠ 0 ∧ ruler j' = i) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
    obtain ⟨ka, hka⟩ := pow_ruler_dvd a
    obtain ⟨kb, hkb⟩ := pow_ruler_dvd b
    rw [ha.2.2] at hka
    rw [hb.2.2] at hkb
    have ka0 : ka ≠ 0 := by rintro rfl; simp at hka; omega
    have kb0 : kb ≠ 0 := by rintro rfl; simp at hkb; omega
    simp only at hab
    rw [hka, hkb, Nat.mul_div_cancel_left _ hP, Nat.mul_div_cancel_left _ hP] at hab
    rw [hka, hkb, show ka = kb by omega]
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hc
  calc 2 ^ i * count i j ≤ 2 ^ i * (j / 2 ^ i) := Nat.mul_le_mul_left _ hc
    _ ≤ j := Nat.mul_div_le j (2 ^ i)

end Lax185574Proofs.Ruler
