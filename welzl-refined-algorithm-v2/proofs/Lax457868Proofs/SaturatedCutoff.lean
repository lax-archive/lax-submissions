import Mathlib

/-!
Arithmetic support for the capped base-case cutoff used by the refined
Welzl algorithm.  These are natural-number facts only.  In particular, this
file does not verify an IMP+ instruction sequence, the computation of
`Nat.clog`, or register fit.
-/

namespace Lax457868Proofs

/-- Addition guarded by remaining capacity.  On the guarded branch the sum
is at most `limit`; the potentially large sum is not part of the guard. -/
def satAdd (limit a b : ℕ) : ℕ :=
  if a ≤ limit ∧ b ≤ limit - a then a + b else limit

/-- Multiplication guarded by division.  When `b` is nonzero, the product is
computed only if the quotient test proves it is at most `limit`. -/
def satMul (limit a b : ℕ) : ℕ :=
  if b = 0 then 0 else if a ≤ limit / b then a * b else limit

theorem satAdd_eq_min (limit a b : ℕ) :
    satAdd limit a b = min limit (a + b) := by
  by_cases h : a ≤ limit ∧ b ≤ limit - a
  · simp [satAdd, h]
    omega
  · have hlarge : limit ≤ a + b := by
      by_cases ha : a ≤ limit
      · have hb : limit - a < b := by
          by_contra hn
          have : b ≤ limit - a := Nat.le_of_not_gt hn
          exact h ⟨ha, this⟩
        omega
      · omega
    simp [satAdd, h, Nat.min_def]
    omega

theorem satAdd_result_le (limit a b : ℕ) : satAdd limit a b ≤ limit := by
  rw [satAdd_eq_min]
  exact min_le_left _ _

theorem satAdd_safe_branch (limit a b : ℕ)
    (h : a ≤ limit ∧ b ≤ limit - a) :
    satAdd limit a b = a + b ∧ a + b ≤ limit := by
  simp [satAdd, h]
  omega

theorem satMul_eq_min (limit a b : ℕ) :
    satMul limit a b = min limit (a * b) := by
  by_cases hb : b = 0
  · subst b
    simp [satMul]
  · by_cases h : a ≤ limit / b
    · have hp : a * b ≤ limit := by
        have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).mp h
        omega
      simp [satMul, hb, h, Nat.min_def]
      omega
    · have hp : limit ≤ a * b := by
        have hn : ¬ a * b ≤ limit := by
          intro hh
          exact h ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).mpr hh)
        omega
      simp [satMul, hb, h, Nat.min_def]
      omega

theorem satMul_result_le (limit a b : ℕ) : satMul limit a b ≤ limit := by
  rw [satMul_eq_min]
  exact min_le_left _ _

theorem satMul_safe_branch (limit a b : ℕ) (hb : b ≠ 0)
    (h : a ≤ limit / b) :
    satMul limit a b = a * b ∧ a * b ≤ limit := by
  have hp : a * b ≤ limit := by
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).mp h
  simp [satMul, hb, h, hp]

theorem satAdd_clamped_inputs (limit a b : ℕ) :
    satAdd limit (min limit a) (min limit b) = satAdd limit a b := by
  rw [satAdd_eq_min, satAdd_eq_min]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem satMul_clamped_inputs (limit a b : ℕ) :
    satMul limit (min limit a) (min limit b) = satMul limit a b := by
  rw [satMul_eq_min, satMul_eq_min]
  by_cases ha : a ≤ limit
  · by_cases hb : b ≤ limit
    · simp [Nat.min_def, ha, hb]
    · have hbl : limit ≤ b := Nat.le_of_not_ge hb
      by_cases hz : a = 0
      · simp [hz]
      · have hpos : 0 < a := Nat.pos_of_ne_zero hz
        have h₁ : limit ≤ a * limit := Nat.le_mul_of_pos_left limit hpos
        have h₂ : limit ≤ a * b := by
          exact h₁.trans (Nat.mul_le_mul_left a hbl)
        simp [Nat.min_def, ha, hbl, h₂]
        omega
  · have hal : limit ≤ a := Nat.le_of_not_ge ha
    by_cases hb : b ≤ limit
    · by_cases hz : b = 0
      · simp [hz]
      · have hpos : 0 < b := Nat.pos_of_ne_zero hz
        have h₁ : limit ≤ limit * b := Nat.le_mul_of_pos_right limit hpos
        have h₂ : limit ≤ a * b := by
          exact h₁.trans (Nat.mul_le_mul_right b hal)
        simp [Nat.min_def, hal, hb, h₂]
        omega
    · have hbl : limit ≤ b := Nat.le_of_not_ge hb
      by_cases hz : limit = 0
      · subst limit
        simp
      · have hpos : 0 < limit := Nat.pos_of_ne_zero hz
        have h₁ : limit ≤ limit * limit := Nat.le_mul_of_pos_left limit hpos
        have h₂ : limit ≤ a * b := by
          exact h₁.trans (Nat.mul_le_mul hal hbl)
        simp [Nat.min_def, hal, hbl, h₂]
        omega

theorem min_add_clamped_inputs (limit a b : ℕ) :
    min limit (min limit a + min limit b) = min limit (a + b) := by
  rw [← satAdd_eq_min, satAdd_clamped_inputs, satAdd_eq_min]

theorem min_mul_clamped_inputs (limit a b : ℕ) :
    min limit (min limit a * min limit b) = min limit (a * b) := by
  rw [← satMul_eq_min, satMul_clamped_inputs, satMul_eq_min]

theorem min_mul_clamped_left (limit a b : ℕ) :
    min limit (min limit a * b) = min limit (a * b) := by
  rw [← min_mul_clamped_inputs limit (min limit a) b]
  have h : min limit (min limit a) = min limit a :=
    min_eq_right (min_le_left _ _)
  rw [h]
  exact min_mul_clamped_inputs limit a b

theorem min_mul_clamped_right (limit a b : ℕ) :
    min limit (a * min limit b) = min limit (a * b) := by
  rw [← min_mul_clamped_inputs limit a (min limit b)]
  have h : min limit (min limit b) = min limit b :=
    min_eq_right (min_le_left _ _)
  rw [h]
  exact min_mul_clamped_inputs limit a b

theorem min_add_clamped_left (limit a b : ℕ) :
    min limit (min limit a + b) = min limit (a + b) := by
  rw [← min_add_clamped_inputs limit (min limit a) b]
  have h : min limit (min limit a) = min limit a :=
    min_eq_right (min_le_left _ _)
  rw [h]
  exact min_add_clamped_inputs limit a b

theorem min_add_clamped_right (limit a b : ℕ) :
    min limit (a + min limit b) = min limit (a + b) := by
  rw [← min_add_clamped_inputs limit a (min limit b)]
  have h : min limit (min limit b) = min limit b :=
    min_eq_right (min_le_left _ _)
  rw [h]
  exact min_add_clamped_inputs limit a b

/-- The mathematical parameter in the paper's cutoff. -/
def refinedCutoffK (c : ℕ) : ℕ :=
  768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1

/-- Repeated guarded products compute the capped fifth power. -/
def satPow5 (limit c : ℕ) : ℕ :=
  let c2 := satMul limit c c
  let c3 := satMul limit c2 c
  let c4 := satMul limit c3 c
  satMul limit c4 c

theorem satPow5_eq (limit c : ℕ) : satPow5 limit c = min limit (c ^ 5) := by
  simp [satPow5, satMul_eq_min, min_mul_clamped_left, Nat.pow_succ]

/-- Exact capped implementation of `min n (2*k)`.  Every intermediate is a
guarded operation with cap `n`; no uncapped power or parameter is evaluated. -/
def saturatedWelzlCutoff (n c : ℕ) : ℕ := Id.run do
  let ℓ := Nat.clog 2 c
  let s := satMul n 64 ℓ
  let sPlusOne := satAdd n s 1
  let p5 := satPow5 n c
  let p := satMul n 768 p5
  let q := satMul n p sPlusOne
  let r := satMul n q ℓ
  let k := satAdd n r 1
  return satMul n 2 k

/-- The exact cutoff strategy checks `n ≤ c` first.  Its second branch is
the guarded arithmetic calculation above, so `clog₂ c` is only needed when
`c < n`. -/
def earlyWelzlCutoff (n c : ℕ) : ℕ :=
  if n ≤ c then n else saturatedWelzlCutoff n c

theorem saturatedWelzlCutoff_eq (n c : ℕ) :
    saturatedWelzlCutoff n c = min n (2 * refinedCutoffK c) := by
  unfold saturatedWelzlCutoff refinedCutoffK
  simp [Id.run, satPow5_eq, satMul_eq_min, satAdd_eq_min,
    min_mul_clamped_left, min_mul_clamped_right,
    min_add_clamped_left]
  rfl

theorem saturatedWelzlCutoff_eq_limit_iff (n c : ℕ) :
    saturatedWelzlCutoff n c = n ↔ n ≤ 2 * refinedCutoffK c := by
  rw [saturatedWelzlCutoff_eq]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem saturatedWelzlCutoff_exact_of_lt (n c : ℕ)
    (h : saturatedWelzlCutoff n c < n) :
    saturatedWelzlCutoff n c = 2 * refinedCutoffK c := by
  rw [saturatedWelzlCutoff_eq] at h ⊢
  have hlt : 2 * refinedCutoffK c < n := by
    by_contra hnot
    have hn : n ≤ 2 * refinedCutoffK c := Nat.le_of_not_gt hnot
    simp [Nat.min_eq_left hn] at h
  simp [Nat.min_eq_right (Nat.le_of_lt hlt)]

theorem saturatedWelzlCutoff_le (n c : ℕ) :
    saturatedWelzlCutoff n c ≤ n := by
  rw [saturatedWelzlCutoff_eq]
  exact min_le_left _ _

theorem refinedCutoffK_ge_c (c : ℕ) (hc : 2 ≤ c) :
    c ≤ refinedCutoffK c := by
  let ℓ := Nat.clog 2 c
  have hℓpos : 0 < ℓ := Nat.clog_pos (by omega) (by omega)
  have hℓ : 1 ≤ ℓ := by omega
  have hpow : c ≤ c ^ 5 := Nat.le_self_pow (by decide) c
  have h768 : c ^ 5 ≤ 768 * c ^ 5 := by
    exact Nat.le_mul_of_pos_left (c ^ 5) (by omega)
  have hterm : 768 * c ^ 5 ≤ (768 * c ^ 5) * (64 * ℓ + 1) :=
    Nat.le_mul_of_pos_right (768 * c ^ 5) (by omega)
  have hterm' : (768 * c ^ 5) * (64 * ℓ + 1) ≤
      (768 * c ^ 5 * (64 * ℓ + 1)) * ℓ :=
    Nat.le_mul_of_pos_right (768 * c ^ 5 * (64 * ℓ + 1)) hℓpos
  change c ≤ 768 * c ^ 5 * (64 * ℓ + 1) * ℓ + 1
  calc
    c ≤ c ^ 5 := hpow
    _ ≤ 768 * c ^ 5 := h768
    _ ≤ (768 * c ^ 5) * (64 * ℓ + 1) := hterm
    _ ≤ (768 * c ^ 5 * (64 * ℓ + 1)) * ℓ := hterm'
    _ ≤ (768 * c ^ 5 * (64 * ℓ + 1)) * ℓ + 1 := Nat.le_add_right _ _

theorem earlyWelzlCutoff_eq (n c : ℕ) (hc : 2 ≤ c) :
    earlyWelzlCutoff n c = min n (2 * refinedCutoffK c) := by
  by_cases hnc : n ≤ c
  · have hbound : n ≤ 2 * refinedCutoffK c := by
      exact hnc.trans ((refinedCutoffK_ge_c c hc).trans
        (Nat.le_mul_of_pos_left (refinedCutoffK c) (by omega)))
    simp [earlyWelzlCutoff, hnc, Nat.min_eq_left hbound]
  · rw [earlyWelzlCutoff, if_neg hnc, saturatedWelzlCutoff_eq]

theorem earlyWelzlCutoff_log_le (n c : ℕ) (h : ¬ n ≤ c) :
    Nat.clog 2 c ≤ Nat.clog 2 n := by
  exact Nat.clog_mono_right 2 (Nat.lt_of_not_ge h).le

end Lax457868Proofs
