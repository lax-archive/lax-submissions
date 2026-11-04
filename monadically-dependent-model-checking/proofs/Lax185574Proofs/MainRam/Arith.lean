import Lax185574Proofs.MainRam.Complete

/-!
The arithmetic of thm:main: the time of the good thread is
`O(n^(3+ε') + |x|)`, and the dovetailer's time is then
`⌊c (n+1)^(3+ε)⌋ + c |x|`, and at most a polynomial of degree five in
`|x|`.
-/

namespace Lax185574Proofs.MainRam

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs

/-- The word of a script is three entries per step plus `n + 1`. -/
theorem length_le_of_encodesSequence {n : ℕ} {y : List ℕ} {s : List (PartialGraph (Fin n))}
    (h : EncodesSequence y s) : y.length ≤ 3 * s.length + n := by
  obtain ⟨σ, rfl, rfl⟩ := h
  change (toWord (List.ofFn σ.colors) ++ toWord σ.steps).length ≤ _
  rw [Lax185574Proofs.Compose.toWord_list_nat]
  have hs : toWord σ.steps = σ.steps.length :: (σ.steps.map toWord).flatten := rfl
  have hf : ((σ.steps.map toWord).flatten).length = 3 * σ.steps.length := by
    rw [List.length_flatten, List.map_map]
    have : ∀ st ∈ σ.steps, (List.length ∘ toWord) st = 3 := fun st _ =>
      Lax185574Proofs.Compose.stepCode_length st
    rw [List.map_congr_left this, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]
  rw [List.length_append, List.length_cons, hs, List.length_cons, hf]
  simp only [List.length_ofFn, Script.run, List.length_scanl]
  omega

/-- A power of `N ≥ 1` with exponent at most `q` is at most `N ^ q`. -/
theorem rpow_le_rpow_of_le {N : ℝ} (hN : 1 ≤ N) {p q : ℝ} (h : p ≤ q) : N ^ p ≤ N ^ q :=
  Real.rpow_le_rpow_of_exponent_le hN h

/-- **The time of the good thread.** All quantities are those of the
good thread `(r, d, j)`: the time `tF` of the program of
thm:skel-few-types, the length `m` and the width bound `Kw` of its
sequence, the length `yl` of its word, and the time bound `tMb` of the
model-checking program, which includes a term linear in the length of
its input. -/
theorem good_time_le {N X i j a b cU cF c₂ tF m Kw yl tMb : ℕ} {ε' : ℝ} (hN : 1 ≤ N) (hj : 1 ≤ j)
    (hε'1 : ε' ≤ 1) (ha1 : 1 ≤ a) (hab : (a : ℝ) * (b + 1) / j ≤ ε') (hε' : 0 < ε')
    (htF : tF ≤ ⌊(cF : ℝ) * (N : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹)⌋₊ + cF * (X + 5))
    (hm : (m : ℝ) ≤ cF * (N : ℝ) ^ (1 + (a : ℝ) * ((j : ℝ))⁻¹))
    (hKw : Kw = ⌊(cF : ℝ) * (N : ℝ) ^ ((a : ℝ) * ((j : ℝ))⁻¹)⌋₊)
    (hyl : yl ≤ 3 * m + N)
    (htMb : tMb ≤ c₂ * m * N ^ 2 * (Kw + 1) ^ b + c₂ * (X + yl + 5)) :
    ((cU * (i + 2) ^ 2 + tF + (yl + 1) * N ^ 2 + X + tMb + 1 : ℕ) : ℝ) ≤
      (cU * (i + 2) ^ 2 + 9 * cF + c₂ * cF * (cF + 1) ^ b + 6 + c₂ * (3 * cF + 7) : ℕ) *
        ((N : ℝ) ^ ((3 : ℝ) + ε') + X) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  set β : ℝ := (a : ℝ) * ((j : ℝ))⁻¹ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβb : β * (b + 1) ≤ ε' := by
    rw [hβ]; rw [div_eq_mul_inv] at hab
    calc (a : ℝ) * ((j : ℝ))⁻¹ * (b + 1) = (a : ℝ) * (b + 1) * ((j : ℝ))⁻¹ := by ring
      _ ≤ ε' := hab
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hβ1 : β ≤ 1 := by nlinarith
  have hjinv : ((j : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hjr
  have hjε : ((j : ℝ))⁻¹ ≤ ε' := by
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have h1 : (1 : ℝ) ≤ (a : ℝ) * (b + 1) := by nlinarith
    calc ((j : ℝ))⁻¹ = 1 / j := by rw [one_div]
      _ ≤ (a : ℝ) * (b + 1) / j := div_le_div_of_nonneg_right h1 hj0.le
      _ ≤ ε' := hab
  have hββ : β ≤ ε' := by nlinarith
  set P : ℝ := (N : ℝ) ^ ((3 : ℝ) + ε') with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hNr (by linarith)
  -- the pieces
  have h1 : ((tF : ℕ) : ℝ) ≤ cF * P + cF * (X + 5) := by
    have := Nat.floor_le (show (0 : ℝ) ≤ cF * (N : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹) by positivity)
    have h3 : (N : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹) ≤ P :=
      rpow_le_rpow_of_le hNr (by linarith)
    have htF' : (tF : ℝ) ≤ (⌊(cF : ℝ) * (N : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹)⌋₊ : ℝ) + cF * (X + 5) := by
      exact_mod_cast htF
    have : (cF : ℝ) * (N : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹) ≤ cF * P :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    linarith
  have hNpow : ∀ k : ℕ, (k : ℝ) ≤ 3 → ((N : ℝ) ^ k) ≤ P := by
    intro k hk
    rw [← Real.rpow_natCast]
    exact rpow_le_rpow_of_le hNr (by linarith)
  have hN1β : (N : ℝ) ^ (1 + β) * (N : ℝ) ^ 2 ≤ P := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    exact rpow_le_rpow_of_le hNr (by push_cast; linarith)
  have h2 : (((yl + 1) * N ^ 2 : ℕ) : ℝ) ≤ (3 * cF + 2) * P := by
    have hyl' : (yl : ℝ) ≤ 3 * m + N := by exact_mod_cast hyl
    have hN2 : (N : ℝ) ^ 2 ≤ P := hNpow 2 (by norm_num)
    have hN3 : (N : ℝ) * (N : ℝ) ^ 2 ≤ P := by
      have := hNpow 3 (by norm_num); rw [pow_succ] at this; linarith
    push_cast
    have hm2 : (m : ℝ) * (N : ℝ) ^ 2 ≤ cF * P := by
      calc (m : ℝ) * (N : ℝ) ^ 2 ≤ (cF * (N : ℝ) ^ (1 + β)) * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hm (by positivity)
        _ = cF * ((N : ℝ) ^ (1 + β) * (N : ℝ) ^ 2) := by ring
        _ ≤ cF * P := mul_le_mul_of_nonneg_left hN1β (Nat.cast_nonneg _)
    have : ((yl : ℝ) + 1) * (N : ℝ) ^ 2 ≤ (3 * m + N + 1) * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc ((yl : ℝ) + 1) * (N : ℝ) ^ 2 ≤ (3 * m + N + 1) * (N : ℝ) ^ 2 := this
      _ = 3 * ((m : ℝ) * (N : ℝ) ^ 2) + (N : ℝ) * (N : ℝ) ^ 2 + (N : ℝ) ^ 2 := by ring
      _ ≤ 3 * (cF * P) + P + P := by linarith
      _ = (3 * cF + 2) * P := by ring
  have h3a : ((c₂ * m * N ^ 2 * (Kw + 1) ^ b : ℕ) : ℝ) ≤ c₂ * cF * (cF + 1) ^ b * P := by
    have hQ : 1 ≤ (N : ℝ) ^ β := Real.one_le_rpow hNr hβ0
    have hK : ((Kw : ℕ) : ℝ) + 1 ≤ (cF + 1) * (N : ℝ) ^ β := by
      rw [hKw]
      have := Nat.floor_le (show (0 : ℝ) ≤ cF * (N : ℝ) ^ β by positivity)
      nlinarith
    have hKb : (((Kw : ℕ) : ℝ) + 1) ^ b ≤ ((cF + 1) : ℝ) ^ b * (N : ℝ) ^ (β * b) := by
      calc (((Kw : ℕ) : ℝ) + 1) ^ b ≤ ((cF + 1) * (N : ℝ) ^ β) ^ b :=
            pow_le_pow_left₀ (by positivity) hK b
        _ = ((cF + 1) : ℝ) ^ b * (N : ℝ) ^ (β * b) := by
            rw [mul_pow, Real.rpow_mul_natCast (by linarith)]
    have hexp : (N : ℝ) ^ (1 + β) * (N : ℝ) ^ 2 * (N : ℝ) ^ (β * b) ≤ P := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
      exact rpow_le_rpow_of_le hNr (by push_cast; nlinarith)
    push_cast
    calc (c₂ : ℝ) * m * (N : ℝ) ^ 2 * ((Kw : ℝ) + 1) ^ b
        ≤ c₂ * (cF * (N : ℝ) ^ (1 + β)) * (N : ℝ) ^ 2 *
            (((cF + 1) : ℝ) ^ b * (N : ℝ) ^ (β * b)) := by gcongr
      _ = c₂ * cF * (cF + 1) ^ b * ((N : ℝ) ^ (1 + β) * (N : ℝ) ^ 2 * (N : ℝ) ^ (β * b)) := by
          ring
      _ ≤ c₂ * cF * (cF + 1) ^ b * P := by gcongr
  have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hmP : (m : ℝ) ≤ cF * P := by
    have : (N : ℝ) ^ (1 + β) ≤ P := rpow_le_rpow_of_le hNr (by linarith)
    calc (m : ℝ) ≤ cF * (N : ℝ) ^ (1 + β) := hm
      _ ≤ cF * P := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hNP : (N : ℝ) ≤ P := by
    have := hNpow 1 (by norm_num); rwa [pow_one] at this
  have h3 : ((tMb : ℕ) : ℝ) ≤ c₂ * cF * (cF + 1) ^ b * P + (c₂ * X + c₂ * ((3 * cF + 6) * P)) := by
    have ht : (tMb : ℝ) ≤ ((c₂ * m * N ^ 2 * (Kw + 1) ^ b : ℕ) : ℝ) + c₂ * ((X : ℝ) + yl + 5) := by
      exact_mod_cast htMb
    have hyl' : (yl : ℝ) ≤ 3 * m + N := by exact_mod_cast hyl
    have hin : (X : ℝ) + yl + 5 ≤ X + (3 * cF + 6) * P := by nlinarith
    have hc2 : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hin hc2
    have e3 : (c₂ : ℝ) * (X + (3 * cF + 6) * P) = c₂ * X + c₂ * ((3 * cF + 6) * P) := by ring
    linarith
  have hcU : (((cU * (i + 2) ^ 2 : ℕ)) : ℝ) ≤ (cU * (i + 2) ^ 2 : ℕ) * P :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hP1
  push_cast at h1 h2 h3 hcU ⊢
  have hcF : (0 : ℝ) ≤ cF := Nat.cast_nonneg _
  set A : ℝ := (cU : ℝ) * ((i : ℝ) + 2) ^ 2
  set D : ℝ := (c₂ : ℝ) * cF * (cF + 1) ^ b
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hAX : 0 ≤ A * X := mul_nonneg hA0 hX
  have hDX : 0 ≤ D * X := mul_nonneg hD0 hX
  have hFX : 0 ≤ (cF : ℝ) * X := mul_nonneg hcF hX
  have hFP : (cF : ℝ) ≤ cF * P := le_mul_of_one_le_right hcF hP1
  have hc2 : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg _
  have hE1 : (0 : ℝ) ≤ c₂ * P := mul_nonneg hc2 (by linarith)
  have hE2 : (0 : ℝ) ≤ c₂ * ((3 * cF + 6) * X) := mul_nonneg hc2 (by positivity)
  have e : (A + 9 * cF + D + 6 + c₂ * (3 * cF + 7)) * (P + X) =
      A * P + 9 * (cF * P) + D * P + 6 * P + A * X + 9 * (cF * X) + D * X + 6 * X +
        (c₂ * ((3 * cF + 6) * P) + c₂ * P + c₂ * X + c₂ * ((3 * cF + 6) * X)) := by ring
  rw [e]
  have h1' : (tF : ℝ) ≤ cF * P + cF * X + 5 * cF := by linarith
  linarith

/-- **The final arithmetic.** If the good thread's work `W` is
`O(n^(3+ε') + |x|)` and the dovetailer's time `T` is at most `A (W' + 1)`
for `W' ≤ K W`, then `T` is within the bound of thm:main, and at most a
polynomial of degree five in `|x|`. -/
theorem final_time_le {N X W W' T A K CW : ℕ} {ε ε' : ℝ} (hN : 1 ≤ N) (hNX : N ≤ X + 1)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hεε : ε' ≤ ε)
    (hW : (W : ℝ) ≤ CW * ((N : ℝ) ^ ((3 : ℝ) + ε') + X)) (hW' : W' ≤ K * W)
    (hT : T ≤ A * (W' + 1)) :
    T ≤ ⌊((A * (K * CW + 1) : ℕ) : ℝ) * (N : ℝ) ^ ((3 : ℝ) + ε)⌋₊ + A * (K * CW + 1) * X ∧
      T ≤ 2 * (A * (K * CW + 1)) * (X + 1) ^ 5 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  set P' : ℝ := (N : ℝ) ^ ((3 : ℝ) + ε') with hP'
  have hP'1 : 1 ≤ P' := Real.one_le_rpow hNr (by linarith)
  have hTr : (T : ℝ) ≤ A * (K * (CW * (P' + X)) + 1) := by
    have h1 : (T : ℝ) ≤ A * ((W' : ℝ) + 1) := by exact_mod_cast hT
    have h2 : (W' : ℝ) ≤ K * W := by exact_mod_cast hW'
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have h3 : (K : ℝ) * W ≤ K * (CW * (P' + X)) := mul_le_mul_of_nonneg_left hW hK
    have : (W' : ℝ) + 1 ≤ K * (CW * (P' + X)) + 1 := by linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_left this hA)
  have hTr' : (T : ℝ) ≤ (A * (K * CW + 1) : ℕ) * (P' + X) := by
    push_cast
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have : (K : ℝ) * (CW * (P' + X)) + 1 ≤ (K * CW + 1) * (P' + X) := by
      have : (K : ℝ) * (CW * (P' + X)) = K * CW * (P' + X) := by ring
      nlinarith
    calc (T : ℝ) ≤ A * (K * (CW * (P' + X)) + 1) := hTr
      _ ≤ A * ((K * CW + 1) * (P' + X)) := mul_le_mul_of_nonneg_left this hA
      _ = A * (K * CW + 1) * (P' + X) := by ring
  set c : ℕ := A * (K * CW + 1)
  constructor
  · have hPP : P' ≤ (N : ℝ) ^ ((3 : ℝ) + ε) := rpow_le_rpow_of_le hNr (by linarith)
    have : (T : ℝ) - c * X ≤ c * (N : ℝ) ^ ((3 : ℝ) + ε) := by
      have : (c : ℝ) * P' ≤ c * (N : ℝ) ^ ((3 : ℝ) + ε) :=
        mul_le_mul_of_nonneg_left hPP (Nat.cast_nonneg _)
      nlinarith
    by_cases hTc : T ≤ c * X
    · omega
    · have : T - c * X ≤ ⌊(c : ℝ) * (N : ℝ) ^ ((3 : ℝ) + ε)⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      omega
  · have hP5 : P' ≤ ((X : ℝ) + 1) ^ 5 := by
      calc P' ≤ (N : ℝ) ^ ((5 : ℕ) : ℝ) := rpow_le_rpow_of_le hNr (by push_cast; linarith)
        _ = (N : ℝ) ^ 5 := Real.rpow_natCast _ _
        _ ≤ ((X : ℝ) + 1) ^ 5 := pow_le_pow_left₀ (by linarith) (by exact_mod_cast hNX) 5
    have hX5 : (X : ℝ) ≤ ((X : ℝ) + 1) ^ 5 := by
      have : (1 : ℝ) ≤ (X : ℝ) + 1 := by linarith
      calc (X : ℝ) ≤ (X : ℝ) + 1 := by linarith
        _ = ((X : ℝ) + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((X : ℝ) + 1) ^ 5 := pow_le_pow_right₀ this (by norm_num)
    have : (T : ℝ) ≤ ((2 * c * (X + 1) ^ 5 : ℕ) : ℝ) := by
      push_cast
      have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast this

end Lax185574Proofs.MainRam
