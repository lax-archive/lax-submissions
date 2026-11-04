import Mathlib

/-!
Polynomial bounds `f X ≤ c X^a` for `X ≥ 1`, closed under sums,
products and powers.
-/

namespace Lax185574Proofs.CompRam

/-- The function is bounded by a monomial for `X ≥ 1`. -/
def PB (f : ℕ → ℕ) : Prop := ∃ c a : ℕ, ∀ X, 1 ≤ X → f X ≤ c * X ^ a

theorem PB.const (c : ℕ) : PB fun _ => c := ⟨c, 0, fun X _ => by simp⟩

theorem PB.id : PB fun X => X := ⟨1, 1, fun X _ => by simp⟩

theorem PB.mono {f g : ℕ → ℕ} (hg : PB g) (h : ∀ X, 1 ≤ X → f X ≤ g X) : PB f := by
  obtain ⟨c, a, hc⟩ := hg
  exact ⟨c, a, fun X hX => le_trans (h X hX) (hc X hX)⟩

theorem PB.add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB fun X => f X + g X := by
  obtain ⟨c1, a1, h1⟩ := hf
  obtain ⟨c2, a2, h2⟩ := hg
  refine ⟨c1 + c2, a1 + a2, fun X hX => ?_⟩
  have e1 : X ^ a1 ≤ X ^ (a1 + a2) := Nat.pow_le_pow_right hX (by omega)
  have e2 : X ^ a2 ≤ X ^ (a1 + a2) := Nat.pow_le_pow_right hX (by omega)
  calc f X + g X ≤ c1 * X ^ a1 + c2 * X ^ a2 := Nat.add_le_add (h1 X hX) (h2 X hX)
    _ ≤ c1 * X ^ (a1 + a2) + c2 * X ^ (a1 + a2) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * X ^ (a1 + a2) := by ring

theorem PB.mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) : PB fun X => f X * g X := by
  obtain ⟨c1, a1, h1⟩ := hf
  obtain ⟨c2, a2, h2⟩ := hg
  refine ⟨c1 * c2, a1 + a2, fun X hX => ?_⟩
  calc f X * g X ≤ (c1 * X ^ a1) * (c2 * X ^ a2) := Nat.mul_le_mul (h1 X hX) (h2 X hX)
    _ = c1 * c2 * X ^ (a1 + a2) := by ring

theorem PB.pow {f : ℕ → ℕ} (hf : PB f) (n : ℕ) : PB fun X => f X ^ n := by
  obtain ⟨c, a, h⟩ := hf
  refine ⟨c ^ n, a * n, fun X hX => ?_⟩
  calc f X ^ n ≤ (c * X ^ a) ^ n := Nat.pow_le_pow_left (h X hX) n
    _ = c ^ n * X ^ (a * n) := by rw [mul_pow, ← pow_mul]

theorem PB.cmul {f : ℕ → ℕ} (hf : PB f) (c : ℕ) : PB fun X => c * f X :=
  (PB.const c).mul hf

theorem PB.xpow (n : ℕ) : PB fun X => X ^ n := PB.id.pow n

end Lax185574Proofs.CompRam
