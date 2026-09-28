import Lax68.Outerplanar
import Mathlib

set_option autoImplicit false

namespace Lax303502Proofs

/-- A rational parametrization of the unit circle, omitting `(-1,0)`. -/
noncomputable def circlePoint (t : ℝ) : ℝ × ℝ :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

theorem circlePoint_onCircle (t : ℝ) :
    (circlePoint t).1 ^ 2 + (circlePoint t).2 ^ 2 = 1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_injective : Function.Injective circlePoint := by
  have recover (t : ℝ) : (circlePoint t).2 / (1 + (circlePoint t).1) = t := by
    have h : 1 + t ^ 2 ≠ 0 := by positivity
    dsimp [circlePoint]
    field_simp
    ring
  intro s t h
  rw [← recover s, ← recover t, h]

/-- A tangent functional is strictly smaller at any other unit-circle point. -/
theorem circle_dot_lt {p q : ℝ × ℝ}
    (hp : p.1 ^ 2 + p.2 ^ 2 = 1) (hq : q.1 ^ 2 + q.2 ^ 2 = 1)
    (hne : p ≠ q) : p.1 * q.1 + p.2 * q.2 < 1 := by
  have hdist : 0 < (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
    by_cases h : p.1 = q.1
    · have h' : p.2 ≠ q.2 := fun h' => hne (Prod.ext h h')
      have := sq_pos_of_ne_zero (sub_ne_zero.mpr h')
      nlinarith [sq_nonneg (p.1 - q.1)]
    · have := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
      nlinarith [sq_nonneg (p.2 - q.2)]
  nlinarith

/-- A chord between unit-circle points contains no third point of the circle. -/
theorem circle_not_mem_segment {a b c : ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) (hb : b.1 ^ 2 + b.2 ^ 2 = 1)
    (hc : c.1 ^ 2 + c.2 ^ 2 = 1) (hca : c ≠ a) (hcb : c ≠ b) :
    c ∉ segment ℝ a b := by
  rintro ⟨s, t, hs, ht, hst, heq⟩
  have h₁ := congrArg Prod.fst heq
  have h₂ := congrArg Prod.snd heq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h₁ h₂
  have hca' := circle_dot_lt hc ha hca
  have hcb' := circle_dot_lt hc hb hcb
  have he : s * (c.1 * a.1 + c.2 * a.2) +
      t * (c.1 * b.1 + c.2 * b.2) = 1 := by
    calc
      _ = c.1 * (s * a.1 + t * b.1) + c.2 * (s * a.2 + t * b.2) := by ring
      _ = 1 := by rw [h₁, h₂]; nlinarith [hc]
  by_cases ht0 : t = 0
  · have hs1 : s = 1 := by linarith
    simp [ht0, hs1] at he
    linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hle := mul_le_mul_of_nonneg_left (le_of_lt hca') hs
    have hlt := mul_lt_mul_of_pos_left hcb' htpos
    nlinarith

end Lax303502Proofs
