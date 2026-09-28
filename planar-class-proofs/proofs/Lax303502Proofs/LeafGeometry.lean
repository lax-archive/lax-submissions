import Lax303502Proofs.Circle

set_option autoImplicit false

namespace Lax303502Proofs

/-- An affine functional vanishing on the chord with parameters `a,b`. -/
noncomputable def chordSide (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - a * b) * p.1 + (a + b) * p.2 - (1 + a * b)

theorem chordSide_circlePoint (a b t : ℝ) :
    chordSide a b (circlePoint t) = -2 * (t - a) * (t - b) / (1 + t ^ 2) := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  dsimp [chordSide, circlePoint]
  field_simp
  ring

theorem chordSide_outside {a b t : ℝ} (hab : a < b) (ht : t < a ∨ b < t) :
    chordSide a b (circlePoint t) < 0 := by
  rw [chordSide_circlePoint]
  have hp : 0 < (t - a) * (t - b) := by
    rcases ht with ht | ht
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr ht) (sub_neg.mpr (ht.trans hab))
    · exact mul_pos (sub_pos.mpr (hab.trans ht)) (sub_pos.mpr ht)
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

theorem chordSide_combo (a b : ℝ) (p q : ℝ × ℝ) (s t : ℝ) (hst : s + t = 1) :
    chordSide a b (s • p + t • q) = s * chordSide a b p + t * chordSide a b q := by
  simp only [chordSide, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  linear_combination (1 + a * b) * hst

theorem chordSide_on_chord {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ segment ℝ (circlePoint a) (circlePoint b)) : chordSide a b p = 0 := by
  rcases hp with ⟨s, t, _, _, hst, rfl⟩
  rw [chordSide_combo _ _ _ _ _ _ hst]
  simp [chordSide_circlePoint]

theorem chordSide_negative_on_segment {a b : ℝ} {p q x : ℝ × ℝ}
    (hp : chordSide a b p < 0) (hq : chordSide a b q < 0)
    (hx : x ∈ segment ℝ p q) : chordSide a b x < 0 := by
  rcases hx with ⟨s, t, hs, ht, hst, rfl⟩
  rw [chordSide_combo _ _ _ _ _ _ hst]
  by_cases hs0 : s = 0
  · have ht1 : t = 1 := by linarith
    simpa [hs0, ht1] using hq
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have h₁ := mul_neg_of_pos_of_neg hspos hp
    have h₂ := mul_nonpos_of_nonneg_of_nonpos ht hq.le
    linarith

/-- A chord between consecutive circle parameters misses all chords whose
endpoints are outside that parameter interval. -/
theorem adjacent_chord_disjoint {a b c d : ℝ} (hab : a < b)
    (hc : c < a ∨ b < c) (hd : d < a ∨ b < d) :
    Disjoint (segment ℝ (circlePoint a) (circlePoint b))
      (segment ℝ (circlePoint c) (circlePoint d)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hz := chordSide_on_chord hx
  have hn := chordSide_negative_on_segment (chordSide_outside hab hc)
    (chordSide_outside hab hd) hy
  linarith

/-- A finite set leaves a nonempty gap immediately to the right of any
specified real number. Endpoints in the set are permitted at the left end. -/
theorem finite_parameter_gap (s : Finset ℝ) (a : ℝ) :
    ∃ b, a < b ∧ ∀ x ∈ s, x ≤ a ∨ b < x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨a + 1, by linarith, by simp⟩
  | @insert x s _ ih =>
    obtain ⟨b, hab, hb⟩ := ih
    by_cases hx : x ≤ a
    · refine ⟨b, hab, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl hx
      · exact hb y hy
    · have hax : a < x := lt_of_not_ge hx
      refine ⟨(a + min x b) / 2, ?_, ?_⟩
      · have := lt_min hax hab
        linarith
      · intro y hy
        have hbx : (a + min x b) / 2 < x := by
          have := min_le_left x b
          linarith
        have hbb : (a + min x b) / 2 < b := by
          have := min_le_right x b
          linarith
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inr hbx
        · rcases hb y hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (hbb.trans hy)

end Lax303502Proofs
