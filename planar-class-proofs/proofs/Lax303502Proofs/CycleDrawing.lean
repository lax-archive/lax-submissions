import Lax303502Proofs.MinorConstructions

set_option autoImplicit false

namespace Lax303502Proofs

open Lax68.GraphMinors

theorem cycle_sameArc {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) {n : ℕ} (hi : Set.InjOn f (Set.Iio n))
    (hedge : ∀ i < n, G.Adj (f i) (f (i+1))) (hclose : f n = f 0)
    (hK : ¬IsMinor K4 G) {a b c d : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (eab : G.Adj (f a) (f b)) (ecd : G.Adj (f c) (f d))
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SameArc (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) := by
  have hab : a ≠ b := fun h => eab.ne (congrArg f h)
  have hcd : c ≠ d := fun h => ecd.ne (congrArg f h)
  have ordered {a b c d : ℕ} (han : a < n) (hbn : b < n) (hcn : c < n) (hdn : d < n)
      (hab : a < b) (hcd : c < d)
      (eab : G.Adj (f a) (f b)) (ecd : G.Adj (f c) (f d))
      (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
      SameArc (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) := by
    by_contra hn
    simp only [SameArc, Nat.cast_lt] at hn
    have hx : (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := by omega
    rcases hx with hx | hx
    · exact hK ⟨cycle_four_minor f hi hedge hclose hx.1 hx.2.1 hx.2.2 hdn eab ecd⟩
    · exact hK ⟨cycle_four_minor f hi hedge hclose hx.1 hx.2.1 hx.2.2 hbn ecd eab⟩
  rcases lt_or_gt_of_ne hab with hab | hab <;> rcases lt_or_gt_of_ne hcd with hcd | hcd
  · exact ordered ha hb hc hd hab hcd eab ecd hac had hbc hbd
  · exact (sameArc_swap_right _ _ _ _).mpr
      (ordered ha hb hd hc hab hcd eab ecd.symm had hac hbd hbc)
  · exact (sameArc_swap_left _ _ _ _).mpr
      (ordered hb ha hc hd hab hcd eab.symm ecd hbc hbd hac had)
  · exact (sameArc_swap_left _ _ _ _).mpr ((sameArc_swap_right _ _ _ _).mpr
      (ordered hb ha hd hc hab hcd eab.symm ecd.symm hbd hbc had hac))

/-- Place the vertices of a spanning cycle in their cyclic order. Any crossing
would provide the two diagonals in `cycle_four_minor`. -/
noncomputable def spanningCycle_drawing {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) {n : ℕ} (hi : Set.InjOn f (Set.Iio n))
    (hedge : ∀ i < n, G.Adj (f i) (f (i+1))) (hclose : f n = f 0)
    (hspan : ∀ v, ∃ i < n, f i = v) (hK : ¬IsMinor K4 G) : CircularDrawing G := by
  classical
  let p := fun v => (hspan v).choose
  have hp v : p v < n ∧ f (p v) = v := (hspan v).choose_spec
  refine ⟨fun v => (p v : ℝ),?_,?_⟩
  · intro x y he
    change (p x : ℝ) = (p y : ℝ) at he
    have he' : p x = p y := by exact_mod_cast he
    rw [← (hp x).2, ← (hp y).2, he']
  · intro a b c d hab hcd hdis
    have hn : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
      simpa [Set.disjoint_left, and_assoc] using hdis
    have pne {x y : V} (h : x ≠ y) : p x ≠ p y := by
      intro he; apply h; rw [← (hp x).2, ← (hp y).2, he]
    apply cycle_sameArc f hi hedge hclose hK (hp a).1 (hp b).1 (hp c).1 (hp d).1
    · simpa only [(hp a).2, (hp b).2] using hab
    · simpa only [(hp c).2, (hp d).2] using hcd
    · exact pne hn.1
    · exact pne hn.2.1
    · exact pne hn.2.2.1
    · exact pne hn.2.2.2

end Lax303502Proofs
