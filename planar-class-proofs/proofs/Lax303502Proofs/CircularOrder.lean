import Lax303502Proofs.LeafGeometry
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace Lax303502Proofs

/-- The two last points lie in the same component of the parameter circle
after the first two points are removed. Endpoints are excluded separately. -/
def SameArc (a b c d : ℝ) : Prop := ((a<c ↔ b<c) ↔ (a<d ↔ b<d))

theorem sameArc_swap_left (a b c d : ℝ) : SameArc b a c d ↔ SameArc a b c d := by
  unfold SameArc
  tauto

theorem sameArc_swap_right (a b c d : ℝ) : SameArc a b d c ↔ SameArc a b c d := by
  exact Iff.comm

theorem sameArc_symm {a b c d : ℝ} (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    SameArc a b c d ↔ SameArc c d a b := by
  have flip {x y : ℝ} (h : x≠y) : y<x ↔ ¬x<y := by
    constructor
    · intro h'; exact not_lt_of_ge h'.le
    · intro h'
      exact lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)
  simp only [SameArc,flip hac,flip had,flip hbc,flip hbd]
  tauto

theorem chordSide_inside {a b t : ℝ} (hat : a<t) (htb : t<b) :
    0 < chordSide a b (circlePoint t) := by
  rw [chordSide_circlePoint]
  apply div_pos
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) (sub_pos.mpr hat))
      (sub_neg.mpr htb)
  · positivity

theorem chordSide_positive_on_segment {a b : ℝ} {p q x : ℝ × ℝ}
    (hp : 0<chordSide a b p) (hq : 0<chordSide a b q)
    (hx : x ∈ segment ℝ p q) : 0<chordSide a b x := by
  rcases hx with ⟨s,t,hs,ht,hst,rfl⟩
  rw [chordSide_combo _ _ _ _ _ _ hst]
  by_cases hs0 : s=0
  · have ht1 : t=1 := by linarith
    simpa [hs0,ht1] using hq
  · have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
    have h₁ := mul_pos hspos hp
    have h₂ := mul_nonneg ht hq.le
    linarith

theorem chordSide_zero_between {a b : ℝ} {p q : ℝ × ℝ}
    (hp : chordSide a b p < 0) (hq : 0 < chordSide a b q) :
    ∃ z ∈ segment ℝ p q, chordSide a b z=0 := by
  let A := chordSide a b p
  let B := chordSide a b q
  have hd : 0<B-A := sub_pos.mpr (hp.trans hq)
  have hsum : B/(B-A)+(-A)/(B-A)=1 := by field_simp; ring
  refine ⟨(B/(B-A)) • p + ((-A)/(B-A)) • q,?_,?_⟩
  · exact ⟨_,_,div_nonneg hq.le hd.le,div_nonneg (neg_nonneg.mpr hp.le) hd.le,hsum,rfl⟩
  · rw [chordSide_combo _ _ _ _ _ _ hsum]
    change B/(B-A)*A+(-A)/(B-A)*B=0
    field_simp
    ring

theorem interleaving_chords_meet {a b c d : ℝ} (hac : a<c) (hcb : c<b) (hbd : b<d) :
    ¬ Disjoint (segment ℝ (circlePoint a) (circlePoint b))
      (segment ℝ (circlePoint c) (circlePoint d)) := by
  have hab := hac.trans hcb
  have hcd := hcb.trans hbd
  obtain ⟨x,hx,hx'⟩ := chordSide_zero_between
    (chordSide_outside hcd (Or.inl hac)) (chordSide_inside hcb hbd)
  obtain ⟨y,hy,hy'⟩ := chordSide_zero_between
    (chordSide_outside hab (Or.inr hbd)) (chordSide_inside hac hcb)
  have hyseg : y ∈ segment ℝ (circlePoint c) (circlePoint d) := by
    rwa [segment_symm] at hy
  have hx0 := chordSide_on_chord hx
  have hy0 := chordSide_on_chord hyseg
  have hdet : 0 < (1-a*b)*(c+d)-(1-c*d)*(a+b) := by
    have he : (1-a*b)*(c+d)-(1-c*d)*(a+b) =
        (c-a)*(1+b^2)+(d-b)*(1+c^2+(b-c)*(c-a)) := by ring
    rw [he]
    positivity
  have he : x=y := by
    have e₁ : (1-a*b)*(x.1-y.1)+(a+b)*(x.2-y.2)=0 := by
      dsimp [chordSide] at hx0 hy'
      linarith
    have e₂ : (1-c*d)*(x.1-y.1)+(c+d)*(x.2-y.2)=0 := by
      dsimp [chordSide] at hx' hy0
      linarith
    have h₁ : ((1-a*b)*(c+d)-(1-c*d)*(a+b))*(x.1-y.1)=0 := by
      linear_combination (c+d)*e₁-(a+b)*e₂
    have h₂ : ((1-a*b)*(c+d)-(1-c*d)*(a+b))*(x.2-y.2)=0 := by
      linear_combination (1-a*b)*e₂-(1-c*d)*e₁
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left (ne_of_gt hdet)))
      (sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left (ne_of_gt hdet)))
  intro hd
  exact Set.disjoint_left.mp hd hx (he ▸ hyseg)

theorem sameArc_iff_between {a b c d : ℝ} (hab : a<b)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    SameArc a b c d ↔ ((a<c ∧ c<b) ↔ (a<d ∧ d<b)) := by
  unfold SameArc
  have hbc' : b<c ↔ ¬c<b := by
    constructor
    · exact fun h => not_lt_of_ge h.le
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) hbc
  have hbd' : b<d ↔ ¬d<b := by
    constructor
    · exact fun h => not_lt_of_ge h.le
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) hbd
  rw [hbc',hbd']
  have hc : a<c ∨ c<b := by rcases lt_or_gt_of_ne hac with h | h; exact Or.inl h; exact Or.inr (h.trans hab)
  have hd : a<d ∨ d<b := by rcases lt_or_gt_of_ne had with h | h; exact Or.inl h; exact Or.inr (h.trans hab)
  tauto

theorem disjoint_chords_iff_sameArc {a b c d : ℝ} (hab : a≠b) (_hcd : c≠d)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    Disjoint (segment ℝ (circlePoint a) (circlePoint b))
      (segment ℝ (circlePoint c) (circlePoint d)) ↔ SameArc a b c d := by
  have ordered {a b c d : ℝ} (hab : a<b)
      (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
      Disjoint (segment ℝ (circlePoint a) (circlePoint b))
        (segment ℝ (circlePoint c) (circlePoint d)) ↔ SameArc a b c d := by
    rw [sameArc_iff_between hab hac had hbc hbd]
    have outside {x : ℝ} (hax : a≠x) (hbx : b≠x) (hn : ¬(a<x ∧ x<b)) : x<a ∨ b<x := by
      rcases lt_or_gt_of_ne hax with h | h
      · right
        exact lt_of_le_of_ne (le_of_not_gt (fun hb => hn ⟨h,hb⟩)) hbx
      · exact Or.inl h
    constructor
    · intro hd
      constructor
      · intro hc
        by_contra hn
        rcases outside had hbd hn with hda | hbd'
        · have hm := interleaving_chords_meet hda hc.1 hc.2
          exact hm (by simpa only [segment_symm ℝ (circlePoint d) (circlePoint c)] using hd.symm)
        · exact interleaving_chords_meet hc.1 hc.2 hbd' hd
      · intro hc
        by_contra hn
        rcases outside hac hbc hn with hca | hbc'
        · exact interleaving_chords_meet hca hc.1 hc.2 hd.symm
        · have hm := interleaving_chords_meet hc.1 hc.2 hbc'
          exact hm (by simpa only [segment_symm ℝ (circlePoint d) (circlePoint c)] using hd)
    · intro he
      by_cases hc : a<c ∧ c<b
      · have hd := he.mp hc
        rw [Set.disjoint_left]
        intro x hx hy
        have hz := chordSide_on_chord hx
        have hp := chordSide_positive_on_segment (chordSide_inside hc.1 hc.2)
          (chordSide_inside hd.1 hd.2) hy
        linarith
      · exact adjacent_chord_disjoint hab (outside hac hbc hc)
          (outside had hbd (fun h => hc (he.mpr h)))
  rcases lt_or_gt_of_ne hab with h | h
  · exact ordered h hac had hbc hbd
  · rw [segment_symm ℝ (circlePoint a),← sameArc_swap_left]
    exact ordered h hbc hbd hac had

end Lax303502Proofs
