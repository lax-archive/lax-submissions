import Lax68.StraightLineDrawings
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Lax303502Proofs
namespace Polygonal

open Lax68.StraightLineDrawings

/-- Two segments with a common endpoint can overlap away from it only when
one of their other endpoints lies on the other segment. -/
theorem segment_common_endpoint {p q r z : Point}
    (hq : q ∉ segment ℝ p r) (hr : r ∉ segment ℝ p q)
    (hz : z ∈ segment ℝ p q) (hz' : z ∈ segment ℝ p r) : z = p := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hz
  obtain ⟨c,d,hc,hd,hcd,he'⟩ := hz'
  by_cases hb0 : b = 0
  · subst b
    have : a = 1 := by linarith
    simpa [this] using he.symm
  by_cases hd0 : d = 0
  · subst d
    have : c = 1 := by linarith
    simpa [this] using he'.symm
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have haeq : a = 1-b := by linarith
  have hceq : c = 1-d := by linarith
  subst a
  subst c
  have e1 := congrArg Prod.fst (he.trans he'.symm)
  have e2 := congrArg Prod.snd (he.trans he'.symm)
  change (1-b) * p.1 + b * q.1 = (1-d) * p.1 + d * r.1 at e1
  change (1-b) * p.2 + b * q.2 = (1-d) * p.2 + d * r.2 at e2
  rcases le_total d b with hdb | hbd
  · exfalso
    apply hq
    refine ⟨1-d/b,d/b,sub_nonneg.mpr ((div_le_one hbpos).mpr hdb),
      div_nonneg hd hb,by ring,?_⟩
    apply Prod.ext <;> change (1-d/b)*_ + (d/b)*_ = _
    · apply (mul_left_cancel₀ hb0)
      field_simp
      nlinarith
    · apply (mul_left_cancel₀ hb0)
      field_simp
      nlinarith
  · exfalso
    apply hr
    refine ⟨1-b/d,b/d,sub_nonneg.mpr ((div_le_one hdpos).mpr hbd),
      div_nonneg hb hd,by ring,?_⟩
    apply Prod.ext <;> change (1-b/d)*_ + (b/d)*_ = _
    · apply (mul_left_cancel₀ hd0)
      field_simp
      nlinarith
    · apply (mul_left_cancel₀ hd0)
      field_simp
      nlinarith

/-- Incident edges of a straight-line drawing meet only at their common vertex. -/
theorem incident_edges {V : Type*} {G : SimpleGraph V} (D : StraightLineDrawing G)
    {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    {z : Point} (hz : z ∈ segment ℝ (D.point a) (D.point b))
    (hz' : z ∈ segment ℝ (D.point a) (D.point c)) : z = D.point a :=
  segment_common_endpoint (D.noVertexOnEdge hac hab.ne.symm hbc)
    (D.noVertexOnEdge hab hac.ne.symm hbc.symm) hz hz'

/-- Intersections of distinct edges are exactly drawn common endpoints. -/
theorem distinct_edges_intersection {V : Type*} {G : SimpleGraph V}
    (D : StraightLineDrawing G) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))
    {z : Point} (hz : z ∈ segment ℝ (D.point a) (D.point b))
    (hz' : z ∈ segment ℝ (D.point c) (D.point d)) :
    ∃ x, (x = a ∨ x = b) ∧ (x = c ∨ x = d) ∧ z = D.point x := by
  classical
  by_cases hac : a = c
  · subst c
    exact ⟨a,Or.inl rfl,Or.inl rfl,
      incident_edges D hab hcd (fun h => hne (Or.inl ⟨rfl,h⟩)) hz hz'⟩
  by_cases had : a = d
  · subst d
    rw [segment_symm ℝ (D.point c) (D.point a)] at hz'
    exact ⟨a,Or.inl rfl,Or.inr rfl,
      incident_edges D hab hcd.symm (fun h => hne (Or.inr ⟨rfl,h⟩)) hz hz'⟩
  by_cases hbc : b = c
  · subst c
    rw [segment_symm ℝ (D.point a) (D.point b)] at hz
    exact ⟨b,Or.inr rfl,Or.inl rfl,
      incident_edges D hab.symm hcd (fun h => hne (Or.inr ⟨h,rfl⟩)) hz hz'⟩
  by_cases hbd : b = d
  · subst d
    rw [segment_symm ℝ (D.point a) (D.point b)] at hz
    rw [segment_symm ℝ (D.point c) (D.point b)] at hz'
    exact ⟨b,Or.inr rfl,Or.inr rfl,
      incident_edges D hab.symm hcd.symm (fun h => hne (Or.inl ⟨h,rfl⟩)) hz hz'⟩
  have hd : Disjoint ({a,b} : Set V) ({c,d}) := by
    simp [Set.disjoint_left,hac,had,hbc,hbd]
  exact (Set.disjoint_left.mp (D.disjointEdges hab hcd hd) hz hz').elim

/-- Concatenating two injective paths meeting only at the joint remains injective. -/
theorem injective_trans {p q r : Point} (A : Path p q) (B : Path q r)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hi : ∀ z, z ∈ Set.range A → z ∈ Set.range B → z = q) :
    Function.Injective (A.trans B) := by
  intro s t h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have he := congrArg Subtype.val (hA h)
    apply Subtype.ext
    dsimp at he ⊢
    linarith
  · have hz := hi _ ⟨_,rfl⟩ ⟨_,h.symm⟩
    have hb := congrArg Subtype.val (hB (h.symm.trans (hz.trans B.source.symm)))
    dsimp at hb
    exfalso
    linarith
  · have hz := hi _ ⟨_,h.symm⟩ ⟨_,rfl⟩
    have hb := congrArg Subtype.val (hB (hz.trans B.source.symm))
    dsimp at hb
    exfalso
    linarith
  · have he := congrArg Subtype.val (hB h)
    apply Subtype.ext
    dsimp at he ⊢
    linarith

theorem injective_segment {p q : Point} (hne : p ≠ q) :
    Function.Injective (Path.segment p q) := by
  intro s t h
  apply Subtype.ext
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at h1 h2
  by_contra hst
  apply hne
  apply Prod.ext
  · have : ((s : ℝ)-(t : ℝ))*(q.1-p.1) = 0 := by nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hst))).symm
  · have : ((s : ℝ)-(t : ℝ))*(q.2-p.2) = 0 := by nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hst))).symm

end Polygonal
end Lax303502Proofs
