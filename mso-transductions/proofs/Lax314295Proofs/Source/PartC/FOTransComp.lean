/-
First-order transductions are closed under composition.

This is the step that the book quotes in the (deferred) proof of Theorem
`nolabel:thm-fo-transduction-into-primes`: "first-order transductions are closed under composition,
which is proved by substituting formulas".

Given transductions `T₁ : ITrans A B` and `T₂ : ITrans B C`, the composed
transduction has one copy of the input positions for every pair (copy of `T₂`,
copy of `T₁`), one extra element for every pair (copy of `T₂`, extra element of
`T₁`) and one for every extra element of `T₂` -- plus one never selected junk
element, which is only there to make the map `phi` below total.  Its formulas
are obtained by the backwards translation of
`RequestProject/PartC/FOTransTr.lean`, applied to the formulas of `T₂`.
-/
import Lax314295Proofs.Source.PartC.FOTransTr
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace FOTr

open MSO

variable {A B C : Type}

section Comp

variable (T₁ : ITrans A B) (T₂ : ITrans B C) (lP : List T₁.P) (lE : List T₁.E)

/-- The copies of the composed transduction. -/
abbrev CP : Type := T₂.P × T₁.P

/-- The extra elements of the composed transduction: a copy of `T₂` over an
extra element of `T₁`, an extra element of `T₂`, or the junk element. -/
abbrev CE : Type := (T₂.P × T₁.E) ⊕ (T₂.E ⊕ Unit)

/-- The order formulas of the composed transduction.  The variable `x₀` denotes
the input position below the first element and every other variable the input
position below the second one, which is the convention used by all four order
formulas of `ITrans`. -/
noncomputable def ordAll : (CP T₁ T₂ ⊕ CE T₁ T₂) → (CP T₁ T₂ ⊕ CE T₁ T₂) → MSO A
  | Sum.inl (j, i), Sum.inl (j', i') =>
      tr T₁ lP lE (fun m => if m = 0 then Sum.inl i else Sum.inl i') (T₂.ordPP j j')
  | Sum.inl (j, i), Sum.inr (Sum.inl (j', r')) =>
      tr T₁ lP lE (fun m => if m = 0 then Sum.inl i else Sum.inr r') (T₂.ordPP j j')
  | Sum.inl (j, i), Sum.inr (Sum.inr (Sum.inl j')) =>
      tr T₁ lP lE (fun _ => Sum.inl i) (T₂.ordPC j j')
  | Sum.inl (_, _), Sum.inr (Sum.inr (Sum.inr ())) => MSO.ff
  | Sum.inr (Sum.inl (j, r)), Sum.inl (j', i') =>
      tr T₁ lP lE (fun m => if m = 0 then Sum.inr r else Sum.inl i') (T₂.ordPP j j')
  | Sum.inr (Sum.inl (j, r)), Sum.inr (Sum.inl (j', r')) =>
      tr T₁ lP lE (fun m => if m = 0 then Sum.inr r else Sum.inr r') (T₂.ordPP j j')
  | Sum.inr (Sum.inl (j, r)), Sum.inr (Sum.inr (Sum.inl j')) =>
      tr T₁ lP lE (fun _ => Sum.inr r) (T₂.ordPC j j')
  | Sum.inr (Sum.inl (_, _)), Sum.inr (Sum.inr (Sum.inr ())) => MSO.ff
  | Sum.inr (Sum.inr (Sum.inl j)), Sum.inl (j', i') =>
      tr T₁ lP lE (fun _ => Sum.inl i') (T₂.ordCP j j')
  | Sum.inr (Sum.inr (Sum.inl j)), Sum.inr (Sum.inl (j', r')) =>
      tr T₁ lP lE (fun _ => Sum.inr r') (T₂.ordCP j j')
  | Sum.inr (Sum.inr (Sum.inl j)), Sum.inr (Sum.inr (Sum.inl j')) =>
      trZ T₁ lP lE (T₂.ordCC j j')
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr (Sum.inr ())) => MSO.ff
  | Sum.inr (Sum.inr (Sum.inr ())), _ => MSO.ff

/-- The composition of two transductions. -/
noncomputable def comp : ITrans A C :=
  haveI := T₁.finP; haveI := T₁.finE; haveI := T₂.finP; haveI := T₂.finE
  { P := CP T₁ T₂
    E := CE T₁ T₂
    finP := inferInstance
    finE := inferInstance
    univP := fun a =>
      MSO.and (T₁.univP a.2) (tr T₁ lP lE (fun _ => Sum.inl a.2) (T₂.univP a.1))
    univC := fun e =>
      match e with
      | Sum.inl (j, r) =>
          MSO.and (atZeroF (T₁.univC r)) (tr T₁ lP lE (fun _ => Sum.inr r) (T₂.univP j))
      | Sum.inr (Sum.inl j) => trZ T₁ lP lE (T₂.univC j)
      | Sum.inr (Sum.inr ()) => MSO.ff
    labP := fun a c => tr T₁ lP lE (fun _ => Sum.inl a.2) (T₂.labP a.1 c)
    labC := fun e c =>
      match e with
      | Sum.inl (j, r) => tr T₁ lP lE (fun _ => Sum.inr r) (T₂.labP j c)
      | Sum.inr (Sum.inl j) => trZ T₁ lP lE (T₂.labC j c)
      | Sum.inr (Sum.inr ()) => MSO.ff
    ordPP := fun a b => ordAll T₁ T₂ lP lE (Sum.inl a) (Sum.inl b)
    ordPC := fun a b => ordAll T₁ T₂ lP lE (Sum.inl a) (Sum.inr b)
    ordCP := fun a b => ordAll T₁ T₂ lP lE (Sum.inr a) (Sum.inl b)
    ordCC := fun a b => ordAll T₁ T₂ lP lE (Sum.inr a) (Sum.inr b) }

@[simp] lemma comp_P : (comp T₁ T₂ lP lE).P = CP T₁ T₂ := rfl
@[simp] lemma comp_E : (comp T₁ T₂ lP lE).E = CE T₁ T₂ := rfl

/-- The element of the composed transduction attached to an element of `T₂`,
using the enumeration `es₁` of the elements of `T₁`. -/
def phi (es₁ : List T₁.Elt) : T₂.Elt → (comp T₁ T₂ lP lE).Elt
  | Sum.inl (j, q) =>
      match es₁[q]? with
      | some (Sum.inl (i, p)) => Sum.inl ((j, i), p)
      | some (Sum.inr r) => Sum.inr (Sum.inl (j, r))
      | none => Sum.inr (Sum.inr (Sum.inr ()))
  | Sum.inr j => Sum.inr (Sum.inr (Sum.inl j))

lemma phi_inl_of_inl {es₁ : List T₁.Elt} {j : T₂.P} {q : ℕ} {i : T₁.P} {p : ℕ}
    (hq : q < es₁.length) (h : es₁[q] = Sum.inl (i, p)) :
    phi T₁ T₂ lP lE es₁ (Sum.inl (j, q)) = Sum.inl ((j, i), p) := by
  show (match es₁[q]? with
    | some (Sum.inl (i, p)) => Sum.inl ((j, i), p)
    | some (Sum.inr r) => Sum.inr (Sum.inl (j, r))
    | none => Sum.inr (Sum.inr (Sum.inr ()))) = _
  rw [List.getElem?_eq_getElem hq, h]
  rfl

lemma phi_inl_of_inr {es₁ : List T₁.Elt} {j : T₂.P} {q : ℕ} {r : T₁.E}
    (hq : q < es₁.length) (h : es₁[q] = Sum.inr r) :
    phi T₁ T₂ lP lE es₁ (Sum.inl (j, q)) = Sum.inr (Sum.inl (j, r)) := by
  show (match es₁[q]? with
    | some (Sum.inl (i, p)) => Sum.inl ((j, i), p)
    | some (Sum.inr r) => Sum.inr (Sum.inl (j, r))
    | none => Sum.inr (Sum.inr (Sum.inr ()))) = _
  rw [List.getElem?_eq_getElem hq, h]
  rfl

lemma phi_inl_of_ge {es₁ : List T₁.Elt} {j : T₂.P} {q : ℕ} (hq : es₁.length ≤ q) :
    phi T₁ T₂ lP lE es₁ (Sum.inl (j, q)) = Sum.inr (Sum.inr (Sum.inr ())) := by
  show (match es₁[q]? with
    | some (Sum.inl (i, p)) => Sum.inl ((j, i), p)
    | some (Sum.inr r) => Sum.inr (Sum.inl (j, r))
    | none => Sum.inr (Sum.inr (Sum.inr ()))) = _
  rw [List.getElem?_eq_none hq]
  rfl

lemma phi_inr {es₁ : List T₁.Elt} (j : T₂.E) :
    phi T₁ T₂ lP lE es₁ (Sum.inr j) = Sum.inr (Sum.inr (Sum.inl j)) := rfl

end Comp

/-! ## Correctness of the composed transduction -/

section Correct

variable {T₁ : ITrans A B} {T₂ : ITrans B C} {lP : List T₁.P} {lE : List T₁.E}
  {w : List A} {v : List B} {es₁ : List T₁.Elt}
  (hFO₁ : T₁.AllFO) (hFO₂ : T₂.AllFO) (hP₁ : T₁.Proper) (H₁ : ITrans.Enum T₁ w v es₁)
  (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE)

include hFO₁ hFO₂ hP₁ H₁ hlP hlE

/-- The universe formulas of the composed transduction select exactly the
elements attached to the selected elements of `T₂`. -/
lemma selected_phi (x : T₂.Elt) :
    (comp T₁ T₂ lP lE).selected w (phi T₁ T₂ lP lE es₁ x) ↔ T₂.selected v x := by
  have hlen : es₁.length = v.length := H₁.length
  rcases x with ⟨j, q⟩ | j
  · rcases Nat.lt_or_ge q es₁.length with hq | hq
    · have hqv : q < v.length := by rw [← hlen]; exact hq
      have hsel1 : T₁.selected w es₁[q] := H₁.selected_getElem hq
      rcases hx : es₁[q] with ⟨i, p⟩ | r
      · rw [phi_inl_of_inl T₁ T₂ lP lE hq hx]
        rw [hx] at hsel1
        show (p < w.length ∧ Sat w (fun _ => p) (fun _ => ∅)
          (MSO.and (T₁.univP i) (tr T₁ lP lE (fun _ => Sum.inl i) (T₂.univP j)))) ↔ _
        have htr : Sat w (fun _ => p) (fun _ => ∅)
            (tr T₁ lP lE (fun _ => Sum.inl i) (T₂.univP j)) ↔
            Sat v (fun _ => q) (fun _ => ∅) (T₂.univP j) := by
          refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.univP j) (hFO₂.1 j) (fun _ => Sum.inl i)
            (fun _ => p) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
          intro i' _
          exact ⟨hq, by rw [hx]; rfl⟩
        show _ ↔ (q < v.length ∧ Sat v (fun _ => q) (fun _ => ∅) (T₂.univP j))
        constructor
        · rintro ⟨-, -, h2⟩
          exact ⟨hqv, htr.1 h2⟩
        · rintro ⟨-, h2⟩
          exact ⟨hsel1.1, hsel1.2, htr.2 h2⟩
      · rw [phi_inl_of_inr T₁ T₂ lP lE hq hx]
        rw [hx] at hsel1
        show Sat w (fun _ => 0) (fun _ => ∅)
          (MSO.and (atZeroF (T₁.univC r)) (tr T₁ lP lE (fun _ => Sum.inr r) (T₂.univP j))) ↔ _
        have htr : Sat w (fun _ => 0) (fun _ => ∅)
            (tr T₁ lP lE (fun _ => Sum.inr r) (T₂.univP j)) ↔
            Sat v (fun _ => q) (fun _ => ∅) (T₂.univP j) := by
          refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.univP j) (hFO₂.1 j) (fun _ => Sum.inr r)
            (fun _ => 0) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
          intro i' _
          exact ⟨hq, by rw [hx]; rfl⟩
        have hz : Sat w (fun _ => 0) (fun _ => ∅) (atZeroF (T₁.univC r)) :=
          (sat_atZeroF w (hFO₁.2.1 r) _ _).2 hsel1
        show _ ↔ (q < v.length ∧ Sat v (fun _ => q) (fun _ => ∅) (T₂.univP j))
        constructor
        · rintro ⟨-, h2⟩
          exact ⟨hqv, htr.1 h2⟩
        · rintro ⟨-, h2⟩
          exact ⟨hz, htr.2 h2⟩
    · rw [phi_inl_of_ge T₁ T₂ lP lE hq]
      have hnv : ¬ q < v.length := by rw [← hlen]; omega
      constructor
      · intro h
        exact absurd (le_refl 0) h
      · rintro ⟨h, -⟩
        exact absurd h hnv
  · rw [phi_inr T₁ T₂ lP lE]
    show Sat w (fun _ => 0) (fun _ => ∅) (trZ T₁ lP lE (T₂.univC j)) ↔ _
    exact sat_trZ hFO₁ hP₁ H₁ hlP hlE (T₂.univC j) (hFO₂.2.1 j) _ _ _

/-- The letter formulas of the composed transduction agree with those of `T₂`
on the elements attached to the elements of `T₂`. -/
lemma labRel_phi {x : T₂.Elt} (hx : T₂.selected v x) (c : C) :
    (comp T₁ T₂ lP lE).labRel w (phi T₁ T₂ lP lE es₁ x) c ↔ T₂.labRel v x c := by
  have hlen : es₁.length = v.length := H₁.length
  rcases x with ⟨j, q⟩ | j
  · have hq : q < es₁.length := by rw [hlen]; exact hx.1
    rcases hxe : es₁[q] with ⟨i, p⟩ | r
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe]
      show Sat w (fun _ => p) (fun _ => ∅) (tr T₁ lP lE (fun _ => Sum.inl i) (T₂.labP j c)) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.labP j c) (hFO₂.2.2.1 j c) (fun _ => Sum.inl i)
        (fun _ => p) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro i' _
      exact ⟨hq, by rw [hxe]; rfl⟩
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe]
      show Sat w (fun _ => 0) (fun _ => ∅) (tr T₁ lP lE (fun _ => Sum.inr r) (T₂.labP j c)) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.labP j c) (hFO₂.2.2.1 j c) (fun _ => Sum.inr r)
        (fun _ => 0) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro i' _
      exact ⟨hq, by rw [hxe]; rfl⟩
  · rw [phi_inr T₁ T₂ lP lE]
    show Sat w (fun _ => 0) (fun _ => ∅) (trZ T₁ lP lE (T₂.labC j c)) ↔ _
    exact sat_trZ hFO₁ hP₁ H₁ hlP hlE (T₂.labC j c) (hFO₂.2.2.2.1 j c) _ _ _

/-- The order formulas of the composed transduction agree with those of `T₂`
on the elements attached to the selected elements of `T₂`. -/
lemma ordRel_phi {x y : T₂.Elt} (hx : T₂.selected v x) (hy : T₂.selected v y) :
    (comp T₁ T₂ lP lE).ordRel w (phi T₁ T₂ lP lE es₁ x) (phi T₁ T₂ lP lE es₁ y) ↔
      T₂.ordRel v x y := by
  have hlen : es₁.length = v.length := H₁.length
  rcases x with ⟨j, q⟩ | j <;> rcases y with ⟨j', q'⟩ | j'
  · -- both are copies of `T₂`
    have hq : q < es₁.length := by rw [hlen]; exact hx.1
    have hq' : q' < es₁.length := by rw [hlen]; exact hy.1
    rcases hxe : es₁[q] with ⟨i, p⟩ | r <;> rcases hye : es₁[q'] with ⟨i', p'⟩ | r'
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe, phi_inl_of_inl T₁ T₂ lP lE hq' hye]
      show Sat w (fun m => if m = 0 then p else p') (fun _ => ∅)
        (tr T₁ lP lE (fun m => if m = 0 then Sum.inl i else Sum.inl i') (T₂.ordPP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPP j j') (hFO₂.2.2.2.2.1 j j')
        (fun m => if m = 0 then Sum.inl i else Sum.inl i')
        (fun m => if m = 0 then p else p') (fun m => if m = 0 then q else q')
        (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      by_cases hm : m = 0
      · simp only [if_pos hm]
        exact ⟨hq, by rw [hxe]; rfl⟩
      · simp only [if_neg hm]
        exact ⟨hq', by rw [hye]; rfl⟩
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe, phi_inl_of_inr T₁ T₂ lP lE hq' hye]
      show Sat w (fun _ => p) (fun _ => ∅)
        (tr T₁ lP lE (fun m => if m = 0 then Sum.inl i else Sum.inr r') (T₂.ordPP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPP j j') (hFO₂.2.2.2.2.1 j j')
        (fun m => if m = 0 then Sum.inl i else Sum.inr r')
        (fun _ => p) (fun m => if m = 0 then q else q')
        (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      by_cases hm : m = 0
      · simp only [if_pos hm]
        exact ⟨hq, by rw [hxe]; rfl⟩
      · simp only [if_neg hm]
        exact ⟨hq', by rw [hye]; rfl⟩
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe, phi_inl_of_inl T₁ T₂ lP lE hq' hye]
      show Sat w (fun _ => p') (fun _ => ∅)
        (tr T₁ lP lE (fun m => if m = 0 then Sum.inr r else Sum.inl i') (T₂.ordPP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPP j j') (hFO₂.2.2.2.2.1 j j')
        (fun m => if m = 0 then Sum.inr r else Sum.inl i')
        (fun _ => p') (fun m => if m = 0 then q else q')
        (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      by_cases hm : m = 0
      · simp only [if_pos hm]
        exact ⟨hq, by rw [hxe]; rfl⟩
      · simp only [if_neg hm]
        exact ⟨hq', by rw [hye]; rfl⟩
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe, phi_inl_of_inr T₁ T₂ lP lE hq' hye]
      show Sat w (fun _ => 0) (fun _ => ∅)
        (tr T₁ lP lE (fun m => if m = 0 then Sum.inr r else Sum.inr r') (T₂.ordPP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPP j j') (hFO₂.2.2.2.2.1 j j')
        (fun m => if m = 0 then Sum.inr r else Sum.inr r')
        (fun _ => 0) (fun m => if m = 0 then q else q')
        (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      by_cases hm : m = 0
      · simp only [if_pos hm]
        exact ⟨hq, by rw [hxe]; rfl⟩
      · simp only [if_neg hm]
        exact ⟨hq', by rw [hye]; rfl⟩
  · -- a copy and an extra element of `T₂`
    have hq : q < es₁.length := by rw [hlen]; exact hx.1
    rcases hxe : es₁[q] with ⟨i, p⟩ | r
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe, phi_inr T₁ T₂ lP lE]
      show Sat w (fun _ => p) (fun _ => ∅)
        (tr T₁ lP lE (fun _ => Sum.inl i) (T₂.ordPC j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPC j j') (hFO₂.2.2.2.2.2.1 j j')
        (fun _ => Sum.inl i) (fun _ => p) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      exact ⟨hq, by rw [hxe]; rfl⟩
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe, phi_inr T₁ T₂ lP lE]
      show Sat w (fun _ => 0) (fun _ => ∅)
        (tr T₁ lP lE (fun _ => Sum.inr r) (T₂.ordPC j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordPC j j') (hFO₂.2.2.2.2.2.1 j j')
        (fun _ => Sum.inr r) (fun _ => 0) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      exact ⟨hq, by rw [hxe]; rfl⟩
  · -- an extra element of `T₂` and a copy
    have hq' : q' < es₁.length := by rw [hlen]; exact hy.1
    rcases hye : es₁[q'] with ⟨i', p'⟩ | r'
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq' hye, phi_inr T₁ T₂ lP lE]
      show Sat w (fun _ => p') (fun _ => ∅)
        (tr T₁ lP lE (fun _ => Sum.inl i') (T₂.ordCP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordCP j j') (hFO₂.2.2.2.2.2.2.1 j j')
        (fun _ => Sum.inl i') (fun _ => p') (fun _ => q') (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      exact ⟨hq', by rw [hye]; rfl⟩
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq' hye, phi_inr T₁ T₂ lP lE]
      show Sat w (fun _ => 0) (fun _ => ∅)
        (tr T₁ lP lE (fun _ => Sum.inr r') (T₂.ordCP j j')) ↔ _
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.ordCP j j') (hFO₂.2.2.2.2.2.2.1 j j')
        (fun _ => Sum.inr r') (fun _ => 0) (fun _ => q') (fun _ => ∅) (fun _ => ∅) ?_).symm
      intro m _
      exact ⟨hq', by rw [hye]; rfl⟩
  · -- two extra elements of `T₂`
    rw [phi_inr T₁ T₂ lP lE, phi_inr T₁ T₂ lP lE]
    show Sat w (fun _ => 0) (fun _ => ∅) (trZ T₁ lP lE (T₂.ordCC j j')) ↔ _
    exact sat_trZ hFO₁ hP₁ H₁ hlP hlE (T₂.ordCC j j') (hFO₂.2.2.2.2.2.2.2 j j') _ _ _

omit hFO₁ hFO₂ hP₁ hlP hlE in
/-- The map `phi` is injective on the selected elements of `T₂`. -/
lemma phi_injOn {x y : T₂.Elt} (hx : T₂.selected v x) (hy : T₂.selected v y)
    (h : phi T₁ T₂ lP lE es₁ x = phi T₁ T₂ lP lE es₁ y) : x = y := by
  have hlen : es₁.length = v.length := H₁.length
  rcases x with ⟨j, q⟩ | j <;> rcases y with ⟨j', q'⟩ | j'
  · have hq : q < es₁.length := by rw [hlen]; exact hx.1
    have hq' : q' < es₁.length := by rw [hlen]; exact hy.1
    rcases hxe : es₁[q] with ⟨i, p⟩ | r <;> rcases hye : es₁[q'] with ⟨i', p'⟩ | r'
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe, phi_inl_of_inl T₁ T₂ lP lE hq' hye] at h
      have h1 : j = j' := congrArg (fun z => z.1.1) (Sum.inl.inj h)
      have h2 : i = i' := congrArg (fun z => z.1.2) (Sum.inl.inj h)
      have h3 : p = p' := congrArg (fun z => z.2) (Sum.inl.inj h)
      subst h1; subst h2; subst h3
      have : es₁[q] = es₁[q'] := by rw [hxe, hye]
      rw [H₁.index_unique hq hq' this]
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe, phi_inl_of_inr T₁ T₂ lP lE hq' hye] at h
      exact absurd h (by simp)
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe, phi_inl_of_inl T₁ T₂ lP lE hq' hye] at h
      exact absurd h (by simp)
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe, phi_inl_of_inr T₁ T₂ lP lE hq' hye] at h
      have h1 : j = j' := congrArg (fun z => z.1) (Sum.inl.inj (Sum.inr.inj h))
      have h2 : r = r' := congrArg (fun z => z.2) (Sum.inl.inj (Sum.inr.inj h))
      subst h1; subst h2
      have : es₁[q] = es₁[q'] := by rw [hxe, hye]
      rw [H₁.index_unique hq hq' this]
  · have hq : q < es₁.length := by rw [hlen]; exact hx.1
    rw [phi_inr T₁ T₂ lP lE] at h
    rcases hxe : es₁[q] with ⟨i, p⟩ | r
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq hxe] at h
      exact absurd h (by simp)
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq hxe] at h
      exact absurd (Sum.inr.inj h) (by simp)
  · have hq' : q' < es₁.length := by rw [hlen]; exact hy.1
    rw [phi_inr T₁ T₂ lP lE] at h
    rcases hye : es₁[q'] with ⟨i', p'⟩ | r'
    · rw [phi_inl_of_inl T₁ T₂ lP lE hq' hye] at h
      exact absurd h (by simp)
    · rw [phi_inl_of_inr T₁ T₂ lP lE hq' hye] at h
      exact absurd (Sum.inr.inj h) (by simp)
  · rw [phi_inr T₁ T₂ lP lE, phi_inr T₁ T₂ lP lE] at h
    rw [Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))]

/-- Every element selected by the composed transduction is attached to a
selected element of `T₂`. -/
lemma exists_phi {z : (comp T₁ T₂ lP lE).Elt} (hz : (comp T₁ T₂ lP lE).selected w z) :
    ∃ x : T₂.Elt, T₂.selected v x ∧ phi T₁ T₂ lP lE es₁ x = z := by
  have hlen : es₁.length = v.length := H₁.length
  rcases z with ⟨⟨j, i⟩, p⟩ | e
  · obtain ⟨hp, hsat⟩ := hz
    have hsat1 : Sat w (fun _ => p) (fun _ => ∅) (T₁.univP i) := hsat.1
    have hsel1 : T₁.selected w (Sum.inl (i, p)) := ⟨hp, hsat1⟩
    obtain ⟨q, hq, hqe⟩ := H₁.exists_index hsel1
    refine ⟨Sum.inl (j, q), ?_, ?_⟩
    · refine ⟨by rw [← hlen]; exact hq, ?_⟩
      refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.univP j) (hFO₂.1 j) (fun _ => Sum.inl i)
        (fun _ => p) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).2 hsat.2
      intro m _
      exact ⟨hq, by rw [hqe]; rfl⟩
    · exact phi_inl_of_inl T₁ T₂ lP lE hq hqe
  · rcases e with ⟨j, r⟩ | e
    · obtain ⟨hsat1, hsat2⟩ := hz
      have hsel1 : T₁.selected w (Sum.inr r) := (sat_atZeroF w (hFO₁.2.1 r) _ _).1 hsat1
      obtain ⟨q, hq, hqe⟩ := H₁.exists_index hsel1
      refine ⟨Sum.inl (j, q), ?_, ?_⟩
      · refine ⟨by rw [← hlen]; exact hq, ?_⟩
        refine (sat_tr hFO₁ hP₁ H₁ hlP hlE (T₂.univP j) (hFO₂.1 j) (fun _ => Sum.inr r)
          (fun _ => 0) (fun _ => q) (fun _ => ∅) (fun _ => ∅) ?_).2 hsat2
        intro m _
        exact ⟨hq, by rw [hqe]; rfl⟩
      · exact phi_inl_of_inr T₁ T₂ lP lE hq hqe
    · rcases e with j | u
      · refine ⟨Sum.inr j, ?_, phi_inr T₁ T₂ lP lE j⟩
        have : Sat w (fun _ => 0) (fun _ => ∅) (trZ T₁ lP lE (T₂.univC j)) := hz
        exact (sat_trZ hFO₁ hP₁ H₁ hlP hlE (T₂.univC j) (hFO₂.2.1 j) _ _ _).1 this
      · exact absurd (le_refl 0) hz

end Correct

/-! ## The composed transduction is proper, first-order and computes the
composition -/

section Main

variable {T₁ : ITrans A B} {T₂ : ITrans B C} {lP : List T₁.P} {lE : List T₁.E}

lemma allFO_comp (hFO₁ : T₁.AllFO) : (comp T₁ T₂ lP lE).AllFO := by
  have hord : ∀ z z' : CP T₁ T₂ ⊕ CE T₁ T₂, (ordAll T₁ T₂ lP lE z z').IsFO := by
    rintro (⟨j, i⟩ | (⟨j, r⟩ | (j | ⟨⟩))) (⟨j', i'⟩ | (⟨j', r'⟩ | (j' | ⟨⟩))) <;>
      first
        | exact isFO_tr hFO₁ lP lE _ _
        | exact isFO_trZ hFO₁ lP lE _
        | exact isFO_ff
  refine ⟨fun a => ⟨hFO₁.1 a.2, isFO_tr hFO₁ lP lE _ _⟩, ?_, fun a c => isFO_tr hFO₁ lP lE _ _,
    ?_, fun a b => hord (Sum.inl a) (Sum.inl b), fun a b => hord (Sum.inl a) (Sum.inr b),
    fun a b => hord (Sum.inr a) (Sum.inl b), fun a b => hord (Sum.inr a) (Sum.inr b)⟩
  · rintro (⟨j, r⟩ | (j | ⟨⟩))
    · exact ⟨isFO_atZeroF (hFO₁.2.1 r), isFO_tr hFO₁ lP lE _ _⟩
    · exact isFO_trZ hFO₁ lP lE _
    · exact isFO_ff
  · rintro (⟨j, r⟩ | (j | ⟨⟩)) c
    · exact isFO_tr hFO₁ lP lE _ _
    · exact isFO_trZ hFO₁ lP lE _
    · exact isFO_ff

variable (hFO₁ : T₁.AllFO) (hFO₂ : T₂.AllFO) (hP₁ : T₁.Proper) (hP₂ : T₂.Proper)
  (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE)

include hFO₁ hFO₂ hP₁ hP₂ hlP hlE

lemma proper_comp {f : List A → List B} (hf : ∀ w, T₁.Outputs w (f w)) :
    (comp T₁ T₂ lP lE).Proper := by
  intro w
  obtain ⟨es₁, H₁⟩ := ITrans.exists_enum (hf w)
  set v := f w with hv
  obtain ⟨hlab₂, hrefl₂, hanti₂, htrans₂, htot₂⟩ := hP₂ v
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
    obtain ⟨c, hc, hu⟩ := hlab₂ x hx
    exact ⟨c, (labRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx c).2 hc,
      fun c' hc' => hu c' ((labRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx c').1 hc')⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
    exact (ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx hx).2 (hrefl₂ x hx)
  · intro z z' hz hz' h h'
    obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
    obtain ⟨y, hy, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz'
    rw [hanti₂ x y hx hy ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx hy).1 h)
      ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hy hx).1 h')]
  · intro z z' z'' hz hz' hz'' h h'
    obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
    obtain ⟨y, hy, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz'
    obtain ⟨z₃, hz₃, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz''
    exact (ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx hz₃).2
      (htrans₂ x y z₃ hx hy hz₃ ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx hy).1 h)
        ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hy hz₃).1 h'))
  · intro z z' hz hz'
    obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
    obtain ⟨y, hy, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz'
    rcases htot₂ x y hx hy with h | h
    · exact Or.inl ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hx hy).2 h)
    · exact Or.inr ((ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hy hx).2 h)

omit hP₂ in
lemma outputs_comp {f : List A → List B} {g : List B → List C}
    (hf : ∀ w, T₁.Outputs w (f w)) (hg : ∀ v, T₂.Outputs v (g v)) (w : List A) :
    (comp T₁ T₂ lP lE).Outputs w (g (f w)) := by
  obtain ⟨es₁, H₁⟩ := ITrans.exists_enum (hf w)
  obtain ⟨es₂, H₂⟩ := ITrans.exists_enum (hg (f w))
  refine ⟨es₂.map (phi T₁ T₂ lP lE es₁), ?_, ?_, ?_, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ H₂.nodup
    intro x hx y hy h
    exact phi_injOn H₁ ((H₂.mem_iff x).1 hx) ((H₂.mem_iff y).1 hy) h
  · intro z
    rw [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (selected_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE x).2 ((H₂.mem_iff x).1 hx)
    · intro hz
      obtain ⟨x, hx, rfl⟩ := exists_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE hz
      exact ⟨x, (H₂.mem_iff x).2 hx, rfl⟩
  · intro i j hi hj hij
    simp only [List.get_eq_getElem, List.getElem_map]
    simp only [List.length_map] at hi hj
    exact (ordRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE (H₂.selected_getElem hi)
      (H₂.selected_getElem hj)).2 (H₂.ord i j hi hj hij)
  · rw [List.length_map]; exact H₂.length
  · intro i hi hi'
    simp only [List.get_eq_getElem, List.getElem_map]
    simp only [List.length_map] at hi
    exact (labRel_phi hFO₁ hFO₂ hP₁ H₁ hlP hlE (H₂.selected_getElem hi) _).2 (H₂.lab i hi hi')

end Main

end FOTr

/-- **First-order transductions are closed under composition.**  This is the
step "first-order transductions are closed under composition, which is proved by
substituting formulas" of the proof that the book sketches for
Theorem `nolabel:thm-fo-transduction-into-primes`. -/
theorem isFOTransduction_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsFOTransduction f) (hg : IsFOTransduction g) : IsFOTransduction (g ∘ f) := by
  classical
  obtain ⟨T₁, hP₁, hFO₁, hO₁⟩ := exists_itrans_of_isFOTransduction hf
  obtain ⟨T₂, hP₂, hFO₂, hO₂⟩ := exists_itrans_of_isFOTransduction hg
  haveI := T₁.finP
  haveI := T₁.finE
  haveI : Fintype T₁.P := Fintype.ofFinite _
  haveI : Fintype T₁.E := Fintype.ofFinite _
  refine (FOTr.comp T₁ T₂ (Finset.univ.toList) (Finset.univ.toList)).isFOTransduction
    (FOTr.proper_comp hFO₁ hFO₂ hP₁ hP₂ ?_ ?_ hO₁) (FOTr.allFO_comp hFO₁) ?_
  · intro i; rw [Finset.mem_toList]; exact Finset.mem_univ i
  · intro r; rw [Finset.mem_toList]; exact Finset.mem_univ r
  · intro w
    exact FOTr.outputs_comp hFO₁ hFO₂ hP₁ (fun i => by rw [Finset.mem_toList]; exact Finset.mem_univ i)
      (fun r => by rw [Finset.mem_toList]; exact Finset.mem_univ r) hO₁ hO₂ w

end Lax314295Proofs.Transducers
