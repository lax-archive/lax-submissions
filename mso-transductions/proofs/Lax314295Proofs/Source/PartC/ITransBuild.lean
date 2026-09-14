/-
Building first-order transductions.

This file collects the elementary tools that are used to exhibit concrete
functions as first-order transductions (Definition `def:mso-transduction` together with the
first-orderness requirement):

* `Transducers.ITrans.outputs_of_pairwise`, which reduces the semantic
  condition `ITrans.Outputs` to the existence of a list of output elements that
  is nodup, enumerates exactly the selected elements, is `Pairwise`-ordered by
  the order relation and carries the right labels;
* `Transducers.isFOTransduction_map_equiv`, saying that a letter-to-letter
  renaming along a bijection of alphabets is a first-order transduction, and
  its corollary `Transducers.isFOTransduction_id`.

These are used in `RequestProject/PartC/FORelabTrans.lean`,
`RequestProject/PartC/FOTransRev.lean` and
`RequestProject/PartC/FOTransDup.lean`.
-/
import Lax314295Proofs.Source.PartC.ITrans
import Lax314295Proofs.Source.PartC.FOPlug
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-! ## Two list lemmas -/

/-- `Forall₂` is compatible with concatenation. -/
lemma forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  intro l₁ l₂ m₁ m₂ h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons hx _ ih => exact List.Forall₂.cons hx ih

/-- `Forall₂` passes to `flatMap`. -/
lemma forall₂_flatMap {α β γ : Type} {R : β → γ → Prop} :
    ∀ (l : List α) {F : α → List β} {G : α → List γ},
      (∀ x ∈ l, List.Forall₂ R (F x) (G x)) → List.Forall₂ R (l.flatMap F) (l.flatMap G) := by
  intro l
  induction l with
  | nil => intro F G _; exact List.Forall₂.nil
  | cons x l ih =>
      intro F G h
      rw [List.flatMap_cons, List.flatMap_cons]
      exact forall₂_append (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

namespace ITrans

variable {A B : Type}

/-- To establish `T.Outputs w v` it suffices to give a list of elements that is
nodup, enumerates exactly the selected elements, is pairwise ordered and has the
right labels. -/
lemma outputs_of_pairwise (T : ITrans A B) {w : List A} {v : List B} (es : List T.Elt)
    (hnd : es.Nodup) (hmem : ∀ x, x ∈ es ↔ T.selected w x)
    (hord : es.Pairwise (T.ordRel w)) (hlen : es.length = v.length)
    (hlab : ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length), T.labRel w es[i] v[i]) :
    T.Outputs w v :=
  ⟨es, hnd, hmem, fun i j hi hj hij => List.pairwise_iff_getElem.1 hord i j hi hj hij, hlen,
    hlab⟩

/-- The variant of `ITrans.outputs_of_pairwise` in which the labelling
condition is given as a `Forall₂`. -/
lemma outputs_of_forall₂ (T : ITrans A B) {w : List A} {v : List B} (es : List T.Elt)
    (hnd : es.Nodup) (hmem : ∀ x, x ∈ es ↔ T.selected w x)
    (hord : es.Pairwise (T.ordRel w)) (hlab : List.Forall₂ (T.labRel w) es v) :
    T.Outputs w v := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hlab
  exact T.outputs_of_pairwise es hnd hmem hord hlen (fun i hi hi' => hget i hi hi')

end ITrans

/-! ## Letter-to-letter renamings -/

/-- The transduction that renames every letter along a bijection of alphabets:
one copy of every position, kept in the same order, relabelled by `e`. -/
def mapEquivTrans {A B : Type} (e : A ≃ B) : ITrans A B where
  P := Unit
  E := Empty
  finP := inferInstance
  finE := inferInstance
  univP := fun _ => MSO.tt
  univC := fun j => j.elim
  labP := fun _ b => MSO.lab (e.symm b) 0
  labC := fun j _ => j.elim
  ordPP := fun _ _ => MSO.le 0 1
  ordPC := fun _ j => j.elim
  ordCP := fun j _ => j.elim
  ordCC := fun j _ => j.elim

namespace mapEquivTrans

variable {A B : Type} (e : A ≃ B)

lemma selected_iff (w : List A) (p : ℕ) :
    (mapEquivTrans e).selected w (Sum.inl ((), p)) ↔ p < w.length := by
  simp [ITrans.selected, mapEquivTrans, MSO.tt, MSO.Sat]

lemma ordRel_iff (w : List A) (p q : ℕ) :
    (mapEquivTrans e).ordRel w (Sum.inl ((), p)) (Sum.inl ((), q)) ↔ p ≤ q := by
  simp [ITrans.ordRel, mapEquivTrans, MSO.Sat]

lemma labRel_iff (w : List A) (p : ℕ) (b : B) :
    (mapEquivTrans e).labRel w (Sum.inl ((), p)) b ↔ w[p]? = some (e.symm b) := by
  simp [ITrans.labRel, mapEquivTrans, MSO.Sat]

lemma proper : (mapEquivTrans e).Proper := by
  intro w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨⟨⟩, p⟩ | j) hx
    · rw [selected_iff] at hx
      refine ⟨e w[p], ?_, ?_⟩
      · show (mapEquivTrans e).labRel w (Sum.inl ((), p)) (e w[p])
        rw [labRel_iff]
        simp [List.getElem?_eq_getElem hx]
      · intro b hb
        rw [labRel_iff] at hb
        rw [List.getElem?_eq_getElem hx] at hb
        have : w[p] = e.symm b := by simpa using hb
        rw [this, Equiv.apply_symm_apply]
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) _
    · rw [ordRel_iff]
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') _ _ h₁ h₂
    · rw [ordRel_iff] at h₁ h₂
      have : p = q := le_antisymm h₁ h₂
      simp [this]
    · exact j'.elim
    · exact j.elim
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') (⟨⟨⟩, r⟩ | j'') _ _ _ h₁ h₂ <;>
      first
        | (rw [ordRel_iff] at h₁ h₂ ⊢; exact le_trans h₁ h₂)
        | (first | exact j.elim | exact j'.elim | exact j''.elim)
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') _ _
    · rw [ordRel_iff, ordRel_iff]
      exact le_total p q
    · exact j'.elim
    · exact j.elim
    · exact j.elim

lemma allFO : (mapEquivTrans e).AllFO := by
  refine ⟨fun _ => ?_, fun j => j.elim, fun _ _ => ?_, fun j _ => j.elim, fun _ _ => ?_,
    fun _ j => j.elim, fun j _ => j.elim, fun j _ => j.elim⟩ <;> trivial

lemma outputs (w : List A) : (mapEquivTrans e).Outputs w (w.map e) := by
  refine (mapEquivTrans e).outputs_of_pairwise
    ((List.range w.length).map (fun p => Sum.inl ((), p))) ?_ ?_ ?_ ?_ ?_
  · refine List.Nodup.map ?_ (List.nodup_range)
    intro p q h
    simpa using h
  · rintro (⟨⟨⟩, p⟩ | j)
    · rw [selected_iff]
      simp
    · exact j.elim
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := w.length))
    intro p q h
    rw [ordRel_iff]
    exact h.le
  · simp
  · intro i hi hi'
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    rw [labRel_iff]
    simp [List.getElem?_eq_getElem hi]

end mapEquivTrans

/-- **A letter-to-letter renaming along a bijection is a first-order
transduction.** -/
theorem isFOTransduction_map_equiv {A B : Type} (e : A ≃ B) :
    IsFOTransduction (fun w : List A => w.map e) :=
  (mapEquivTrans e).isFOTransduction (mapEquivTrans.proper e) (mapEquivTrans.allFO e)
    (mapEquivTrans.outputs e)

/-- The identity is a first-order transduction. -/
theorem isFOTransduction_id (A : Type) : IsFOTransduction (id : List A → List A) := by
  have h := isFOTransduction_map_equiv (Equiv.refl A)
  simpa using h

end Lax314295Proofs.Transducers
