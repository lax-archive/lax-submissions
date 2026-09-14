/-
The output of an mso transduction, read as an ordered enumeration.

`ITrans.Outputs T w v` says that there is a list `es` of elements that
enumerates, without repetitions and in the order given by the order formulas,
the elements selected by the universe formulas, and that `v` is the
corresponding sequence of letters.  Together with the requirements of
Definition `def:mso-transduction` (`ITrans.Proper`) this makes `q ↦ es[q]` an *isomorphism*
between the positions of `v` and the selected elements ordered by the order
formulas.  This file records that fact in the form in which the backwards
translation of `RequestProject/PartC/FOTransTr.lean` uses it:

* `Enum.ord_iff_le`: `es[q]` precedes `es[q']` if and only if `q ≤ q'`;
* `Enum.lab_iff`: the letter of `v` at the position `q` is the unique letter
  that the letter formulas give to `es[q]`;
* `Enum.exists_index`: every selected element occurs in `es`.
-/
import Lax314295Proofs.Source.PartC.ITrans
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace ITrans

variable {A B : Type}

/-- The data extracted from `T.Outputs w v`: the enumeration `es` of the
selected elements, in the order given by the order formulas. -/
structure Enum (T : ITrans A B) (w : List A) (v : List B) (es : List T.Elt) : Prop where
  /-- The enumeration has no repetitions. -/
  nodup : es.Nodup
  /-- The enumeration lists exactly the selected elements. -/
  mem_iff : ∀ x, x ∈ es ↔ T.selected w x
  /-- The enumeration is increasing for the order formulas. -/
  ord : ∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
    i < j → T.ordRel w es[i] es[j]
  /-- The enumeration has the length of the output string. -/
  length : es.length = v.length
  /-- The letters of the output string are the ones given by the letter
  formulas. -/
  lab : ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length), T.labRel w es[i] v[i]

lemma exists_enum {T : ITrans A B} {w : List A} {v : List B} (h : T.Outputs w v) :
    ∃ es : List T.Elt, Enum T w v es := by
  obtain ⟨es, hnd, hmem, hord, hlen, hlab⟩ := h
  exact ⟨es, hnd, hmem, hord, hlen, hlab⟩

namespace Enum

variable {T : ITrans A B} {w : List A} {v : List B} {es : List T.Elt}

lemma selected_getElem (H : Enum T w v es) {q : ℕ} (hq : q < es.length) :
    T.selected w es[q] :=
  (H.mem_iff _).1 (List.getElem_mem hq)

lemma lt_length_of_getElem_inl (H : Enum T w v es) {q : ℕ} (hq : q < es.length)
    {i : T.P} {p : ℕ} (h : es[q] = Sum.inl (i, p)) : p < w.length := by
  have := H.selected_getElem hq
  rw [h] at this
  exact this.1

lemma exists_index (H : Enum T w v es) {x : T.Elt} (hx : T.selected w x) :
    ∃ q, ∃ hq : q < es.length, es[q] = x := by
  obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem ((H.mem_iff x).2 hx)
  exact ⟨q, hq, hqe⟩

lemma index_unique (H : Enum T w v es) {q q' : ℕ} (hq : q < es.length) (hq' : q' < es.length)
    (h : es[q] = es[q']) : q = q' :=
  (List.Nodup.getElem_inj_iff H.nodup).1 h

lemma ord_iff_le (H : Enum T w v es) (hP : T.Proper) {q q' : ℕ} (hq : q < es.length)
    (hq' : q' < es.length) : T.ordRel w es[q] es[q'] ↔ q ≤ q' := by
  obtain ⟨-, hrefl, hanti, -, -⟩ := hP w
  constructor
  · intro h
    by_contra hlt
    have hlt' : q' < q := by omega
    have h2 := H.ord q' q hq' hq hlt'
    have := hanti _ _ (H.selected_getElem hq) (H.selected_getElem hq') h h2
    exact absurd (H.index_unique hq hq' this) (by omega)
  · intro h
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact hrefl _ (H.selected_getElem hq)
    · exact H.ord q q' hq hq' hlt

lemma lab_iff (H : Enum T w v es) (hP : T.Proper) {q : ℕ} (hq : q < es.length)
    (hq' : q < v.length) (b : B) : T.labRel w es[q] b ↔ v[q] = b := by
  obtain ⟨hlab, -⟩ := hP w
  obtain ⟨c, -, hu⟩ := hlab _ (H.selected_getElem hq)
  constructor
  · intro h
    exact (hu v[q] (H.lab q hq hq')).trans (hu b h).symm
  · rintro rfl
    exact H.lab q hq hq'

lemma getElem?_eq (H : Enum T w v es) (hP : T.Proper) {q : ℕ} (hq : q < es.length) (b : B) :
    T.labRel w es[q] b ↔ v[q]? = some b := by
  have hq' : q < v.length := by rw [← H.length]; exact hq
  rw [H.lab_iff hP hq hq' b, List.getElem?_eq_getElem hq']
  simp

/-- The first element of the enumeration is the least selected element. -/
lemma min_zero (H : Enum T w v es) (hP : T.Proper) {x : T.Elt} (hx : T.selected w x)
    (h0 : 0 < es.length) : T.ordRel w es[0] x := by
  obtain ⟨q, hq, rfl⟩ := H.exists_index hx
  exact (H.ord_iff_le hP h0 hq).2 (Nat.zero_le _)

/-- A selected element that precedes every selected element is the first
element of the enumeration. -/
lemma eq_zero_of_min (H : Enum T w v es) (hP : T.Proper) {x : T.Elt} (hx : T.selected w x)
    (hmin : ∀ y, T.selected w y → T.ordRel w x y) (h0 : 0 < es.length) : x = es[0] := by
  obtain ⟨-, -, hanti, -, -⟩ := hP w
  exact hanti _ _ hx (H.selected_getElem h0) (hmin _ (H.selected_getElem h0))
    (H.min_zero hP hx h0)

lemma nil_of_no_selected (H : Enum T w v es) (h : ∀ x, ¬ T.selected w x) : es = [] := by
  by_contra h'
  have h0 : 0 < es.length :=
    Nat.pos_of_ne_zero (fun hz => h' (List.length_eq_zero_iff.mp hz))
  exact h _ (H.selected_getElem h0)

lemma v_eq_nil_of_no_selected (H : Enum T w v es) (h : ∀ x, ¬ T.selected w x) : v = [] := by
  have hl := H.length
  rw [H.nil_of_no_selected h] at hl
  exact List.length_eq_zero_iff.mp hl.symm

end Enum

end ITrans
end Lax314295Proofs.Transducers
