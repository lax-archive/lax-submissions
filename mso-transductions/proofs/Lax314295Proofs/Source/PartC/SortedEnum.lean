/-
Sorted enumerations of a finite linear order.

The semantics of an mso transduction (Definition `def:mso-transduction`) presents the output
string through *some* list of the selected elements which is strictly increasing
for the order formula.  The two-way transducer of
`RequestProject/PartC/WalkAut.lean` walks that list by repeatedly asking for the
minimum, the maximum and the successor of an element.  This file contains the
elementary order-theoretic dictionary between the two presentations.
-/
import Mathlib

namespace Lax314295Proofs.Transducers

namespace SortedEnum

variable {E : Type}

/-- The list `es` enumerates, without repetitions and in increasing order, a set
of elements on which `Le` is a linear order. -/
structure Spec (Le : E → E → Prop) (es : List E) : Prop where
  /-- No repetitions. -/
  nodup : es.Nodup
  /-- The list is increasing. -/
  sorted : ∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length), i < j → Le es[i] es[j]
  /-- Reflexivity on the enumerated elements. -/
  refl : ∀ x ∈ es, Le x x
  /-- Antisymmetry on the enumerated elements. -/
  antisymm : ∀ x ∈ es, ∀ y ∈ es, Le x y → Le y x → x = y
  /-- Totality on the enumerated elements. -/
  total : ∀ x ∈ es, ∀ y ∈ es, Le x y ∨ Le y x

variable {Le : E → E → Prop} {es : List E}

lemma mem_index {x : E} (hx : x ∈ es) : ∃ m, ∃ hm : m < es.length, es[m] = x := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem.1 hx
  exact ⟨m, hm⟩

lemma le_of_index_le (h : Spec Le es) {i j : ℕ} (hi : i < es.length) (hj : j < es.length)
    (hij : i ≤ j) : Le es[i] es[j] := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact h.sorted i j hi hj hlt
  · subst heq
    exact h.refl _ (List.getElem_mem hi)

lemma not_le_of_index_lt (h : Spec Le es) {i j : ℕ} (hi : i < es.length) (hj : j < es.length)
    (hij : i < j) : ¬ Le es[j] es[i] := by
  intro hle
  have h1 : Le es[i] es[j] := h.sorted i j hi hj hij
  have := h.antisymm _ (List.getElem_mem hi) _ (List.getElem_mem hj) h1 hle
  exact absurd (h.nodup.getElem_inj_iff.1 this) (by omega)

lemma not_le_iff (h : Spec Le es) {i j : ℕ} (hi : i < es.length) (hj : j < es.length) :
    (¬ Le es[j] es[i]) ↔ i < j := by
  constructor
  · intro hn
    by_contra hc
    exact hn (le_of_index_le h hj hi (by omega))
  · exact not_le_of_index_lt h hi hj

lemma isMax_iff (h : Spec Le es) {r : ℕ} (hr : r < es.length) :
    (∀ x ∈ es, Le x es[r]) ↔ r + 1 = es.length := by
  constructor
  · intro hmax
    by_contra hc
    have hr1 : r + 1 < es.length := by omega
    exact not_le_of_index_lt h hr hr1 (by omega) (hmax _ (List.getElem_mem hr1))
  · intro hlast x hx
    obtain ⟨m, hm, rfl⟩ := mem_index hx
    exact le_of_index_le h hm hr (by omega)

lemma isMin_iff (h : Spec Le es) {r : ℕ} (hr : r < es.length) :
    (∀ x ∈ es, Le es[r] x) ↔ r = 0 := by
  constructor
  · intro hmin
    by_contra hc
    have h0 : 0 < es.length := by omega
    exact not_le_of_index_lt h h0 hr (by omega) (hmin _ (List.getElem_mem h0))
  · rintro rfl x hx
    obtain ⟨m, hm, rfl⟩ := mem_index hx
    exact le_of_index_le h hr hm (by omega)

lemma succ_iff (h : Spec Le es) {r s : ℕ} (hr : r < es.length) (hs : s < es.length) :
    (¬ Le es[s] es[r] ∧ ∀ z ∈ es, ¬ (¬ Le z es[r] ∧ ¬ Le es[s] z)) ↔ s = r + 1 := by
  rw [not_le_iff h hr hs]
  constructor
  · rintro ⟨hlt, hno⟩
    by_contra hc
    have hr1 : r + 1 < es.length := by omega
    have hlt' : r + 1 < s := by omega
    refine hno _ (List.getElem_mem hr1) ⟨?_, ?_⟩
    · rw [not_le_iff h hr hr1]
      omega
    · rw [not_le_iff h hr1 hs]
      omega
  · rintro rfl
    refine ⟨by omega, ?_⟩
    intro z hz
    obtain ⟨m, hm, rfl⟩ := mem_index hz
    rintro ⟨h1, h2⟩
    rw [not_le_iff h hr hm] at h1
    rw [not_le_iff h hm hs] at h2
    omega

end SortedEnum

end Lax314295Proofs.Transducers
