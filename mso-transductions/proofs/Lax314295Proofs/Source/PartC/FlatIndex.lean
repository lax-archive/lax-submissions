/-
Indexing the flattening of a list of lists.

Used in the proof of Theorem `thm:logic-regular-functions` of *Transducers* (M. Bojańczyk): the
output of a two-way transducer is the concatenation of the strings produced by the successive steps
of its run, and the corresponding output positions of the mso transduction are indexed by pairs
(step of the run, position inside the string produced at that step).  This file defines that list of
pairs and proves the four facts about it that are needed: it enumerates the pairs without
repetitions, it is sorted lexicographically, and reading the letters at those pairs gives back the
flattened list. -/
import Lax765601Proofs.Source.Common.Aux
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace FlatIndex

variable {B : Type}

/-- The pairs (index of a list, index inside that list) of a list of lists, in
lexicographic order. -/
def pairs : List (List B) → List (ℕ × ℕ)
  | [] => []
  | l :: L => (List.range l.length).map (fun i => (0, i)) ++
      (pairs L).map (fun ti => (ti.1 + 1, ti.2))

/-- The letter of a list of lists at a pair of indices. -/
def get2 (L : List (List B)) (ti : ℕ × ℕ) : Option B := (L[ti.1]?).bind (fun l => l[ti.2]?)

@[simp] lemma pairs_nil : pairs ([] : List (List B)) = [] := rfl

lemma pairs_cons (l : List B) (L : List (List B)) :
    pairs (l :: L) = (List.range l.length).map (fun i => (0, i)) ++
      (pairs L).map (fun ti => (ti.1 + 1, ti.2)) := rfl

lemma get2_cons_succ (l : List B) (L : List (List B)) (t i : ℕ) :
    get2 (l :: L) (t + 1, i) = get2 L (t, i) := rfl

lemma get2_cons_zero (l : List B) (L : List (List B)) (i : ℕ) :
    get2 (l :: L) (0, i) = l[i]? := rfl

lemma map_range_getElem? (l : List B) :
    (List.range l.length).map (fun i => l[i]?) = l.map some := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj, List.getElem?_eq_getElem hj]
    simp
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
    simp

/-- Reading the letters at the pairs gives back the flattened list. -/
lemma map_get2_pairs (L : List (List B)) :
    (pairs L).map (get2 L) = L.flatten.map some := by
  induction L with
  | nil => simp
  | cons l L ih =>
      rw [pairs_cons, List.map_append, List.flatten_cons, List.map_append, ← ih]
      congr 1
      · rw [List.map_map]
        exact map_range_getElem? l
      · rw [List.map_map]
        apply List.map_congr_left
        rintro ⟨a, b⟩ -
        exact get2_cons_succ l L a b

@[simp] lemma length_pairs (L : List (List B)) : (pairs L).length = L.flatten.length := by
  have h := congrArg List.length (map_get2_pairs L)
  rwa [List.length_map, List.length_map] at h

lemma mem_pairs (L : List (List B)) (t i : ℕ) :
    (t, i) ∈ pairs L ↔ ∃ l, L[t]? = some l ∧ i < l.length := by
  induction L generalizing t with
  | nil => simp
  | cons l L ih =>
      rw [pairs_cons, List.mem_append]
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
      cases t with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, exists_eq_left']
          constructor
          · rintro (⟨i', hi', -, rfl⟩ | ⟨⟨a, b⟩, -, h1, -⟩)
            · exact hi'
            · exact absurd h1 (by omega)
          · intro h
            exact Or.inl ⟨i, h, by simp⟩
      | succ t =>
          simp only [List.getElem?_cons_succ]
          constructor
          · rintro (⟨i', -, h1, -⟩ | ⟨⟨a, b⟩, hab, h1, h2⟩)
            · exact absurd h1 (by omega)
            · simp only at h1 h2
              subst h2
              obtain rfl : a = t := by omega
              exact (ih a).1 hab
          · intro h
            exact Or.inr ⟨(t, i), (ih t).2 h, rfl, rfl⟩

lemma nodup_pairs (L : List (List B)) : (pairs L).Nodup := by
  induction L with
  | nil => simp
  | cons l L ih =>
      rw [pairs_cons]
      refine List.Nodup.append ?_ ?_ ?_
      · refine List.Nodup.map ?_ List.nodup_range
        intro i j h
        simpa using h
      · refine List.Nodup.map ?_ ih
        rintro ⟨a, b⟩ ⟨a', b'⟩ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) h.2
      · rintro ⟨a, b⟩ ha hb
        simp only [List.mem_map, Prod.mk.injEq] at ha hb
        obtain ⟨i, -, h1, -⟩ := ha
        obtain ⟨⟨c, d⟩, -, h2, -⟩ := hb
        omega

/-- The pairs are sorted lexicographically. -/
lemma pairwise_pairs (L : List (List B)) :
    List.Pairwise (fun a b : ℕ × ℕ => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) (pairs L) := by
  induction L with
  | nil => simp
  | cons l L ih =>
      rw [pairs_cons]
      refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
      · refine List.pairwise_map.2 (List.pairwise_lt_range.imp ?_)
        intro i j hij
        exact Or.inr ⟨rfl, hij⟩
      · refine List.pairwise_map.2 ?_
        refine ih.imp ?_
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        rcases hab with h | ⟨h1, h2⟩
        · exact Or.inl (by simpa using h)
        · exact Or.inr ⟨by simpa using h1, h2⟩
      · rintro ⟨a, b⟩ ha ⟨c, d⟩ hb
        simp only [List.mem_map, Prod.mk.injEq] at ha hb
        obtain ⟨i, -, h1, -⟩ := ha
        obtain ⟨⟨e, g⟩, -, h2, -⟩ := hb
        exact Or.inl (by simp only []; omega)

end FlatIndex
end Lax314295Proofs.Transducers
