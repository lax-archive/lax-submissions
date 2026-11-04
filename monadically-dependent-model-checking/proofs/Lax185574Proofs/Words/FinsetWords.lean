import Lax185574Proofs.Words.Read
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
The words of finite sets of vertices and of graphs on `Fin n`.

A finite set of vertices is encoded by its size followed by the frames
`1, u` of its elements in increasing order. A graph on `Fin n` is
encoded by `n` followed by the words of the neighborhoods of the
vertices in order.
-/

namespace Lax185574Proofs.Words

open Lax185574.WordEncoding

/-- The entries of the word of a finite set after its size. -/
def elemFrames (us : List ℕ) : List ℕ := us.flatMap fun u => [1, u]

theorem elemFrames_cons (u : ℕ) (us : List ℕ) : elemFrames (u :: us) = 1 :: u :: elemFrames us := by
  simp [elemFrames]

theorem elemFrames_append (us vs : List ℕ) :
    elemFrames (us ++ vs) = elemFrames us ++ elemFrames vs := by
  simp [elemFrames]

theorem length_elemFrames (us : List ℕ) : (elemFrames us).length = 2 * us.length := by
  induction us with
  | nil => rfl
  | cons a us ih => rw [elemFrames_cons]; simp [ih]; ring

/-- The elements of a finite set of vertices in increasing order. -/
def sortedVals {n : ℕ} (A : Finset (Fin n)) : List ℕ := (A.sort (· ≤ ·)).map Fin.val

theorem sortedVals_pairwise {n : ℕ} (A : Finset (Fin n)) : (sortedVals A).Pairwise (· < ·) := by
  unfold sortedVals
  rw [List.pairwise_map]
  exact (Finset.sortedLT_sort A).pairwise

theorem mem_sortedVals {n : ℕ} {A : Finset (Fin n)} {u : ℕ} :
    u ∈ sortedVals A ↔ ∃ h : u < n, (⟨u, h⟩ : Fin n) ∈ A := by
  unfold sortedVals
  simp only [List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v.2, hv⟩
  · rintro ⟨h, hu⟩; exact ⟨_, hu, rfl⟩

theorem length_sortedVals {n : ℕ} (A : Finset (Fin n)) : (sortedVals A).length = A.card := by
  simp [sortedVals]

theorem sortedVals_lt {n : ℕ} {A : Finset (Fin n)} {u : ℕ} (h : u ∈ sortedVals A) : u < n := by
  obtain ⟨h, -⟩ := mem_sortedVals.mp h; exact h

theorem singleton_lt_singleton {a b : ℕ} : [a] < [b] ↔ a < b := by
  rw [List.cons_lt_cons_iff]
  simp

/-- **The word of a finite set of vertices.** -/
theorem toWord_finset_fin {n : ℕ} (A : Finset (Fin n)) :
    toWord A = A.card :: elemFrames (sortedVals A) := by
  have hL : Finset.words A = (sortedVals A).map fun u => [u] := by
    unfold Finset.words
    have hnd : ((sortedVals A).map fun u => [u]).Nodup :=
      (List.nodup_map_iff (fun a b h => by simpa using h)).mpr
        ((sortedVals_pairwise A).imp (fun h => ne_of_lt h))
    have hpw : ((sortedVals A).map fun u => [u]).Pairwise (· ≤ ·) := by
      rw [List.pairwise_map]
      exact (sortedVals_pairwise A).imp fun h => le_of_lt (singleton_lt_singleton.mpr h)
    have hset : A.image toWord = ((sortedVals A).map fun u => [u]).toFinset := by
      ext w
      simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, mem_sortedVals]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨v.val, ⟨v.2, hv⟩, rfl⟩
      · rintro ⟨u, ⟨h, hu⟩, rfl⟩; exact ⟨_, hu, rfl⟩
    rw [hset]
    exact (List.toFinset_sort (· ≤ ·) hnd).mpr hpw
  change toWord (Finset.words A) = _
  rw [toWord_words, hL]
  simp only [List.length_map, length_sortedVals, frames, List.map_map]
  congr 1

end Lax185574Proofs.Words
