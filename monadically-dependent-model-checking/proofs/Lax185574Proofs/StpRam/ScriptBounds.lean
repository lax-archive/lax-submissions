import Lax185574Proofs.StpRam.Script

/-!
Sizes of the states, queries and answers of the script of
lem:compute-stp, in terms of `X = |x| + max x + 1`.
-/

namespace Lax185574Proofs.StpRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding

variable {n : ℕ}

theorem total_take_le (ws : List (List ℕ)) (t : ℕ) : total (ws.take t) ≤ total ws := by
  have h : total (ws.take t) + total (ws.drop t) = total ws := by
    rw [← total_append, List.take_append_drop]
  omega

theorem length_toWord_take_le (ws : List (List ℕ)) (t : ℕ) :
    (toWord (ws.take t)).length ≤ (toWord ws).length := by
  rw [length_toWord_words, length_toWord_words]
  have := total_take_le ws t
  have : (ws.take t).length ≤ ws.length := List.length_take_le' _ _
  omega

section
variable {G : PartialGraph (Fin n)} {k q X : ℕ} (hs : Sizes G k q X)
include hs

theorem X_pow : X ≤ X ^ 3 ∧ X ^ 2 ≤ X ^ 3 ∧ 1 ≤ X ^ 2 := by
  have h1 := hs.one
  refine ⟨?_, Nat.pow_le_pow_right h1 (by omega), Nat.one_le_pow _ _ (by omega)⟩
  calc X = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ 3 := Nat.pow_le_pow_right h1 (by omega)

theorem famF_bound : (∀ u ∈ famF G k q, u.length ≤ maxTreeSize G k q) ∧
    ∀ u ∈ famF G k q, ∀ y ∈ u, y + 1 ≤ X := by
  constructor
  · intro u hu
    rw [famF, famW, List.mem_ofFn] at hu
    obtain ⟨v, rfl⟩ := hu
    exact hs.famL v
  · intro u hu y hy
    rw [famF, famW, List.mem_ofFn] at hu
    obtain ⟨v, rfl⟩ := hu
    exact hs.famE v y hy

theorem stS_bound {t : ℕ} (ht : t ≤ q * n) :
    (stS G k q t).length ≤ 11 * X ^ 3 ∧ ∀ y ∈ stS G k q t, y < 4 * X ^ 3 := by
  obtain ⟨hX3, hX23, hX2⟩ := X_pow hs
  have hF := famF_bound hs
  have hFl := length_famF G k q
  have hFw := length_toWord_famF G k q
  have hlen := hs.len
  have hgl : glW G ≤ X := by unfold glW; omega
  have htw := length_toWord_take_le (answers G k q) t
  have hQ := hs.QX
  have hL := hs.LX
  constructor
  · rw [stS, length_stState]
    have := hs.twA
    have := hs.nX
    omega
  · intro y hy
    rw [stS, stState] at hy
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with ((h | h | h | h | h | h) | h) | h
    · omega
    · have := hs.nX; omega
    · have := hs.kX; omega
    · have := hs.qX; omega
    · omega
    · omega
    · refine toWord_words_lt (by have := hs.nX; omega) (fun u hu => ?_) (fun u hu y hy => ?_) y h
      · have := hF.1 u hu; omega
      · have := hF.2 u hu y hy; omega
    · refine toWord_words_lt ?_ (fun u hu => ?_) (fun u hu y hy => ?_) y h
      · have := List.length_take_le t (answers G k q); omega
      · have := hs.ansL u (List.mem_of_mem_take hu); omega
      · have := hs.ansE u (List.mem_of_mem_take hu) y hy; omega

omit hs in
theorem getD_bound {ws : List (List ℕ)} {i L B : ℕ} (hl : ∀ u ∈ ws, u.length ≤ L)
    (he : ∀ u ∈ ws, ∀ y ∈ u, y < B) : (ws.getD i []).length ≤ L ∧ ∀ y ∈ ws.getD i [], y < B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp
  | some u =>
    have hu : u ∈ ws := List.mem_of_getElem? h
    exact ⟨hl u hu, he u hu⟩

theorem qryS_bound (t : ℕ) : (qryS G k q t).length ≤ maxTreeSize G k q ∧
    ∀ y ∈ qryS G k q t, y < 3 * X := by
  have hF := famF_bound hs
  refine getD_bound (fun u hu => ?_) (fun u hu y hy => ?_)
  · rcases List.mem_append.mp hu with h | h
    · exact hF.1 u h
    · exact hs.ansL u h
  · rcases List.mem_append.mp hu with h | h
    · have := hF.2 u h y hy; omega
    · exact hs.ansE u h y hy

theorem ansS_bound (t : ℕ) : (ansS G k q t).length ≤ maxTreeSize G k q ∧
    ∀ y ∈ ansS G k q t, y < 3 * X :=
  getD_bound hs.ansL hs.ansE

end

end Lax185574Proofs.StpRam
