import Lax185574Proofs.FarRam.Costs


/-!
The inputs of the rounds of the far-tree program are of size quadratic in
the size of the input of the program.
-/

namespace Lax185574Proofs.FarRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.PartialGraphs Lax185574Proofs.EvalRam

theorem maxEntry_le_of {u : List ℕ} {b : ℕ} (h : ∀ y ∈ u, y ≤ b) : maxEntry u ≤ b := by
  by_cases hu : u = []
  · subst hu; simp [maxEntry]
  · exact h _ (maxEntry_mem hu)

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)
  (S : List (List ℕ))

/-- The size parameter of an input `x`: its length plus its largest entry plus one. -/
def ySz (x : List ℕ) : ℕ := x.length + maxEntry x + 1

theorem gbnd_zero (x : List ℕ) (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) ++ toWord S)
    (B : ℕ) (hB : 1764 * ySz x ^ 4 ≤ B) :
    GBnd 0 x.length k (node G k (q + 1) u) [] S [0] S.length 0 B := by
  refine ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  set Y := ySz x
  have hlen : (gIn 0 x.length k (node G k (q + 1) u) [] S [0]).length = x.length + 3 := by
    simp [gIn, hx]; omega
  have hme : maxEntry (gIn 0 x.length k (node G k (q + 1) u) [] S [0]) ≤ Y := by
    apply maxEntry_le_of
    intro y hy
    have hy' : y = 0 ∨ y = x.length ∨ y ∈ x := by
      simp only [gIn, hx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto
    rcases hy' with rfl | rfl | h
    · omega
    · simp only [Y, ySz]; omega
    · have := le_maxEntry h; simp only [Y, ySz]; omega
  have hY : x.length + 1 ≤ Y := by simp only [Y, ySz]; omega
  have h1 : (gIn 0 x.length k (node G k (q + 1) u) [] S [0]).length +
      maxEntry (gIn 0 x.length k (node G k (q + 1) u) [] S [0]) + 10 ≤ 42 * Y ^ 2 := by
    rw [hlen]; nlinarith
  calc _ ≤ (42 * Y ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 1764 * Y ^ 4 := by ring
    _ ≤ B := hB

theorem gbnd_succ (x : List ℕ) (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) ++ toWord S)
    (B : ℕ) (hB : 1764 * ySz x ^ 4 ≤ B) (j : ℕ) (hj : j < (Node.exts (node G k (q + 1) u)).words.length) :
    GBnd 1 (4 + (wl k (node G k (q + 1) u) S j).length + total (wl k (node G k (q + 1) u) S j)) k
      (node G k (q + 1) u) [0, j + 1, S.length] (wl k (node G k (q + 1) u) S (j + 1)) [] S.length (j + 1) B := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
  set Y := ySz x
  have hM : ∀ v ∈ [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u), v ≤ maxEntry x :=
    fun v hv => le_maxEntry (by rw [hx]; exact List.mem_append_left _ hv)
  have hMS : ∀ v ∈ toWord S, v ≤ maxEntry x := fun v hv => le_maxEntry (by rw [hx]; simp [hv])
  have hN : x.length = 3 + (toWord (node G k (q + 1) u)).length + (toWord S).length := by rw [hx]; simp; omega
  have hR : (Node.exts (node G k (q + 1) u)).words.length ≤ (toWord (node G k (q + 1) u)).length := by
    have := length_toWord_words (Node.exts (node G k (q + 1) u)).words
    rw [toWord_node_succ, List.length_append]; omega
  have hSl := length_toWord_words S
  obtain ⟨hw1, hw2⟩ := wl_bound G k q u (maxEntry x) hM S (j + 1)
  obtain ⟨hw1', hw2'⟩ := wl_bound G k q u (maxEntry x) hM S j
  have hWt := length_toWord_words (wl k (node G k (q + 1) u) S (j + 1))
  have hY : x.length + maxEntry x + 1 = Y := rfl
  have hjt : (j + 1) * ((toWord (node G k (q + 1) u)).length + 3) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hjt' : j * ((toWord (node G k (q + 1) u)).length + 3) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hlen : (gIn 1 (4 + (wl k (node G k (q + 1) u) S j).length + total (wl k (node G k (q + 1) u) S j)) k (node G k (q + 1) u) [0, j + 1, S.length]
      (wl k (node G k (q + 1) u) S (j + 1)) []).length ≤ 15 * (Y * Y) := by
    simp only [gIn, List.length_append, List.length_cons, List.length_nil]
    have : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hme : maxEntry (gIn 1 (4 + (wl k (node G k (q + 1) u) S j).length + total (wl k (node G k (q + 1) u) S j)) k (node G k (q + 1) u) [0, j + 1, S.length]
      (wl k (node G k (q + 1) u) S (j + 1)) []) ≤ 15 * (Y * Y) := by
    apply maxEntry_le_of
    intro y hy
    have : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
    simp only [gIn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.append_nil] at hy
    rcases hy with ((((h | h | h | h | h) | h) | (h | h | h)) | h)
    · omega
    · omega
    · have := hM k (by simp); omega
    · have := hM (q + 1) (by simp); omega
    · have := hM ℓ (by simp); omega
    · have := hM y (by simp [h]); omega
    · omega
    · omega
    · omega
    · have := wl_entries G k q u (maxEntry x) hM S hMS (j + 1) y h; omega
  have h1 : (gIn 1 (4 + (wl k (node G k (q + 1) u) S j).length + total (wl k (node G k (q + 1) u) S j)) k (node G k (q + 1) u) [0, j + 1, S.length]
      (wl k (node G k (q + 1) u) S (j + 1)) []).length + maxEntry (gIn 1 (4 + (wl k (node G k (q + 1) u) S j).length + total (wl k (node G k (q + 1) u) S j)) k (node G k (q + 1) u)
        [0, j + 1, S.length] (wl k (node G k (q + 1) u) S (j + 1)) []) + 10 ≤ 42 * Y ^ 2 := by
    have hY1 : 1 ≤ Y := by simp only [Y, ySz]; omega
    have : 1 ≤ Y * Y := Nat.mul_le_mul hY1 hY1
    rw [sq]; omega
  calc _ ≤ (42 * Y ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 1764 * Y ^ 4 := by ring
    _ ≤ B := hB

end Lax185574Proofs.FarRam
