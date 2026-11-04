import Lax185574Proofs.FarRam.Rounds


/-!
Sizes along the script of the far-tree program: the answers, the word
lists read in the rounds, and the output.
-/

namespace Lax185574Proofs.FarRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.PartialGraphs Lax185574Proofs.EvalRam

theorem mem_toWord_words_cases {ws : List (List ℕ)} {v : ℕ} (hv : v ∈ toWord ws) :
    v = ws.length ∨ (∃ w ∈ ws, v = w.length) ∨ (∃ w ∈ ws, v ∈ w) := by
  rw [toWord_words] at hv
  rcases List.mem_cons.mp hv with h | h
  · exact Or.inl h
  · simp only [frames, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨w, hw, rfl⟩, hv'⟩ := h
    rcases List.mem_cons.mp hv' with h' | h'
    · exact Or.inr (Or.inl ⟨w, hw, h'⟩)
    · exact Or.inr (Or.inr ⟨w, hw, h'⟩)

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)

/-- **The answers are small.** -/
theorem ansW_bound (M : ℕ) (hM : ∀ v ∈ [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u), v ≤ M) (j : ℕ) :
    (ansW k (node G k (q + 1) u) j).length ≤ (toWord (node G k (q + 1) u)).length + 3 ∧
      ∀ v ∈ ansW k (node G k (q + 1) u) j, v < M + 2 + (toWord (node G k (q + 1) u)).length := by
  by_cases hj : j < (Node.exts (node G k (q + 1) u)).words.length
  · obtain ⟨b, -, ha, hinf⟩ := ans_query G k q u j hj
    rw [ha, last_answer]
    have hl := hinf.length_le
    have hk : k ≤ M := hM k (by simp)
    have hq : q + 1 ≤ M := hM (q + 1) (by simp)
    have hℓ : ℓ ≤ M := hM ℓ (by simp)
    obtain ⟨h1, h2⟩ := answer_bound_last G (k + 1) q u b (M + 2 + (toWord (node G k (q + 1) u)).length)
      (fun v hv => by have := hM v (List.mem_append_right _ (hinf.subset hv)); omega) (by omega) (by omega) (by omega)
      (by omega)
    exact ⟨by omega, h2⟩
  · rw [ansW, dif_neg hj]; simp

theorem wl_bound (M : ℕ) (hM : ∀ v ∈ [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u), v ≤ M)
    (S : List (List ℕ)) (j : ℕ) :
    total (wl k (node G k (q + 1) u) S j) ≤ total S + j * ((toWord (node G k (q + 1) u)).length + 3) ∧
      (wl k (node G k (q + 1) u) S j).length = S.length + j := by
  induction j with
  | zero => simp [wl]
  | succ j ih =>
    rw [wl_succ, total_append, total_singleton, List.length_append]
    have := (ansW_bound G k q u M hM j).1
    refine ⟨by rw [Nat.succ_mul]; omega, by simp [ih.2]; omega⟩

theorem wl_entries (M : ℕ) (hM : ∀ v ∈ [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u), v ≤ M)
    (S : List (List ℕ)) (hMS : ∀ v ∈ toWord S, v ≤ M) (j : ℕ) (v : ℕ)
    (hv : v ∈ toWord (wl k (node G k (q + 1) u) S j)) :
    v ≤ (toWord S).length + j + (toWord (node G k (q + 1) u)).length + M + 3 := by
  have hS := length_toWord_words S
  have hl := (wl_bound G k q u M hM S j).2
  rcases mem_toWord_words_cases hv with h | ⟨w, hw, h⟩ | ⟨w, hw, h⟩
  · omega
  · rcases List.mem_append.mp hw with h' | h'
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h'
      have hle : S[i].length ≤ (toWord S).length := by
        have := off_add_le hi; have := off_le_total S i; omega
      omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h'
      have := (ansW_bound G k q u M hM i).1; omega
  · rcases List.mem_append.mp hw with h' | h'
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h'
      have h2 := (mem_toWord_words hi).2 v h
      have := hMS v h2; omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h'
      have := (ansW_bound G k q u M hM i).2 v h; omega

theorem toWord_filter_map_le (S : List (List ℕ)) (p : List ℕ → Bool) :
    (toWord ((S.filter p).map nuPart)).length ≤ (toWord S).length := by
  rw [length_toWord_words, length_toWord_words]
  suffices h : ∀ S : List (List ℕ), ((S.filter p).map nuPart).length ≤ S.length ∧
      total ((S.filter p).map nuPart) ≤ total S by have := h S; omega
  intro S
  induction S with
  | nil => simp [total]
  | cons w S ih =>
    have hw : (nuPart w).length ≤ w.length := by simp [nuPart]
    by_cases hp : p w = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.length_cons]
      have := total_append [nuPart w] ((S.filter p).map nuPart)
      have := total_append [w] S
      simp only [total_singleton, List.singleton_append] at *
      omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, if_false, List.length_cons]
      have := total_append [w] S
      simp only [total_singleton, List.singleton_append] at *
      omega

end Lax185574Proofs.FarRam
