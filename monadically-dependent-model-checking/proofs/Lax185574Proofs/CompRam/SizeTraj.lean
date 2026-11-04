import Lax185574Proofs.CompRam.SizeRound
import Lax185574Proofs.CompRam.Run

/-!
The sizes along the script of an instance of lem:compose.

The parameters of an instance (`szP`): `Λ = |x|`, `K = k + q + 1`, and
`B0 = max x + |x| + K + 3`. Every state of the trajectory up to its end
is good (`traj_ok`), so the stack, the questions and the answers are
small, and the inputs and outputs of all rounds have length at most
`Lsz` and entries at most `max x + Lsz` (`size_ok`). `count_le_word`:
the number of nodes of a type tree is at most the length of its word,
so the number `m` of calls is at most `5 |x|^(q+1)`.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-! ### Nodes and words -/

theorem sum_words {α : Type*} [WordEncoding α] (S : Finset α)
    (hinj : Set.InjOn (toWord : α → List ℕ) S) (f : List ℕ → ℕ) :
    (S.words.map f).sum = ∑ a ∈ S, f (toWord a) := by
  unfold Finset.words
  have h := (Finset.sort_perm_toList (S.image toWord) (r := (· ≤ ·))).map f
  rw [h.sum_eq, Finset.sum_map_toList, Finset.sum_image hinj]

theorem count_le_word : ∀ {h ℓ : ℕ} (t : Node h ℓ), Node.count t ≤ (toWord t).length
  | 0, ℓ, t => by
    have := count_lt_toWord (Node.atoms t).words
    rw [toWord_node_zero]; simp only [Node.count]; omega
  | h + 1, ℓ, t => by
    rw [toWord_node_succ, List.length_append]
    have h1 := count_lt_toWord (Node.atoms t).words
    have h2 : (toWord (Node.exts t).words).length = 1 + ∑ e ∈ Node.exts t, ((toWord e).length + 1) := by
      rw [length_toWord_words, sum_words _ (fun a _ b _ hab => ext_word_inj hab)]
    have h3 : ∑ e ∈ Node.exts t, Node.count e.2 ≤ ∑ e ∈ Node.exts t, ((toWord e).length + 1) :=
      Finset.sum_le_sum fun e _ => by
        have := count_le_word e.2
        rw [toWord_ext]; simp only [List.length_cons]; omega
    show 1 + ∑ e ∈ t.2, Node.count e.2 ≤ _
    have : Node.exts t = t.2 := rfl
    rw [← this]
    omega

/-! ### The fixed words -/

theorem atL_entries {ℓ R₁ R₂ B : ℕ} (hB : atN ℓ R₁ R₂ < B) (hℓ : ℓ < B) (h1 : R₁ < B) (h2 : R₂ < B)
    (h6 : 6 ≤ B) : ∀ e ∈ toWord (atL ℓ R₁ R₂), e < B := by
  intro e he
  rcases mem_toWord_cases he with rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, he'⟩
  · rw [length_atL]; exact hB
  · rcases mem_atL.1 hc with ⟨i, -, j, -, rfl⟩ | ⟨i, -, rfl⟩ | ⟨r, -, i, -, j, -, rfl⟩ |
      ⟨r, -, -, i, -, rfl⟩ <;> simp <;> omega
  · rcases mem_atL.1 hc with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨r, hr, i, hi, j, hj, rfl⟩ |
      ⟨r, -, hr, i, hi, rfl⟩ <;> simp at he' <;> omega

theorem dSq_lt : ∀ e ∈ dSq, e < 8000 := by
  rw [dSq_eq, toWord_ext_word]
  intro e he
  have a1 := atL_entries (ℓ := 1) (R₁ := 729) (R₂ := 6561) (B := 8000) (by simp [atN]) (by omega)
    (by omega) (by omega) (by omega)
  have a2 := atL_entries (ℓ := 2) (R₁ := 1) (R₂ := 81) (B := 8000) (by simp [atN]) (by omega)
    (by omega) (by omega) (by omega)
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he; omega
    · exact a1 e he
  · rcases List.mem_append.1 he with he | he
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he; omega
    · exact a2 e he

theorem dSa_lt : ∀ e ∈ dSa, e < 8000 := by
  rw [dSa_eq]
  intro e he
  have a1 := atL_entries (ℓ := 1) (R₁ := 1) (R₂ := 81) (B := 8000) (by simp [atN]) (by omega)
    (by omega) (by omega) (by omega)
  rcases List.mem_append.1 he with he | he
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he; omega
  · exact a1 e he

theorem length_dSa_le : dSa.length ≤ 40000 := by rw [length_dSa]; omega

end Lax185574Proofs.CompRam
