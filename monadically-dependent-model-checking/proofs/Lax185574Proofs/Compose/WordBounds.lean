import Lax185574.Partitions
import Lax185574Proofs.Compose.GraphLength

/-!
Crude bounds on the words of encoded objects: `WB a N` says that the
word of `a` has length at most `N` and entries at most `N`. A program
that receives such a word as input is admissible once the word length
holds a fixed power of `N`.
-/

namespace Lax185574Proofs.Compose

open Lax185574.WordEncoding Lax185574.Partitions

universe u v

/-- The word of `a` has length and entries at most `N`. -/
def WB {α : Type u} [WordEncoding α] (a : α) (N : ℕ) : Prop :=
  (toWord a).length ≤ N ∧ ∀ v ∈ toWord a, v ≤ N

theorem WB.mono {α : Type u} [WordEncoding α] {a : α} {N N' : ℕ} (h : WB a N) (hN : N ≤ N') :
    WB a N' :=
  ⟨h.1.trans hN, fun v hv => (h.2 v hv).trans hN⟩

theorem wb_fin {n : ℕ} (v : Fin n) : WB v (n + 1) := by
  refine ⟨by change 1 ≤ n + 1; omega, fun x hx => ?_⟩
  change x ∈ [v.val] at hx
  simp at hx; omega

theorem wb_prod {α : Type u} {β : Type v} [WordEncoding α] [WordEncoding β] {a : α} {b : β}
    {N N' : ℕ} (ha : WB a N) (hb : WB b N') : WB (a, b) (N + N') := by
  refine ⟨?_, fun x hx => ?_⟩
  · change (toWord a ++ toWord b).length ≤ _
    rw [List.length_append]; exact Nat.add_le_add ha.1 hb.1
  · change x ∈ toWord a ++ toWord b at hx
    rcases List.mem_append.mp hx with h | h
    · exact (ha.2 x h).trans (by omega)
    · exact (hb.2 x h).trans (by omega)

theorem length_flatten_le {α : Type u} [WordEncoding α] {N : ℕ} :
    ∀ l : List α, (∀ a ∈ l, WB a N) → ((l.map toWord).flatten).length ≤ l.length * N
  | [], _ => by simp
  | a :: l, h => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have := length_flatten_le l (fun b hb => h b (List.mem_cons_of_mem _ hb))
      have := (h a List.mem_cons_self).1
      rw [Nat.add_mul, one_mul]; omega

theorem wb_list {α : Type u} [WordEncoding α] {l : List α} {N : ℕ} (h : ∀ a ∈ l, WB a N) :
    WB l ((l.length + 1) * (N + 1)) := by
  refine ⟨?_, fun x hx => ?_⟩
  · change (l.length :: (l.map toWord).flatten).length ≤ _
    rw [List.length_cons]
    have := length_flatten_le l h
    nlinarith
  · change x ∈ l.length :: (l.map toWord).flatten at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · nlinarith
    · simp only [List.mem_flatten, List.mem_map] at hx
      obtain ⟨_, ⟨a, ha, rfl⟩, hxa⟩ := hx
      have := (h a ha).2 x hxa
      nlinarith

theorem wb_listNat {u : List ℕ} {N : ℕ} (hl : u.length ≤ N) (he : ∀ v ∈ u, v ≤ N) :
    WB u (N + 1) := by
  rw [WB, toWord_list_nat]
  refine ⟨by simp; omega, fun x hx => ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact (he x hx).trans (by omega)

theorem wb_finset {α : Type u} [WordEncoding α] {S : Finset α} {N : ℕ} (h : ∀ a ∈ S, WB a N) :
    WB S ((S.card + 1) * (N + 2)) := by
  have hw : ∀ u ∈ Finset.words S, WB u (N + 1) := by
    intro u hu
    simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    exact wb_listNat (h a ha).1 (h a ha).2
  have hl : (Finset.words S).length ≤ S.card := by
    simp only [Finset.words, Finset.length_sort]
    exact Finset.card_image_le
  have := wb_list hw
  exact this.mono (Nat.mul_le_mul (by omega) le_rfl)

theorem wb_fun {α : Type u} [WordEncoding α] {n : ℕ} {f : Fin n → α} {N : ℕ}
    (h : ∀ i, WB (f i) N) : WB f ((n + 1) * (N + 1)) := by
  have := wb_list (l := List.ofFn f) (N := N) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  rw [List.length_ofFn] at this
  exact this

theorem wb_finset_fin {n : ℕ} (S : Finset (Fin n)) : WB S ((n + 1) * (n + 3)) :=
  (wb_finset (fun v _ => wb_fin v)).mono
    (Nat.mul_le_mul (by have := Finset.card_le_univ S; simp at this; omega) le_rfl)

theorem wb_graph {n : ℕ} (G : SimpleGraph (Fin n)) : WB G ((n + 1) * ((n + 1) * (n + 3) + 1)) := by
  classical
  exact wb_fun (f := fun v : Fin n => Finset.univ.filter (G.Adj v)) (fun v => wb_finset_fin _)

theorem wb_setoid {n : ℕ} (P : Setoid (Fin n)) : WB P ((n + 1) * ((n + 1) * (n + 3) + 2)) := by
  have h := wb_finset (S := parts P) (fun a _ => wb_finset_fin a)
  refine h.mono (Nat.mul_le_mul ?_ le_rfl)
  have : (parts P).card ≤ n := by
    unfold parts
    exact Finset.card_image_le.trans (by simp)
  omega

/-- The word of a graph has length at most `3 (n+1)²`. -/
theorem toWord_graph_length_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    (toWord G).length ≤ 3 * (n + 1) ^ 2 := by
  classical
  rw [toWord_graph_length]
  have hb : ∀ u ∈ graphBlocks G, u.length ≤ 2 * n := by
    intro u hu
    simp only [graphBlocks, List.mem_ofFn] at hu
    obtain ⟨v, rfl⟩ := hu
    rw [setBlock_length]
    have : (Finset.words (Finset.univ.filter (G.Adj v))).length ≤ n := by
      simp only [Finset.words, Finset.length_sort]
      exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
    omega
  have key : ∀ bs : List (List ℕ), (∀ u ∈ bs, u.length ≤ 2 * n) →
      (blocksWord bs).length ≤ bs.length * (2 * n + 1) := by
    intro bs
    induction bs with
    | nil => intro _; simp [blocksWord]
    | cons u bs ih =>
        intro h
        rw [blocksWord_cons, List.length_append, List.length_cons]
        have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
        have := h u List.mem_cons_self
        simp only [blk, List.length_cons]
        nlinarith
  have := key _ hb
  rw [graphBlocks_length] at this
  nlinarith

end Lax185574Proofs.Compose
