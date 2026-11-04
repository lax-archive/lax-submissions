import Lax185574Proofs.ResolveRam.SizeSpec
import Lax185574Proofs.MC.Bounds.TreeEntries
import Lax185574Proofs.MC.Bounds.WordSizes

/-!
Words whose entries are bounded by their length.

`Good K X u` says that every entry of `u` is at most the length of `u`
plus `K` plus `X`. The words of lists, finite sets and families of good
words are good, and so are concatenations and the inputs of the switch.
The words of type trees and of their roots are good if `K` bounds the
constant of the rank and the arity and `X` bounds the colors, by
`tree_entry` and `node_entry`. The canonical form of a list of words
has as entries its lengths and the entries of the words.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.DistanceLogic Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.Simulate

/-- Every entry of `u` is at most its length plus `K` plus `X`. -/
def Good (K X : ℕ) (u : List ℕ) : Prop := ∀ e ∈ u, e ≤ u.length + K + X

variable {K X : ℕ}

theorem Good.mono {K' X' : ℕ} {u : List ℕ} (h : Good K X u) (hK : K ≤ K') (hX : X ≤ X') :
    Good K' X' u :=
  fun e he => le_trans (h e he) (by omega)

theorem good_of_le {u : List ℕ} (h : ∀ e ∈ u, e ≤ K + X) : Good K X u :=
  fun e he => by have := h e he; omega

theorem Good.append {u v : List ℕ} (hu : Good K X u) (hv : Good K X v) : Good K X (u ++ v) := by
  intro e he
  simp only [List.length_append]
  rcases List.mem_append.1 he with h | h
  · have := hu e h; omega
  · have := hv e h; omega

theorem good_cons {a : ℕ} {u : List ℕ} (ha : a ≤ u.length + 1 + K + X) (hu : Good K X u) :
    Good K X (a :: u) := by
  intro e he
  simp only [List.length_cons]
  rcases List.mem_cons.1 he with rfl | h
  · omega
  · have := hu e h; omega

theorem length_le_flatten {L : List (List ℕ)} {u : List ℕ} (h : u ∈ L) :
    u.length ≤ L.flatten.length := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem good_flatten {L : List (List ℕ)} (h : ∀ u ∈ L, Good K X u) : Good K X L.flatten := by
  intro e he
  obtain ⟨u, hu, heu⟩ := List.mem_flatten.1 he
  have := h u hu e heu
  have := length_le_flatten hu
  omega

theorem length_lt_toWord_list {α : Type*} [WordEncoding α] (l : List α)
    (hne : ∀ a ∈ l, toWord a ≠ []) : l.length < (toWord l).length := by
  show l.length < (l.length :: (l.map toWord).flatten).length
  simp only [List.length_cons]
  suffices l.length ≤ ((l.map toWord).flatten).length by omega
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h1 := hne a (by simp)
    have h2 := ih (fun b hb => hne b (by simp [hb]))
    have : (toWord a).length ≠ 0 := fun h0 => h1 (List.eq_nil_of_length_eq_zero h0)
    omega

theorem good_list {α : Type*} [WordEncoding α] (l : List α) (hne : ∀ a ∈ l, toWord a ≠ [])
    (h : ∀ a ∈ l, Good K X (toWord a)) : Good K X (toWord l) := by
  have hl := length_lt_toWord_list l hne
  show Good K X (l.length :: (l.map toWord).flatten)
  refine good_cons ?_ (good_flatten ?_)
  · change l.length < (l.length :: (l.map toWord).flatten).length at hl
    simp only [List.length_cons] at hl
    omega
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
    exact h a ha

theorem good_fun {α : Type*} [WordEncoding α] {n : ℕ} (f : Fin n → α) (hn : n ≤ X)
    (h : ∀ i, Good K X (toWord (f i))) : Good K X (toWord f) := by
  rw [toWord_fun_eq]
  refine good_cons (by omega) (good_flatten ?_)
  intro u hu
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact h i

theorem good_finset {α : Type*} [WordEncoding α] (S : Finset α) (h : ∀ a ∈ S, Good K X (toWord a)) :
    Good K X (toWord S) := by
  intro e he
  rcases mem_toWord_finset S he with h1 | ⟨a, ha, hl, h2⟩
  · omega
  · have := h a ha e h2; omega

theorem good_tree {V : Type*} (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V)
    (hK : k + q + nodeCst k q ℓ ≤ K) (hX : ∀ v, G.color v ≤ X) : Good K X (toWord (tree G k q a)) := by
  intro e he
  rcases tree_entry G k q a he with h | h | ⟨v, rfl⟩
  · omega
  · omega
  · have := hX v; omega

theorem good_node {V : Type*} (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V)
    (hK : nodeCst k q ℓ ≤ K) (hX : ∀ v, G.color v ≤ X) : Good K X (toWord (node G k q a)) := by
  intro e he
  rcases node_entry G q k ℓ a e he with h | h | ⟨v, rfl⟩
  · omega
  · omega
  · have := hX v; omega

theorem good_swIn {a b c : List ℕ} (ha : Good K X a) (hb : Good K X b) (hc : Good K X c) :
    Good K X (swIn a b c) := by
  have h := (ha.append hb).append hc
  have hw : swIn a b c = [a.length, b.length, c.length] ++ (a ++ b ++ c) := by
    simp [swIn]
  intro e he
  rw [hw] at he ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
  rcases List.mem_append.1 he with h1 | h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl <;> omega
  · have := h e h1
    simp only [List.length_append] at this
    omega

theorem good_sw5In {a b c d f : List ℕ} (ha : Good K X a) (hb : Good K X b) (hc : Good K X c)
    (hd : Good K X d) (hf : Good K X f) : Good K X (sw5In a b c d f) :=
  good_swIn (good_swIn ha hb hc) hd hf

theorem good_fix {u : List ℕ} (h : maxEntry u ≤ K) : Good K X u :=
  good_of_le fun e he => by have := le_maxEntry he; omega

/-- The word of a word, as a list of numbers. -/
theorem toWord_listNat (w : List ℕ) : toWord w = w.length :: w := by
  show w.length :: (w.map toWord).flatten = _
  congr 1
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [ih]; rfl

theorem good_word {w : List ℕ} (h : Good K X w) : Good K X (toWord w) := by
  rw [toWord_listNat]
  refine good_cons (by omega) h

/-- Entries of the canonical form of a list of words. -/
theorem canonW_entry {ws : List (List ℕ)} {e : ℕ} (he : e ∈ canonW ws) :
    e ≤ (canonW ws).length ∨ ∃ w ∈ ws, e ∈ w := by
  unfold canonW at he ⊢
  set l := ws.toFinset.sort (· ≤ ·) with hl
  have hlen := length_lt_toWord_list l (fun w _ => by rw [toWord_listNat]; simp)
  change e ∈ l.length :: (l.map toWord).flatten at he
  rcases List.mem_cons.1 he with rfl | h
  · left; omega
  · obtain ⟨u, hu, heu⟩ := List.mem_flatten.1 h
    have hlu := length_le_flatten hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    have hw' : w ∈ ws := by
      rw [hl, Finset.mem_sort, List.mem_toFinset] at hw; exact hw
    rw [toWord_listNat] at heu hlu
    rcases List.mem_cons.1 heu with rfl | h2
    · left
      have : (toWord l).length = 1 + ((l.map toWord).flatten).length := by
        show (l.length :: (l.map toWord).flatten).length = _
        simp only [List.length_cons]; omega
      simp only [List.length_cons] at hlu
      omega
    · right; exact ⟨w, hw', h2⟩

theorem mem_toWord_words {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) {e : ℕ} (he : e ∈ w) :
    e ∈ toWord ws := by
  show e ∈ ws.length :: (ws.map toWord).flatten
  refine List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨toWord w, List.mem_map.2 ⟨w, hw, rfl⟩, ?_⟩)
  rw [toWord_listNat]; exact List.mem_cons_of_mem _ he

theorem maxEntry_le_bound {u : List ℕ} {B : ℕ} (h : ∀ e ∈ u, e ≤ B) : maxEntry u ≤ B := by
  induction u with
  | nil => exact Nat.zero_le _
  | cons a u ih =>
    show max a (maxEntry u) ≤ B
    exact max_le (h a (by simp)) (ih fun e he => h e (by simp [he]))

end Lax185574Proofs.ResolveRam
