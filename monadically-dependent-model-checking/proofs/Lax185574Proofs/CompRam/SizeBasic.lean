import Lax185574Proofs.CompRam.GlueSpec
import Lax185574Proofs.ShiftRam.Rounds

/-!
Sizes of the words of the stack machine of lem:compose.

`NW d l w`: the word `w` is the word of a node of depth `d` and arity
`l`. `Small Λ B w`: `w` has length at most `Λ` and entries below `B`.
The lemmas bound the words that the machine builds from node words (the
atoms of a frame, its children), and the answers of the rank shift and
of the restriction (`sh_answer`, `re_answer`): an answer is at most as
long as the node asked about, and its entries stay below every bound
`B` above the entries, the length, the arity and the rank of that node.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.ShiftRam Lax185574Proofs.RestrictionRam

/-- The word is the word of a node of depth `d` and arity `l`. -/
def NW (d l : ℕ) (w : List ℕ) : Prop := ∃ t : Node d l, w = toWord t

/-- The word has length at most `Λ` and entries below `B`. -/
def Small (Λ B : ℕ) (w : List ℕ) : Prop := w.length ≤ Λ ∧ ∀ e ∈ w, e < B

theorem Small.mono {Λ Λ' B B' : ℕ} {w : List ℕ} (h : Small Λ B w) (h1 : Λ ≤ Λ') (h2 : B ≤ B') :
    Small Λ' B' w := ⟨le_trans h.1 h1, fun e he => lt_of_lt_of_le (h.2 e he) h2⟩

theorem mem_toWord_cases {ws : List (List ℕ)} {v : ℕ} (hv : v ∈ toWord ws) :
    v = ws.length ∨ (∃ w ∈ ws, v = w.length) ∨ (∃ w ∈ ws, v ∈ w) := by
  rw [toWord_words] at hv
  rcases List.mem_cons.mp hv with h | h
  · exact Or.inl h
  · simp only [frames, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨w, hw, rfl⟩, hv'⟩ := h
    rcases List.mem_cons.mp hv' with h' | h'
    · exact Or.inr (Or.inl ⟨w, hw, h'⟩)
    · exact Or.inr (Or.inr ⟨w, hw, h'⟩)

theorem mem_toWord_of_mem {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) {v : ℕ} (hv : v ∈ w) :
    v ∈ toWord ws := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  exact (mem_toWord_words hi).2 v hv

theorem length_le_toWord {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) :
    w.length < (toWord ws).length := by
  rw [length_toWord_words]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w : List ℕ => w.length + 1) hw)
  omega

theorem count_lt_toWord (ws : List (List ℕ)) : ws.length < (toWord ws).length := by
  rw [length_toWord_words]
  have : ws.length ≤ (ws.map fun w : List ℕ => w.length + 1).sum := by
    calc ws.length = (ws.map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (fun u _ => by omega)
  omega

/-- Entries of the word of a list of small words are small. -/
theorem toWord_lt {ws : List (List ℕ)} {B : ℕ} (h1 : ws.length < B)
    (h2 : ∀ w ∈ ws, w.length < B ∧ ∀ e ∈ w, e < B) : ∀ e ∈ toWord ws, e < B := by
  intro e he
  rcases mem_toWord_cases he with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, he'⟩
  · exact h1
  · exact (h2 w hw).1
  · exact (h2 w hw).2 e he'

theorem length_toWord_append (a b : List (List ℕ)) :
    (toWord (a ++ b)).length + 1 = (toWord a).length + (toWord b).length := by
  rw [length_toWord_words, length_toWord_words, length_toWord_words, List.map_append,
    List.sum_append]
  omega

theorem length_renAtom (l : ℕ) (c : List ℕ) : (renAtom l c).length = c.length := by
  simp [renAtom]

theorem renAtom_lt {l B : ℕ} {c : List ℕ} (h : ∀ e ∈ c, e < B) : ∀ e ∈ renAtom l c, e < B + l := by
  intro e he
  simp only [renAtom, List.mem_mapIdx] at he
  obtain ⟨i, hi, rfl⟩ := he
  have := h c[i] (List.getElem_mem hi)
  split <;> omega

theorem length_toWord_map_renAtom (l : ℕ) (ws : List (List ℕ)) :
    (toWord (ws.map (renAtom l))).length = (toWord ws).length := by
  rw [length_toWord_words, length_toWord_words, List.map_map]
  congr 2
  exact List.map_congr_left fun c _ => by simp [length_renAtom]

/-! ### Node words -/

theorem atomsOf_prefix {d l : ℕ} {w : List ℕ} (h : NW d l w) : toWord (atomsOf w) <+: w := by
  obtain ⟨t, rfl⟩ := h
  rw [atomsOf_node]
  cases d with
  | zero => rw [toWord_node_zero]
  | succ d => rw [toWord_node_succ]; exact List.prefix_append _ _

theorem atomsOf_small {d l Λ B : ℕ} {w : List ℕ} (h : NW d l w) (hs : Small Λ B w) :
    Small Λ B (toWord (atomsOf w)) := by
  have hp := atomsOf_prefix h
  exact ⟨le_trans hp.length_le hs.1, fun e he => hs.2 e (hp.subset he)⟩

theorem extsOf_count {d l : ℕ} {w : List ℕ} (h : NW (d + 1) l w) : (extsOf w).length < w.length := by
  obtain ⟨t, rfl⟩ := h
  rw [extsOf_node, toWord_node_succ, List.length_append]
  have := count_lt_toWord (Node.exts t).words
  omega

theorem nw_child {d l : ℕ} {w : List ℕ} (h : NW (d + 1) l w) {j : ℕ} (hj : j < (extsOf w).length) :
    NW d (l + 1) (((extsOf w).getD j []).drop 1) ∧ ((extsOf w).getD j []).drop 1 <:+: w := by
  obtain ⟨t, rfl⟩ := h
  rw [extsOf_node] at hj
  obtain ⟨ε, hε, hw⟩ := extsOf_getD t hj
  rw [hw]
  simp only [List.drop_succ_cons, List.drop_zero]
  exact ⟨⟨ε.2, rfl⟩, child_infix hε⟩

/-- The entries of the guard of an extension are entries of the word. -/
theorem ext_head_mem {d l : ℕ} {w : List ℕ} (h : NW (d + 1) l w) {j : ℕ}
    (hj : j < (extsOf w).length) : ((extsOf w).getD j []).headD 0 ∈ w := by
  obtain ⟨t, rfl⟩ := h
  rw [extsOf_node] at hj
  obtain ⟨ε, hε, hw⟩ := extsOf_getD t hj
  rw [hw, List.headD_cons]
  have h1 : toWord ε ∈ (Node.exts t).words := mem_words.mpr ⟨ε, hε, rfl⟩
  have h2 := mem_toWord_of_mem h1 (v := ε.1.val) (by rw [toWord_ext]; simp)
  rw [toWord_node_succ]
  exact List.mem_append_right _ h2

/-! ### The answers -/

variable {n : ℕ} (G : PartialGraph (Fin n))

/-- **The answer of a restriction is small.** -/
theorem re_bound (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) (J : List (Fin l)) (hJ : J.Nodup)
    (Bz : ℕ) (hc : ∀ v ∈ toWord (node G kk d u), v < Bz) (hl : (toWord (node G kk d u)).length < Bz)
    (hℓ : l < Bz) (hk : kk < Bz) (hq : d < Bz) :
    (toWord (tree G kk d (fun i => u (J.get i)))).length ≤ (toWord (node G kk d u)).length + 3 ∧
      ∀ v ∈ toWord (tree G kk d (fun i => u (J.get i))), v < Bz := by
  set μ := node G kk d u with hμ
  have hJl : J.length ≤ l := by simpa using hJ.length_le_card
  have hz : tree G kk d (fun i => u (J.get i)) = restrictTree kk d l μ J := by
    rw [restrictTree_tree G kk d _ _ hJ]
  have hw : toWord (tree G kk d (fun i => u (J.get i))) = [kk, d, J.length] ++
      treeOut (rsub J) (rgsub J) d 0 (toWord μ) 0 := by
    rw [hz, treeOut_restrict J (toWord μ) d 0 μ 0 [] (by simp)]
    rfl
  rw [hw]
  refine ⟨?_, ?_⟩
  · have := length_treeOut_le (rsub J) (rgsub J) d 0 l (toWord μ) 0 μ [] (by simp)
    simp; omega
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · simp at h; rcases h with rfl | rfl | rfl <;> omega
    · refine treeOut_lt _ _ (toWord μ) hc hl d 0 l 0 μ [] (by simp) ?_ ?_ ?_ v h
      · intro tg k' v' r hv' hr
        rcases rsub_le J hJl hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd _ _ tg k' v' r hv' hr
        rcases rsub_le J hJl hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd i r _ _ hi hr
        rcases gmap_le J hJl hr with h' | h'
        · have := hc i hi; omega
        · omega

/-- **The answer of a rank shift is small.** -/
theorem sh_bound (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) (hl1 : 1 ≤ l) (Bz : ℕ)
    (hc : ∀ v ∈ toWord (node G kk (d + 1) u), v < Bz) (hl : (toWord (node G kk (d + 1) u)).length < Bz)
    (hℓ : l + 1 < Bz) (hk : kk + 1 < Bz) (hq : d < Bz) :
    (toWord (node G (kk + 1) d u)).length ≤ (toWord (node G kk (d + 1) u)).length ∧
      ∀ v ∈ toWord (node G (kk + 1) d u), v < Bz := by
  obtain ⟨a, ha, -⟩ := exists_guard_zero G kk d hl1 u
  obtain ⟨b, hb⟩ := child_eq G kk d u ha
  have hinf := child_infix ha
  rw [hb] at hinf
  obtain ⟨h1, h2⟩ := answer_bound G (kk + 1) d u b Bz (fun v hv => hc v (hinf.subset hv))
    (lt_of_le_of_lt hinf.length_le hl) hℓ hk hq
  rw [toWord_tree_eq] at h1 h2
  simp only [List.length_append] at h1
  have := hinf.length_le
  refine ⟨by simp at h1; omega, fun v hv => h2 v (List.mem_append_right _ hv)⟩

end Lax185574Proofs.CompRam
