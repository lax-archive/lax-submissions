import Lax185574Proofs.Compose.CsrToGraph
import Lax185574Proofs.StpRam.Relax

/-!
The word of a graph on `Fin n` as blocks of neighbor lists, and the
offsets and targets of its compressed-row form.

The block of vertex `v` is the number of its neighbors followed by the
words `1, z` of its neighbors `z` in increasing order (`vblk`). The
offset of `v` is the number of neighbors of the vertices before `v`,
and the targets are the neighbor lists one after the other.
-/

namespace Lax185574Proofs.StpRam

open Lax185574.WordEncoding Lax185574Proofs.Compose

open Classical in
/-- The neighbors of `v`, in increasing order. -/
noncomputable def nbrL {n : ℕ} (H : SimpleGraph (Fin n)) (v : ℕ) : List ℕ :=
  (List.range n).filter fun z => ∃ h : z < n, ∃ hv : v < n, H.Adj ⟨v, hv⟩ ⟨z, h⟩

/-- The block of a neighbor list. -/
def vblk (l : List ℕ) : List ℕ := l.length :: (l.map fun z => [1, z]).flatten

/-- The blocks of the vertices `v, …, n − 1`. -/
noncomputable def blocksFrom {n : ℕ} (H : SimpleGraph (Fin n)) (v : ℕ) : List ℕ :=
  ((List.range' v (n - v)).map fun w => vblk (nbrL H w)).flatten

/-- The offsets. -/
noncomputable def offL {n : ℕ} (H : SimpleGraph (Fin n)) (v : ℕ) : ℕ :=
  ((List.range v).map fun w => (nbrL H w).length).sum

/-- The targets. -/
noncomputable def tgtL {n : ℕ} (H : SimpleGraph (Fin n)) (p : ℕ) : ℕ :=
  ((List.range n).map (nbrL H)).flatten.getD p 0

theorem mem_nbrL {n : ℕ} {H : SimpleGraph (Fin n)} {v z : ℕ} (hv : v < n) :
    z ∈ nbrL H v ↔ ∃ h : z < n, H.Adj ⟨v, hv⟩ ⟨z, h⟩ := by
  simp only [nbrL, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h, _, ha⟩; exact ⟨h, ha⟩
  · rintro ⟨h, ha⟩; exact ⟨h, h, hv, ha⟩

theorem lt_of_mem_nbrL {n : ℕ} {H : SimpleGraph (Fin n)} {v z : ℕ} (h : z ∈ nbrL H v) : z < n := by
  simp only [nbrL, List.mem_filter, List.mem_range] at h; exact h.1

theorem nbrL_of_ge {n : ℕ} (H : SimpleGraph (Fin n)) {v : ℕ} (hv : n ≤ v) : nbrL H v = [] := by
  simp only [nbrL, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq]
  rintro z - ⟨_, h, _⟩; omega

/-- The word of a graph, block by block. -/
theorem toWord_graph_blocks {n : ℕ} (H : SimpleGraph (Fin n)) : toWord H = n :: blocksFrom H 0 := by
  classical
  rw [toWord_graph]
  congr 1
  simp only [blocksWord, graphBlocks, blocksFrom, Nat.sub_zero, List.range'_eq_map_range,
    Nat.zero_add, List.map_ofFn]
  rw [List.ofFn_eq_map]
  simp only [List.map_map]
  rw [← List.map_coe_finRange_eq_range] <;> try rfl
  · simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp, blk, vblk, setBlock_length]
    rw [words_fin]
    have hfil : ((List.range n).filter (fun z => ∃ h : z < n, (⟨z, h⟩ : Fin n) ∈
        Finset.univ.filter (H.Adj v))) = nbrL H v := by
      unfold nbrL; congr 1; funext z
      apply decide_eq_decide.mpr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h, ha⟩ => ⟨h, v.isLt, ha⟩, fun ⟨h, _, ha⟩ => ⟨h, ha⟩⟩
    rw [setBlock, words_fin, hfil]
    simp only [List.length_map, List.map_map]
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    congr 2

theorem blocksFrom_succ {n : ℕ} (H : SimpleGraph (Fin n)) {v : ℕ} (hv : v < n) :
    blocksFrom H v = vblk (nbrL H v) ++ blocksFrom H (v + 1) := by
  unfold blocksFrom
  rw [show n - v = (n - (v + 1)) + 1 by omega, List.range'_succ]
  simp

theorem blocksFrom_n {n : ℕ} (H : SimpleGraph (Fin n)) : blocksFrom H n = [] := by
  simp [blocksFrom]

theorem offL_succ {n : ℕ} (H : SimpleGraph (Fin n)) (v : ℕ) :
    offL H (v + 1) = offL H v + (nbrL H v).length := by
  simp [offL, List.range_succ]

theorem offL_mono {n : ℕ} (H : SimpleGraph (Fin n)) {v w : ℕ} (h : v ≤ w) : offL H v ≤ offL H w := by
  induction w with
  | zero => simp at h; subst h; rfl
  | succ w ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [offL_succ]; exact le_trans (ih (by omega)) (by omega)
    · rfl

theorem length_flatten_take_range {n : ℕ} (H : SimpleGraph (Fin n)) {v : ℕ} (hv : v ≤ n) :
    (((List.range n).map (nbrL H)).take v).flatten.length = offL H v := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hv]
  simp [offL, List.length_flatten, List.map_map, Function.comp_def]

theorem length_targets {n : ℕ} (H : SimpleGraph (Fin n)) :
    ((List.range n).map (nbrL H)).flatten.length = offL H n := by
  rw [← length_flatten_take_range H le_rfl, List.take_of_length_le (by simp)]

/-- The slots of row `v` hold the neighbors of `v`. -/
theorem tgtL_row {n : ℕ} (H : SimpleGraph (Fin n)) {v j : ℕ} (hv : v < n)
    (hj : j < (nbrL H v).length) : tgtL H (offL H v + j) = (nbrL H v)[j] := by
  set L := (List.range n).map (nbrL H) with hL
  have hvL : v < L.length := by simp [hL, hv]
  have hLv : L[v] = nbrL H v := by simp [hL]
  have hsplit : L.flatten = (L.take v).flatten ++ (L[v] ++ (L.drop (v + 1)).flatten) := by
    have h1 := List.take_append_drop v L
    rw [List.drop_eq_getElem_cons hvL] at h1
    have h2 := congrArg List.flatten h1
    simp only [List.flatten_append, List.flatten_cons] at h2
    exact h2.symm
  unfold tgtL
  rw [← hL, hsplit, ← length_flatten_take_range H hv.le, ← hL]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _ |>.trans (by omega)),
    show (L.take v).flatten.length + j - (L.take v).flatten.length = j by omega,
    List.getElem?_append_left (by rw [hLv]; exact hj)]
  simp only [hLv]
  rw [List.getElem?_eq_getElem hj]; rfl

theorem inRow_iff {n : ℕ} (H : SimpleGraph (Fin n)) {w : ℕ} (hw : w < n) (v : ℕ) :
    InRow (offL H) (tgtL H) w v ↔ v ∈ nbrL H w := by
  constructor
  · rintro ⟨p, h1, h2, rfl⟩
    rw [offL_succ] at h2
    obtain ⟨j, rfl⟩ : ∃ j, p = offL H w + j := ⟨p - offL H w, by omega⟩
    rw [tgtL_row H hw (by omega)]
    exact List.getElem_mem _
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    exact ⟨offL H w + j, by omega, by rw [offL_succ]; omega, tgtL_row H hw hj⟩

theorem tgtL_lt {n : ℕ} (H : SimpleGraph (Fin n)) {p : ℕ} (hp : p < offL H n) : tgtL H p < n := by
  unfold tgtL
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_targets]; exact hp)]
  simp only [Option.getD_some]
  have := List.getElem_mem (l := ((List.range n).map (nbrL H)).flatten)
    (by rw [length_targets]; exact hp)
  simp only [List.mem_flatten, List.mem_map, List.mem_range] at this
  obtain ⟨_, ⟨w, -, rfl⟩, hm⟩ := this
  exact lt_of_mem_nbrL hm

end Lax185574Proofs.StpRam
