import Lax185574Proofs.TreeAlgo.ComputeScatterType
import Lax185574Proofs.Words.Lex
import Lax185574Proofs.EncodingInjectivity

/-!
The word of the scatter type, as the program of lem:compute-stp writes
it.

The program holds the words of the shifted trees in the list `A`, where
entry `(i − 1) · n + v` is the word of `tree_{k+i,q−i}(v)` for
`1 ≤ i ≤ q` and `v < n`. It sorts the distinct words of `A`, and then
writes for every radius `r` from `1` to the radius bound of level `1`,
and for every distinct word `u` whose level admits `r`, the word
`r, u, value`. The value is the length of the greedy scan, capped at
`k + q`. `words_stp` shows that this list is the list of words of
`stp^G_{k,q}`, so its word is the word of the scatter type.
-/

namespace Lax185574Proofs.StpRam

open Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.PartialGraphEncoding
open Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus)

variable {n : ℕ}

/-- The radius bound `9^(k+i) · ρ⁻(k + i, q − i)` of level `i`. -/
def radius (k q i : ℕ) : ℕ := 9 ^ (k + i) * rhoMinus (k + i) (q - i)

/-- The word of the tree of level `i` of vertex `v`, from the list of
shifted trees. -/
def lw (A : List (List ℕ)) (n i v : ℕ) : List ℕ := A.getD ((i - 1) * n + v) []

/-- The greedy scan for the radius `r` and the tree word `u` of level
`i`. -/
def greedyW (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (i r : ℕ) (u : List ℕ) :
    List (Fin n) :=
  (List.finRange n).foldl
    (fun (S : List (Fin n)) (v : Fin n) =>
      if lw A n i v.val = u ∧ ∀ s ∈ S, v ∉ ballFrom adj s r then S ++ [v] else S) []

/-- The word written for the radius `r` and the tree word `u`. -/
def triple (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r : ℕ) (u : List ℕ) :
    List ℕ :=
  r :: u ++ [min (greedyW adj A (u.headD 0 - k) r u).length (k + q)]

/-- The words written by the program, in order. -/
def emitList (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q : ℕ) : List (List ℕ) :=
  (List.range (radius k q 1)).flatMap fun r' =>
    ((sortedDistinct A).filter fun u => r' + 1 ≤ radius k q (u.headD 0 - k)).map
      (triple adj A k q (r' + 1))

/-- Entry `j` of the list of shifted trees: the word of the tree of
level `j / n + 1` of vertex `j % n`. -/
noncomputable def ansW (G : PartialGraph (Fin n)) (k q j : ℕ) : List ℕ :=
  if h : j % n < n then toWord (shiftTree^[j / n + 1] (family G k q ⟨j % n, h⟩)) else []

/-- The list of the shifted trees, levels `1` to `q`. -/
noncomputable def answers (G : PartialGraph (Fin n)) (k q : ℕ) : List (List ℕ) :=
  (List.range (q * n)).map (ansW G k q)

/-! ### Facts about the radius bound -/

theorem radius_le_one (k q i : ℕ) (hi : 1 ≤ i) (hiq : i ≤ q) : radius k q i ≤ radius k q 1 := by
  unfold radius
  simp only [Lax3.DistFO.rhoMinus]
  rw [← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = 1 + j + m := ⟨q - (1 + j), by omega⟩
  have e1 : 1 + j + m - (1 + j) = m := by omega
  have e2 : 1 + j + m - 1 = j + m := by omega
  rw [e1, e2]
  nlinarith

/-! ### The tree words -/

variable {G : PartialGraph (Fin n)}

theorem headD_toWord (τ : TypeTree) : (toWord τ).headD 0 = τ.k := rfl

theorem ansW_eq (k q : ℕ) {i : ℕ} (hi : i < q) (v : Fin n) :
    ansW G k q (i * n + v) = toWord (tree G (k + (i + 1)) (q - (i + 1)) ![v]) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have h1 : (i * n + v) % n = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
  have h2 : (i * n + v) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  unfold ansW
  rw [dif_pos (by rw [h1]; exact v.isLt)]
  congr 1
  have hv : (⟨(i * n + v) % n, by rw [h1]; exact v.isLt⟩ : Fin n) = v := Fin.ext h1
  rw [hv, h2]
  exact shift_family k q v (by omega)

theorem lw_answers (k q : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hiq : i ≤ q) (v : Fin n) :
    lw (answers G k q) n i v = toWord (tree G (k + i) (q - i) ![v]) := by
  have hlt : (i - 1) * n + v < q * n := by
    have : (i - 1) * n + n ≤ q * n := by
      have : (i - 1 + 1) * n ≤ q * n := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    omega
  unfold lw answers
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [ansW_eq k q (by omega) v, show i - 1 + 1 = i by omega]

theorem mem_answers (k q : ℕ) {u : List ℕ} :
    u ∈ answers G k q ↔ ∃ i, 1 ≤ i ∧ i ≤ q ∧ ∃ v : Fin n, u = toWord (tree G (k + i) (q - i) ![v]) := by
  unfold answers
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hj
      · exact h
    have hjn : j / n < q := by
      rw [Nat.div_lt_iff_lt_mul hn]; exact hj
    refine ⟨j / n + 1, Nat.le_add_left 1 _, Nat.succ_le_of_lt hjn, ⟨j % n, Nat.mod_lt _ hn⟩, ?_⟩
    have := ansW_eq (G := G) k q hjn ⟨j % n, Nat.mod_lt _ hn⟩
    simp only at this
    rw [Nat.div_add_mod' j n] at this
    exact this
  · rintro ⟨i, hi1, hiq, v, rfl⟩
    refine ⟨(i - 1) * n + v, ?_, ?_⟩
    · have : (i - 1 + 1) * n ≤ q * n := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      have := v.isLt; omega
    · rw [ansW_eq k q (by omega) v, show i - 1 + 1 = i by omega]

/-! ### Order of the written words -/

theorem append_lt_append_of_lt {u v a b : List ℕ} (h : u < v) (hp : ¬ u <+: v) :
    u ++ a < v ++ b := by
  rcases List.lt_iff_exists.mp h with ⟨h1, -⟩ | ⟨i, hu, hv, heq, hlt⟩
  · exact absurd (by rw [h1]; exact List.take_prefix _ _) hp
  · refine List.lt_iff_exists.mpr (Or.inr ⟨i, by simp; omega, by simp; omega, fun j hj => ?_, ?_⟩)
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
      exact heq j hj
    · rw [List.getElem_append_left hu, List.getElem_append_left hv]; exact hlt

theorem not_prefix_of_tree {τ τ' : TypeTree} (h : toWord τ < toWord τ') :
    ¬ toWord τ <+: toWord τ' := by
  rintro ⟨s, hs⟩
  have := (Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree.prefix_inj τ' τ [] s
    (by rw [List.append_nil, hs]))
  obtain ⟨rfl, rfl⟩ := this
  exact lt_irrefl _ h

/-! ### The greedy scan on words -/

theorem greedyW_eq {adj : Fin n → List (Fin n)} (k q : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hiq : i ≤ q)
    (r : ℕ) (b : Fin n) :
    greedyW adj (answers G k q) i r (toWord (tree G (k + i) (q - i) ![b])) =
      greedyCore adj (fun v => shiftTree^[i] (family G k q v)) r
        (tree G (k + i) (q - i) ![b]) := by
  unfold greedyW greedyCore
  congr 1
  funext S v
  have : lw (answers G k q) n i v = toWord (tree G (k + i) (q - i) ![b]) ↔
      shiftTree^[i] (family G k q v) = tree G (k + i) (q - i) ![b] := by
    have : PrefixFree TypeTree := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
    rw [lw_answers k q hi1 hiq v, shift_family k q v hiq]
    exact toWord_injective.eq_iff
  simp only [this]

theorem tree_k (k q : ℕ) (v : Fin n) : (tree G k q ![v]).k = k := rfl

/-! ### The written words are the words of the scatter type -/

theorem mem_emitList {adj : Fin n → List (Fin n)} {A : List (List ℕ)} {k q : ℕ} {w : List ℕ} :
    w ∈ emitList adj A k q ↔ ∃ r u, 1 ≤ r ∧ r ≤ radius k q 1 ∧ u ∈ A ∧
      r ≤ radius k q (u.headD 0 - k) ∧ w = triple adj A k q r u := by
  simp only [emitList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    mem_sortedDistinct, decide_eq_true_eq]
  constructor
  · rintro ⟨r', hr', u, ⟨hu, hur⟩, rfl⟩
    exact ⟨r' + 1, u, by omega, by omega, hu, hur, rfl⟩
  · rintro ⟨r, u, hr1, hr2, hu, hur, rfl⟩
    exact ⟨r - 1, by omega, u, ⟨hu, by rw [show r - 1 + 1 = r by omega]; exact hur⟩,
      by rw [show r - 1 + 1 = r by omega]⟩

theorem mem_image_stpCore {adj : Fin n → List (Fin n)} (k q : ℕ) {w : List ℕ} :
    w ∈ (stpCore adj (family G k q) k q).image toWord ↔
      w ∈ emitList adj (answers G k q) k q := by
  rw [mem_emitList]
  simp only [stpCore, Finset.mem_image, domainCore, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨_, ⟨d, ⟨i', hi', b, r, ⟨hr1, hr2⟩, rfl⟩, rfl⟩, rfl⟩
    have hf := shift_family (G := G) k q b (show i' + 1 ≤ q by omega)
    refine ⟨r, toWord (tree G (k + (i' + 1)) (q - (i' + 1)) ![b]), hr1,
      le_trans hr2 (radius_le_one k q _ (by omega) (by omega)),
      (mem_answers k q).mpr ⟨i' + 1, by omega, by omega, b, rfl⟩,
      by rw [headD_toWord, tree_k, show k + (i' + 1) - k = i' + 1 by omega]; exact hr2, ?_⟩
    simp only [hf, tree_k, show k + (i' + 1) - k = i' + 1 by omega, triple, headD_toWord]
    rw [greedyW_eq k q (by omega) (by omega)]
    rfl
  · rintro ⟨r, u, hr1, hr2, hu, hur, rfl⟩
    obtain ⟨i, hi1, hiq, b, rfl⟩ := (mem_answers k q).mp hu
    rw [headD_toWord, tree_k, show k + i - k = i by omega] at hur
    have hf := shift_family (G := G) k q b hiq
    refine ⟨_, ⟨(r, shiftTree^[i - 1 + 1] (family G k q b)),
      ⟨i - 1, by omega, b, r, ⟨hr1, by rw [show i - 1 + 1 = i by omega]; exact hur⟩, rfl⟩, rfl⟩, ?_⟩
    rw [show i - 1 + 1 = i by omega, hf]
    simp only [tree_k, show k + i - k = i by omega, triple, headD_toWord]
    rw [greedyW_eq k q hi1 hiq]
    rfl

theorem emitList_pairwise {adj : Fin n → List (Fin n)} (k q : ℕ) :
    (emitList adj (answers G k q) k q).Pairwise (· < ·) := by
  have : PrefixFree TypeTree := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  unfold emitList
  rw [List.pairwise_flatMap]
  refine ⟨fun r' _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine ((sortedDistinct_sorted _).filter _).imp_of_mem fun {u u'} hu hu' huu => ?_
    have hu1 := mem_sortedDistinct.mp (List.mem_filter.mp hu).1
    have hu2 := mem_sortedDistinct.mp (List.mem_filter.mp hu').1
    obtain ⟨i, -, -, b, rfl⟩ := (mem_answers k q).mp hu1
    obtain ⟨i', -, -, b', rfl⟩ := (mem_answers k q).mp hu2
    simp only [triple]
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff]
    exact Or.inr ⟨rfl, append_lt_append_of_lt huu (not_prefix_of_tree huu)⟩
  · refine (List.pairwise_lt_range).imp fun {r₁ r₂} h12 => ?_
    intro x hx y hy
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u', -, rfl⟩ := List.mem_map.mp hy
    simp only [triple, List.cons_append]
    rw [List.cons_lt_cons_iff]
    exact Or.inl (by omega)

/-- **The word of the scatter type.** With the lists of resolved
neighbors, the list of words written by the program is the list of
words of `stp^G_{k,q}`. -/
theorem words_stp {adj : Fin n → List (Fin n)} (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v)
    (k q : ℕ) : Finset.words (stp G k q) = emitList adj (answers G k q) k q := by
  rw [← stpCore_eq hadj k q]
  unfold Finset.words
  have hP := emitList_pairwise (G := G) (adj := adj) k q
  have hset : (stpCore adj (family G k q) k q).image toWord =
      (emitList adj (answers G k q) k q).toFinset := by
    ext w; rw [mem_image_stpCore, List.mem_toFinset]
  rw [hset, List.toFinset_sort _ (hP.imp ne_of_lt)]
  exact hP.imp le_of_lt

theorem toWord_stp {adj : Fin n → List (Fin n)} (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v)
    (k q : ℕ) : toWord (stp G k q) = toWord (emitList adj (answers G k q) k q) := by
  show toWord (Finset.words (stp G k q)) = _
  rw [words_stp hadj]

end Lax185574Proofs.StpRam
