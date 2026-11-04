import Lax185574Proofs.ResolveRam.Glue.CFinAt
import Lax185574Proofs.ResolveRam.Glue.CaseFin

/-!
The states and calls after the last call of an item on the way down
(position `dn d i m` with `m + 1 = nDn d i`), on words.

The expansion of the item is `exE d i`, the new item words of the level
below (`exE_eq`, `exE_words`). The next position is one of four
(`next_fin_a` to `next_fin_d`): the next item of the level, the first
item of the next level, the first item of the last level on the way up,
or the first item of the level itself on the way up when the next level
is empty. In each case the state of the next position is the old one
with the new lengths of the levels and the expansion appended to the
item words (`sw_fin_a` to `sw_fin_d`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The expansion of item `i` of level `d`, as item words. -/
noncomputable def exE (d i : ℕ) : List (List ℕ) :=
  (nxW G P Q s k₀ q₀ d (i + 1)).drop (nxW G P Q s k₀ q₀ d i).length

theorem nxL_prefix (d : ℕ) {i j : ℕ} (h : i ≤ j) :
    ∃ Z, nxL G P Q s k₀ q₀ d j = nxL G P Q s k₀ q₀ d i ++ Z := by
  refine ⟨(((lvR G P Q s k₀ q₀ d).zipIdx.take j).drop i).flatMap
    fun x => asItems x.2 (exR G P Q s k₀ q₀ x.1.2), ?_⟩
  rw [nxL, nxL, ← List.flatMap_append]
  congr 1
  conv_lhs => rw [← List.take_append_drop i ((lvR G P Q s k₀ q₀ d).zipIdx.take j)]
  rw [List.take_take, Nat.min_eq_left h]

theorem nxW_prefix (d : ℕ) {i j : ℕ} (h : i ≤ j) :
    ∃ Z, nxW G P Q s k₀ q₀ d j = nxW G P Q s k₀ q₀ d i ++ Z := by
  obtain ⟨Z, hZ⟩ := nxL_prefix G P Q s k₀ q₀ d h
  exact ⟨Z.map itemW, by rw [nxW, nxW, hZ, List.map_append]⟩

theorem exE_eq (d i : ℕ) :
    nxW G P Q s k₀ q₀ d (i + 1) = nxW G P Q s k₀ q₀ d i ++ exE G P Q s k₀ q₀ d i := by
  obtain ⟨Z, hZ⟩ := nxW_prefix G P Q s k₀ q₀ d (Nat.le_succ i)
  rw [exE, hZ, List.drop_left]

theorem length_exE (d i : ℕ) :
    (nxW G P Q s k₀ q₀ d (i + 1)).length = (nxW G P Q s k₀ q₀ d i).length + (exE G P Q s k₀ q₀ d i).length := by
  rw [exE_eq G P Q s k₀ q₀ d i, List.length_append]

theorem exE_words {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) {k q ℓ : ℕ}
    {t : Node (q + 1) ℓ} (hx : (itm G P Q s k₀ q₀ d i).2 = ⟨k, q + 1, ℓ, t⟩) :
    exE G P Q s k₀ q₀ d i =
      (exW (dW G P Q s) k q ℓ (toWord t) (coW G P Q s k₀ q₀ ⟨k, q + 1, ℓ, t⟩)).map (i :: ·) := by
  rw [exE, sw_fin_item hi hx, List.drop_left]

/-! ### The next position -/

theorem next_fin {d i m : ℕ} (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    next G P Q s k₀ q₀ (.dn d i m) =
      if i + 1 < (lvR G P Q s k₀ q₀ d).length then .dn d (i + 1) 0
      else if (lvR G P Q s k₀ q₀ (d + 1)).length = 0 then .up d 0 0
      else if d + 1 < q₀ then .dn (d + 1) 0 0 else .up (d + 1) 0 0 := by
  simp only [next, show ¬ (m + 1 < nDn G P Q s k₀ q₀ d i) by omega, if_false]

/-! ### The states -/

/-- The state after an item on the way down, from the old state. -/
def swFin (w : SW) (LL' : List ℕ) (E : List (List ℕ)) : SW := ⟨w.CT, w.SG, [], [], LL', [], [], w.LV ++ E, []⟩

theorem LV_dn' (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).LV = lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := by
  simp [swAt]

theorem sw_fin_a {d i m : ℕ} :
    swAt G P Q s k₀ q₀ (.dn d (i + 1) 0) =
      swFin (swAt G P Q s k₀ q₀ (.dn d i m))
        (llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d (exE G P Q s k₀ q₀ d i).length 0)
        (exE G P Q s k₀ q₀ d i) := by
  rw [← ll_next_item (exE G P Q s k₀ q₀ d i).length (length_exE G P Q s k₀ q₀ d i) m, swFin, LV_dn',
    List.append_assoc, ← exE_eq]
  simp [swAt]

theorem sw_fin_b {d i m : ℕ} (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length) :
    swAt G P Q s k₀ q₀ (.dn (d + 1) 0 0) =
      swFin (swAt G P Q s k₀ q₀ (.dn d i m))
        (llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d (exE G P Q s k₀ q₀ d i).length 1)
        (exE G P Q s k₀ q₀ d i) := by
  rw [← ll_next_level (exE G P Q s k₀ q₀ d i).length hi (length_exE G P Q s k₀ q₀ d i) m, swFin, LV_dn',
    List.append_assoc, ← exE_eq, hi, sw_next_level]
  simp [swAt]

theorem sw_fin_c {d i m : ℕ} (hd : d + 1 = q₀) (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length) :
    swAt G P Q s k₀ q₀ (.up (d + 1) 0 0) =
      swFin (swAt G P Q s k₀ q₀ (.dn d i m))
        (llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d (exE G P Q s k₀ q₀ d i).length 0)
        (exE G P Q s k₀ q₀ d i) := by
  rw [← ll_down_end (exE G P Q s k₀ q₀ d i).length hd hi (length_exE G P Q s k₀ q₀ d i) m, swFin, LV_dn',
    List.append_assoc, ← exE_eq, hi, sw_down_end hd]
  simp [swAt]

theorem sw_fin_d {d i m : ℕ} (hd : d < q₀) (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (h0 : (lvR G P Q s k₀ q₀ (d + 1)).length = 0) :
    swAt G P Q s k₀ q₀ (.up d 0 0) =
      swFin (swAt G P Q s k₀ q₀ (.dn d i m))
        (llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d (exE G P Q s k₀ q₀ d i).length (q₀ - d - 1))
        (exE G P Q s k₀ q₀ d i) := by
  rw [← ll_down_empty (exE G P Q s k₀ q₀ d i).length hd hi h0 (length_exE G P Q s k₀ q₀ d i) m, swFin,
    LV_dn', List.append_assoc, ← exE_eq, hi, sw_down_empty hd h0]
  have : outW G P Q s k₀ q₀ (d + 1) = [] := by
    rw [← List.length_eq_zero_iff, length_outW, h0]
  simp [swAt, this]

/-! ### The item words -/

/-- The index of item `j` of level `d` in the words of the state at `dn d i m`. -/
theorem ws_item_j {d i m j : ℕ} (hj : j < (lvR G P Q s k₀ q₀ d).length) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws[4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length +
        (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length + (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length +
        offL G P Q s k₀ q₀ d + j]? = some (itemW (lvR G P Q s k₀ q₀ d)[j]) := by
  set w := swAt G P Q s k₀ q₀ (.dn d i m)
  have hLV : w.LV = lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := by simp [w, swAt]
  have hg := lvsW_get G P Q s k₀ q₀ (le_refl d) hj (nxW G P Q s k₀ q₀ d i)
  rw [← hLV] at hg
  have hws : w.ws = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)) ++ (w.LV ++ w.OU) := by
    simp [SW.ws]
  have hl : (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)).length =
      4 + w.SG.length + w.FA.length + w.CO.length := by simp; omega
  have hidx : offL G P Q s k₀ q₀ d + j < w.LV.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [hws, List.getElem?_append_right (by omega), hl,
    show 4 + w.SG.length + w.FA.length + w.CO.length + offL G P Q s k₀ q₀ d + j -
      (4 + w.SG.length + w.FA.length + w.CO.length) = offL G P Q s k₀ q₀ d + j by omega,
    List.getElem?_append_left hidx, hg]

/-- The first item of the next level among the old item words. -/
theorem ws_item_next {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hn : 0 < (nxW G P Q s k₀ q₀ d i).length) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws[4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length +
        (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length + (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length +
        offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length]? =
      (lvW G P Q s k₀ q₀ (d + 1))[0]? := by
  set w := swAt G P Q s k₀ q₀ (.dn d i m)
  have hLV : w.LV = lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := by simp [w, swAt]
  have hws : w.ws = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)) ++ (w.LV ++ w.OU) := by
    simp [SW.ws]
  have hl : (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)).length =
      4 + w.SG.length + w.FA.length + w.CO.length := by simp; omega
  have hlv : (lvsW G P Q s k₀ q₀ d).length = offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length := by
    rw [length_lvsW, offL_succ]
  obtain ⟨Z, hZ⟩ := nxW_prefix G P Q s k₀ q₀ d (i := i) (j := (lvR G P Q s k₀ q₀ d).length) (by omega)
  rw [nxW_full] at hZ
  rw [hws, List.getElem?_append_right (by omega), hl,
    show 4 + w.SG.length + w.FA.length + w.CO.length + offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length -
      (4 + w.SG.length + w.FA.length + w.CO.length) = (lvsW G P Q s k₀ q₀ d).length by omega,
    hLV, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self, hZ,
    List.getElem?_append_left hn, List.getElem?_append_left hn]

/-- The first item of the next level is the first new word when no old one is there. -/
theorem exE_item_next {d i : ℕ} (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (hn : (nxW G P Q s k₀ q₀ d i).length = 0) :
    (exE G P Q s k₀ q₀ d i)[0]? = (lvW G P Q s k₀ q₀ (d + 1))[0]? := by
  have h := exE_eq G P Q s k₀ q₀ d i
  rw [hi, nxW_full, List.length_eq_zero_iff.1 hn, List.nil_append] at h
  rw [h]

theorem lvW_get {d j : ℕ} (hj : j < (lvR G P Q s k₀ q₀ d).length) :
    (lvW G P Q s k₀ q₀ d)[j]? = some (itemW (itm G P Q s k₀ q₀ d j)) := by
  rw [itm_eq G P Q s k₀ q₀ hj]; simp [lvW, List.getElem?_eq_getElem hj]

/-! ### The calls -/

theorem atQW_eq (σ : TypeTree) :
    atQW (ctW G P Q) P Q (if s then 1 else 0) σ = toWord (atomQ G P Q s k₀ q₀ σ) := by
  rw [atQW, atomQ_words, ctCols_ctW]; rfl

theorem callOf_dn0 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    callOf G P Q s k₀ q₀ (.dn d i 0) = .shift (itm G P Q s k₀ q₀ d i).2 := by
  rw [callOf_dn' hi (by have := two_le_nDn G P Q s k₀ q₀ hi; omega)]; simp

theorem callOf_up0 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    callOf G P Q s k₀ q₀ (.up d i 0) = .canon (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) := by
  rw [callOf_up' hi (by unfold nUp; split_ifs <;> omega)]; simp

theorem next_up0_ne_fin {d : ℕ} (hd : d < q₀ ∨ 0 < d) : next G P Q s k₀ q₀ (.up d 0 0) ≠ .fin := by
  simp only [next, nUp]
  split_ifs <;> simp_all <;> omega

theorem winOf_up0 {d : ℕ} (hd : d < q₀ ∨ 0 < d) : winOf G P Q s k₀ q₀ (.up d 0 0) = 0 := by
  simp [winOf, next_up0_ne_fin G P Q s k₀ q₀ hd]

theorem tagOf_up0 {d : ℕ} (hd : d < q₀ ∨ 0 < d) : tagOf G P Q s k₀ q₀ (.up d 0 0) = 1 := by
  simp [tagOf, winOf_up0 G P Q s k₀ q₀ hd]

end Lax185574Proofs.ResolveRam.Glue
