import Lax185574Proofs.ResolveRam.Glue.ClauseJ
import Lax185574Proofs.ResolveRam.Glue.CaseDn

/-!
Facts on the positions on the way down, for the cases of the later
rounds: the windows and tags (`winOf_dn`, `tagOf_dn`), the item words in
the state (`ws_item`), the sum of the level lengths before level `d`
(`sum_LL`), and the step after the rank shift (`next_dn0`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem next_dn_ne_fin (d i m : ℕ) : next G P Q s k₀ q₀ (.dn d i m) ≠ .fin := by
  simp only [next]; split_ifs <;> simp

theorem winOf_dn (d i m : ℕ) : winOf G P Q s k₀ q₀ (.dn d i m) = 0 := by
  simp [winOf, next_dn_ne_fin]

theorem tagOf_dn (d i m : ℕ) : tagOf G P Q s k₀ q₀ (.dn d i m) = 1 := by
  simp [tagOf, winOf_dn]

theorem sum_LL {d i m : ℕ} : (((swAt G P Q s k₀ q₀ (.dn d i m)).LL).take d).sum = offL G P Q s k₀ q₀ d := by
  simp only [swAt, llW, offL]
  rw [List.take_append_of_le_length (by simp), List.range_succ, List.map_append,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

theorem ws_item {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ h : 4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
        (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length + offL G P Q s k₀ q₀ d + i <
        (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length,
      (swAt G P Q s k₀ q₀ (.dn d i m)).ws[4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length +
        (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length + (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length +
        offL G P Q s k₀ q₀ d + i] = itemW (lvR G P Q s k₀ q₀ d)[i] := by
  set w := swAt G P Q s k₀ q₀ (.dn d i m)
  have hLV : w.LV = lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := by simp [w, swAt]
  have hg := lvsW_get G P Q s k₀ q₀ (le_refl d) hi (nxW G P Q s k₀ q₀ d i)
  rw [← hLV] at hg
  have hws : w.ws = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)) ++ (w.LV ++ w.OU) := by
    simp [SW.ws]
  have hl : (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)).length =
      4 + w.SG.length + w.FA.length + w.CO.length := by simp; omega
  have hidx : offL G P Q s k₀ q₀ d + i < w.LV.length := (List.getElem?_eq_some_iff.1 hg).1
  have hget : w.ws[4 + w.SG.length + w.FA.length + w.CO.length + offL G P Q s k₀ q₀ d + i]? =
      some (itemW (lvR G P Q s k₀ q₀ d)[i]) := by
    rw [hws, List.getElem?_append_right (by omega), hl,
      show 4 + w.SG.length + w.FA.length + w.CO.length + offL G P Q s k₀ q₀ d + i -
        (4 + w.SG.length + w.FA.length + w.CO.length) = offL G P Q s k₀ q₀ d + i by omega,
      List.getElem?_append_left hidx, hg]
  exact ⟨(List.getElem?_eq_some_iff.1 hget).1, (List.getElem?_eq_some_iff.1 hget).2⟩

theorem ws_item' {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).ws[4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length +
        (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length + (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length +
        offL G P Q s k₀ q₀ d + i]? = some (itemW (lvR G P Q s k₀ q₀ d)[i]) := by
  obtain ⟨h, e⟩ := ws_item G P Q s k₀ q₀ (m := m) hi
  rw [List.getElem?_eq_getElem h, e]

theorem next_dn0 {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    next G P Q s k₀ q₀ (.dn d i 0) = .dn d i 1 := by
  have := two_le_nDn G P Q s k₀ q₀ hi
  simp only [next]; rw [if_pos (by omega)]

theorem callOf_dn_comp {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : 2 ≤ m)
    (hmn : m < nDn G P Q s k₀ q₀ d i) :
    ∃ h : m - 2 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length,
      callOf G P Q s k₀ q₀ (.dn d i m) = .compose (shOf G (itm G P Q s k₀ q₀ d i).2)
        (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2)[m - 2] := by
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  refine ⟨by omega, ?_⟩
  rw [callOf_dn' hi hmn]
  simp only [show m ≠ 0 by omega, show m ≠ 1 by omega, if_false]
  rw [List.getD_eq_getElem _ _ (by omega)]

theorem FA_dn0 {d i : ℕ} : (swAt G P Q s k₀ q₀ (.dn d i 0)).FA = [] := by simp [swAt]
theorem CO_dn0 {d i : ℕ} : (swAt G P Q s k₀ q₀ (.dn d i 0)).CO = [] := by simp [swAt]
theorem FA_dn1 {d i : ℕ} : (swAt G P Q s k₀ q₀ (.dn d i 1)).FA = [] := by simp [swAt]
theorem CO_dn1 {d i : ℕ} : (swAt G P Q s k₀ q₀ (.dn d i 1)).CO = [] := by simp [swAt]

theorem scW_dn (d i m : ℕ) : scW G P Q s k₀ q₀ (.dn d i m) =
    [0, ySz (xIn G k₀ q₀ P Q s), (xIn G k₀ q₀ P Q s).length, n, P, Q, if s then 1 else 0, k₀, q₀, 1, d, i, m,
      (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length, (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length,
      (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length, (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length] := by
  simp [scW, curW]

theorem SG_dn (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.dn d i m)).SG = (Lax185574.ScatterTypes.stp G k₀ q₀).words := by
  simp [swAt]

theorem LV_dn (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.dn d i m)).LV =
    lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := by
  simp [swAt]

theorem LL_dn (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.dn d i m)).LL =
    llW G P Q s k₀ q₀ d ++ [(nxL G P Q s k₀ q₀ d i).length] := by
  simp [swAt]

end Lax185574Proofs.ResolveRam.Glue
