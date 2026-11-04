import Lax185574Proofs.ResolveRam.Glue.CFinT
import Lax185574Proofs.ResolveRam.Glue.CFinE

/-!
The finishing of an item on the way down, from the library with the
compositions of the item (`fE_ok`): the expansion of the item, then the
end of the round by the next position.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

theorem scR_finEV : ∀ y ∈ scR, y ∉ finEV := by decide

/-- The finishing of an item. -/
noncomputable def fE (atC : Com) : Com := .seq finE (gate (finT' atC))

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem itm_shape1 (hk : 1 ≤ k₀) {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ (q ℓ : ℕ) (t : Node (q + 1) ℓ), (itm G P Q s k₀ q₀ d i).2 = ⟨k₀ + d, q + 1, ℓ, t⟩ ∧ q + 1 = q₀ - d := by
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk hd.le hi
  obtain ⟨e, he⟩ : ∃ e, q₀ - d = e + 1 := ⟨q₀ - d - 1, by omega⟩
  rw [itm_eq G P Q s k₀ q₀ hi]
  revert t
  rw [he]
  intro t hx
  exact ⟨e, ℓ, t, hx, rfl⟩

/-- The cost of the expansion of item `i` of level `d`. -/
noncomputable def kFE (d i m : ℕ) (b : List ℕ) : ℕ :=
  kFinE ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [] :: coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) b d
    (cEx * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + (itm G P Q s k₀ q₀ d i).2.ℓ +
      total (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length +
      rhoPlus (k₀ + 1) q₀ + 1) ^ aEx) (exE G P Q s k₀ q₀ d i)

set_option maxHeartbeats 6400000 in
/-- **The finishing of an item.** -/
theorem fE_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {W d i m : ℕ} {wx b : List ℕ} {τ0 τ : Env} (hk : 1 ≤ k₀) (hkq : kq0 < W) (hd : d < q₀)
    (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nDn G P Q s k₀ q₀ d i)
    (P0 : PreR W (rhoPlus (k₀ + 1) q₀ + 2) (scW G P Q s k₀ q₀ (.dn d i m)) (swAt G P Q s k₀ q₀ (.dn d i m)).ws
      wx b τ0)
    (M : FinMid W (scW G P Q s k₀ q₀ (.dn d i m)) b
      ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [] :: coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) τ0 τ)
    (hm0 : τ.vars "m0" = (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length) :
    FinUpOut W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
      (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (finPs G P Q s k₀ q₀ d i m) (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))) b
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (kFE G P Q s k₀ q₀ d i m b + 104 + kBr G P Q s k₀ q₀ hAt hAV d i m b (next G P Q s k₀ q₀ (.dn d i m)))
      (fE atC) τ0 τ := by
  set R := rhoPlus (k₀ + 1) q₀ + 2
  set w := swAt G P Q s k₀ q₀ (.dn d i m)
  set C := coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2
  have hR : 1 ≤ R := by omega
  have hkq24 : 2 ^ 24 * 64 ≤ kq0 := by unfold kq0; exact Nat.mul_le_mul_left _ (by omega)
  have hw4 := length_SW_ws w
  have hwl := length_ws_parts w
  have g := M.hsc
  have hdd : τ.vars "dd" = d := by have := g 10 (by omega); rw [scW_dn] at this; exact this
  have hii : τ.vars "ii" = i := by have := g 11 (by omega); rw [scW_dn] at this; exact this
  have hnS : τ.vars "nSG" = w.SG.length := by have := g 13 (by omega); rw [scW_dn] at this; exact this
  have hnF : τ.vars "nFA" = w.FA.length := by have := g 14 (by omega); rw [scW_dn] at this; exact this
  have hnC : τ.vars "nCO" = w.CO.length := by have := g 15 (by omega); rw [scW_dn] at this; exact this
  have hgP : τ.vars "gP" = P := by have := g 4 (by omega); rw [scW_dn] at this; exact this
  have hgQ : τ.vars "gQ" = Q := by have := g 5 (by omega); rw [scW_dn] at this; exact this
  have hgS : τ.vars "gS" = if s then 1 else 0 := by have := g 6 (by omega); rw [scW_dn] at this; exact this
  have hz0 : τ.vars "z0" = 0 := by
    rw [M.hfr "z0" (by simp)]; have := P0.hsc 0 (by omega); rw [scW_dn] at this; exact this
  have hit := ws_item_j G P Q s k₀ q₀ (d := d) (i := i) (m := m) (j := i) hi
  have hiw := (List.getElem?_eq_some_iff.1 hit).1
  have hitw : w.ws[4 + w.SG.length + w.FA.length + w.CO.length + offL G P Q s k₀ q₀ d + i]'hiw =
      itemW (itm G P Q s k₀ q₀ d i) := by
    rw [itm_eq G P Q s k₀ q₀ hi]; exact (List.getElem?_eq_some_iff.1 hit).2
  obtain ⟨q, ℓ, t, hσ, hq⟩ := itm_shape1 G P Q s k₀ q₀ hk hd hi
  have hLLl := length_LL_dn G P Q s k₀ q₀ d i m
  have hrq : rhoPlus (k₀ + d + 1) q ≤ rhoPlus (k₀ + 1) q₀ := by
    have h1 : k₀ + d + 1 = k₀ + (d + 1) := by omega
    have h2 : q = q₀ - (d + 1) := by rw [← Nat.sub_sub]; exact Nat.eq_sub_of_add_eq hq
    rw [h1, h2]; exact rho_lvl (by omega)
  have hCw : ∀ x ∈ C, ∃ ν : TypeTree, x = toWord ν := by
    intro x hx
    simp only [C, coW, List.mem_map] at hx
    obtain ⟨ν, -, rfl⟩ := hx
    exact ⟨_, rfl⟩
  obtain ⟨τ1, KE, rE, hKE, hO, fr1, ya1, xa1, ar1, hl1, o1, i1, hB1⟩ :=
    finE_run (W := W) (R := R) (d := d) (i := i) (oL := offL G P Q s k₀ q₀ d) (p := (itm G P Q s k₀ q₀ d i).1.1)
      (g := (itm G P Q s k₀ q₀ d i).1.2) (k := k₀ + d) (q := q) (ℓ := ℓ) (t := t) (nS := w.SG.length)
      (nF := w.FA.length) (nC := w.CO.length) (P := P) (Q := Q) (sg := if s then 1 else 0) (ws := w.ws) (C := C)
      (b := b) M.hW (by omega) M.harr M.hlt M.hlib hm0 (by rw [M.hfr "rR" (by simp)]; exact P0.hrR) hz0
      (by rw [M.hfr "bl" (by simp)]; exact P0.hbl) (fun j hj => by rw [M.hy]; exact P0.hy j hj) M.hov hdd hii
      hnS hnF hnC hw4 (by rw [ws3_dn]; omega) (by rw [ws3_dn]; exact sum_LL G P Q s k₀ q₀) hiw
      (by rw [hitw, ← hσ]) (by rw [ws0_dn]; exact isCT_ctW G P Q) hgP hgQ hgS (by split_ifs <;> omega) hCw
      (by show _ ≤ rhoPlus (k₀ + 1) q₀ + 2; omega)
  have hE : (exW (dwOf P Q (if s then 1 else 0) (w.ws[0]'(by omega))) (k₀ + d) q ℓ (toWord t) C).map (i :: ·) =
      exE G P Q s k₀ q₀ d i := by
    rw [exE_words G P Q s k₀ q₀ hi hσ, ws0_dn]; simp only [C, hσ]; rfl
  have hL1 : finL1 G P Q s k₀ q₀ d i m =
      w.ws ++ [] :: C ++ (exW (dwOf P Q (if s then 1 else 0) (w.ws[0]'(by omega))) (k₀ + d) q ℓ (toWord t) C).map (i :: ·) := by
    rw [hE]; rfl
  have hℓ : (itm G P Q s k₀ q₀ d i).2.ℓ = ℓ := by rw [hσ]
  have hpow : cEx * ((w.ws[0]'(by omega)).length + 1) * (w.ws[4 + w.SG.length + w.FA.length + w.CO.length +
        offL G P Q s k₀ q₀ d + i].length + ℓ + total C + C.length + rhoPlus (k₀ + d + 1) q + 1) ^ aEx ≤
      cEx * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + (itm G P Q s k₀ q₀ d i).2.ℓ +
        total C + C.length + rhoPlus (k₀ + 1) q₀ + 1) ^ aEx := by
    rw [ws0_dn, hitw, hℓ]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hKE' : KE ≤ kFE G P Q s k₀ q₀ d i m b := by
    show KE ≤ kFinE (w.ws ++ [] :: C) b d (cEx * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length +
      (itm G P Q s k₀ q₀ d i).2.ℓ + total C + C.length + rhoPlus (k₀ + 1) q₀ + 1) ^ aEx) (exE G P Q s k₀ q₀ d i)
    unfold kFinE at hKE ⊢; rw [← hE]; omega
  have hnx : τ.vars "nx" = τ0.vars "nx" := M.hfr "nx" (by simp)
  have hmw : τ.vars "mw" = τ0.vars "mw" := M.hfr "mw" (by simp)
  unfold FinUpOut
  by_cases hov1 : τ1.vars "ovf" = 0
  swap
  · refine ⟨τ1, _, Run.seq rE (gate_skip hov1 (hl1.vars "ovf")), by omega, fun h => absurd h hov1,
      fun hB => hB1 _ ?_ (by rw [hnx, hmw]; exact hB)⟩
    rw [← hL1]; exact List.sublist_append_left _ _
  obtain ⟨L1, he0, hpc, -, how, S, hS1, hS2, hS3⟩ := hO hov1
  have FP : FinPre G P Q s k₀ q₀ W R d i m wx b τ0 τ1 := by
    refine ⟨P0, ⟨by rw [fr1 "W" (by decide)]; exact M.hW, ar1, hl1, by rw [hL1]; exact L1,
      fun j h => by rw [fr1 _ (scR_finEV _ (List.getElem_mem _))]; exact M.hsc j h,
      fun y hy => by rw [fr1 y (by revert y; decide)]; exact M.hfr y hy, by rw [ya1]; exact M.hy, hov1,
      by rw [o1]; exact M.hout⟩, by rw [fr1 "m0" (by decide)]; exact hm0, he0, ?_, how,
      ⟨S, by rw [hL1]; exact hS1, hS2, hS3⟩⟩
    rw [hpc, ← hE, List.length_map]
  obtain ⟨τ', K, r, hK, hO', hB'⟩ := finT_ok G P Q s k₀ q₀ hAt hAV hk hkq hd hi hm FP
  exact ⟨τ', _, Run.seq rE (gate_run hov1 (by omega) r), by omega, hO', hB'⟩

end Lax185574Proofs.ResolveRam.Glue
