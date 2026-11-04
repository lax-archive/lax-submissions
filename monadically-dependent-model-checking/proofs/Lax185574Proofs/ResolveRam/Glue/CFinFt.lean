import Lax185574Proofs.ResolveRam.Glue.CFinF
import Lax185574Proofs.ResolveRam.Glue.CFtree

/-!
The case after the far tree when no member passes: the item is finished
(`bFtE_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax185574.ResolveLift
open Lax3.DistFO (rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

set_option maxHeartbeats 6400000 in
/-- **The case after the far tree, when no member passes.** -/
theorem bFtE_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {d i W : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF0 : (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length = 0) :
    BodyCall (bFt (fE atC)) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.dn d i 1))
      (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.dn d i 1)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1)))
      (finL1 G P Q s k₀ q₀ d i 1 ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1)))
      (finPs G P Q s k₀ q₀ d i 1) (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1))))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1)))
      (kFt (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
        ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord) (kFA G P Q s k₀ q₀ d i)
        (kFE G P Q s k₀ q₀ d i 1 (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))) + 104 +
          kBr G P Q s k₀ q₀ hAt hAV d i 1 (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1)))
            (next G P Q s k₀ q₀ (.dn d i 1)))) := by
  intro τ0 P0 hov hkq
  set t := (itm G P Q s k₀ q₀ d i).2
  set F := faP G (dataOf G P Q s k₀ q₀) t
  set Lf := (faOf G t).map toWord
  have hnd : nDn G P Q s k₀ q₀ d i = 2 + F.length := nDn_itm hi
  have hc1 : callOf G P Q s k₀ q₀ (.dn d i 1) = .ftree t := by
    rw [callOf_dn' hi (by have := two_le_nDn G P Q s k₀ q₀ hi; omega)]; simp [t]
  rw [hc1] at P0 ⊢
  set w0 := swAt G P Q s k₀ q₀ (.dn d i 1)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.ftree t)
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  have hSH : w0.SH = toWord (shOf G t) := by simp [w0, swAt, t]
  have hCT : w0.CT = ctW G P Q := by simp [w0, swAt]
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i 1)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW_dn] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW_dn] using hsc 11 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW_dn] using hsc 13 (by omega)
  have hCO : τ0.vars "nCO" = 0 := by simpa [scR, scW_dn, w0, CO_dn1] using hsc 15 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW_dn] using hsc 16 (by omega)
  have hgP : τ0.vars "gP" = P := by simpa [scR, scW_dn] using hsc 4 (by omega)
  have hgQ : τ0.vars "gQ" = Q := by simpa [scR, scW_dn] using hsc 5 (by omega)
  have hgS : τ0.vars "gS" = (if s then 1 else 0) := by simpa [scR, scW_dn] using hsc 6 (by omega)
  have hOU : w0.OU = [] := OU_dn G P Q s k₀ q₀ d i 1
  have hFA0 : w0.FA = [] := FA_dn1 G P Q s k₀ q₀
  have hCO0 : w0.CO = [] := CO_dn1 G P Q s k₀ q₀
  have hwsl : ws.length = 4 + w0.SG.length + w0.LV.length := by
    simp only [ws, SW.ws, List.length_append, List.length_cons, List.length_nil, hOU, hFA0, hCO0]; omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.ftree t)
  have hpl : plF + (realY G k₀ q₀ (.ftree t)).length ≤ b.length := by
    rw [show plF = preLen (.ftree t) from rfl, ← hpre]; simp only [b, hsp, List.length_append]; omega
  have hbW : b.length < W + 1 := by rw [← P0.hbl]; exact hl0.vars _
  -- step 1: the scalars of the piece
  let f1 : String → ℕ := fun y => if y = "m0" then ws.length else if y = "os" then 1 else if y = "yo" then plF else 0
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ0)
    (l := [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)]) (f := f1)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · rw [show f1 "m0" = ws.length by simp [f1]]; exact ev_var P0.hlib.m (by omega)
      · rw [show f1 "oc" = 0 by simp [f1]]; exact evalB_lit (by omega)
      · rw [show f1 "os" = 1 by simp [f1]]; exact evalB_lit (by omega)
      · rw [show f1 "yo" = plF by simp [f1]]
        exact evalB_lit (by omega))
    (by decide)
  have hv1 : ∀ y, y ∉ ["m0", "oc", "os", "yo"] → τ1.vars y = τ0.vars y := fun y hy => g1 y (by simpa using hy)
  have hm01 : τ1.vars "m0" = ws.length := by rw [s1 "m0" (by simp)]; simp [f1]
  -- step 2: the piece FA
  have hws0 : 0 < ws.length := by omega
  have hws1 : 1 < ws.length := by omega
  have h0 : ws[0] = ctW G P Q := by rw [← hCT]; simp [ws, SW.ws]
  have h1 : ws[1] = toWord (shOf G t) := by rw [← hSH]; simp [ws, SW.ws]
  obtain ⟨wsh, hwsh⟩ := sh_itm G P Q s k₀ q₀ hk hd hi
  have hsk : (toWord (shOf G t)).getD 0 0 = k₀ + d + 1 := by
    rw [show shOf G t = _ from hwsh, Lax185574Proofs.FarRam.toWord_typeTree]; rfl
  have hsq : (toWord (shOf G t)).getD 1 0 = q₀ - d - 1 := by
    rw [show shOf G t = _ from hwsh, Lax185574Proofs.FarRam.toWord_typeTree]; rfl
  have hyl : SegAt "y" 0 b τ1 := fun j hj => by rw [a1]; exact P0.hy j hj
  have hYAt : YAt (toWord Lf) plF τ1 := by
    intro j hj
    have hr : realY G k₀ q₀ (.ftree t) = toWord Lf := rfl
    have hj' : plF + j < b.length := by rw [← hr] at hj; omega
    have hy' := hyl (plF + j) hj'
    rw [Nat.zero_add] at hy'
    rw [hy']
    have hpre' : pre.length = plF := hpre
    have hjr : j < (realY G k₀ q₀ (.ftree t)).length := by rw [hr]; exact hj
    simp only [b, hsp]
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simp only [hpre', Nat.add_sub_cancel_left, hr]
  have hPW : P ≤ W := by rw [← hgP]; have := hl0.vars "gP"; omega
  have hQW : Q ≤ W := by rw [← hgQ]; have := hl0.vars "gQ"; omega
  have hlw1 := hl0
  have hRoom : Room W (rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0))
      (ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0) := by
    set So := sOfV τ0 ws b
    have hr : realY G k₀ q₀ (.ftree t) = toWord Lf := rfl
    have hm1 : maxEntry (toWord ws) ≤ total ws + ws.length + maxEntry ws.flatten :=
      maxEntry_le fun v hv => mem_toWord_bound hv (by omega) (fun w hw x hx => by
        have := le_maxEntry (List.mem_flatten.2 ⟨w, hw, hx⟩); omega)
    have hl1 := length_toWord_words ws
    have hm2 : maxEntry (toWord Lf) ≤ maxEntry b :=
      maxEntry_le fun v hv => le_maxEntry (by rw [← hr] at hv; simp only [b, hsp]; simp [hv])
    have hl2 : (toWord Lf).length ≤ b.length := by rw [← hr]; omega
    have h12 : ws[1].getD 2 0 ≤ maxEntry ws.flatten := by
      rw [List.getD_eq_getElem?_getD]
      rcases h : ws[1][2]? with _ | v
      · simp
      · have := le_maxEntry (List.mem_flatten.2 ⟨ws[1], List.getElem_mem _, List.mem_of_getElem? h⟩)
        simpa using this
    have hSo : ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0 + 1 ≤ 5 * So := by
      simp only [ySz, List.length_nil]; omega
    have hR' : rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1 ≤ R := by
      rw [h1, hsk, hsq]; have := rho_sh (k₀ := k₀) (q₀ := q₀) hd; simp only [R]; omega
    unfold Room
    have hroom' := hroom
    unfold RoomOK at hroom'
    calc 2 ^ 16 * (rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1) ^ 2 *
          (ySz (toWord ws) + ySz (toWord Lf) + plF + ([] : List ℕ).length + ws[1].getD 2 0 + 1) ^ 2
        ≤ 2 ^ 16 * R ^ 2 * (5 * So) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR' 2)) (Nat.pow_le_pow_left hSo 2)
      _ ≤ 2 ^ 24 * R * R * R * R * So * So := by
          have : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by omega)
          have := Nat.mul_le_mul_right (So * So) (Nat.mul_le_mul_left (2 ^ 16 * 25) this)
          nlinarith
      _ ≤ W := hroom'.le
  obtain ⟨τ2, r2, F2, pc2, P2⟩ := faSpec' W τ1 ws Lf [] 0 1 plF P Q (if s then 1 else 0) hws0 hws1
    (by rw [hv1 "W" (by decide), P0.hW]) (fun b' => by rw [a1]; exact P0.harr b')
    (P0.hlib.at_.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1]))
    (by rw [s1 "oc" (by simp)]; simp [f1]) (by rw [s1 "os" (by simp)]; simp [f1]) (by rw [s1 "yo" (by simp)]; simp [f1])
    (by rw [hv1 "gP" (by decide), hgP]) (by rw [hv1 "gQ" (by decide), hgQ]) hPW hQW
    (by rw [hv1 "gS" (by decide), hgS]) (by split_ifs <;> omega)
    (by rw [h0]; exact isCT_ctW G P Q) ⟨_, h1⟩ (fun w hw => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hw; exact ⟨ν, rfl⟩) hYAt
    (filled_of_po (by rw [hv1 "po" (by decide), P0.hpo])) hRoom
  have hK2 : cFA * ((toWord Lf).length + ws[0].length + 1) *
      (ws[1].length + ws[1].getD 2 0 + maxLen Lf + rhoPlus (ws[1].getD 0 0) (ws[1].getD 1 0) + 1) ^ aFA =
      kFA G P Q s k₀ q₀ d i := by rw [h0, h1]; rfl
  rw [hK2] at r2
  have hFw : Lf.filter (passSel (dwOf P Q (if s then 1 else 0) ws[0]) ws[1]) = F.map toWord := by
    rw [h0, h1, faP_words (dW_ok G P Q s k₀ q₀)]; rfl
  rw [hFw] at F2 pc2
  simp only [List.nil_append] at F2
  set F' := F.map toWord
  have hv2 : ∀ y, y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ2.vars y = τ0.vars y := fun y h1 h2 => by
    rw [P2.vars y h1, hv1 y h2]
  have ha2 : ∀ b', b' ∈ keepA → τ2.arrs b' = τ0.arrs b' := fun b' hb => by rw [P2.arrs b' hb, a1]
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt (Run.seq r1 r2) hl0
  have ar2 : ArrW W τ2 := fun b' => by rw [P2.len, a1]; exact P0.harr b'
  have L2 : Lib ws τ2 := P0.hlib.of (by rw [hv2 "m" (by decide) (by decide)]) (by rw [hv2 "lt" (by decide) (by decide)])
    (ha2 "a" (by decide)) (ha2 "st" (by decide)) (ha2 "ln" (by decide))
  -- step 3: the room check after the piece
  obtain ⟨τ3, r3, ov3, f3, a3, u3, i3⟩ := rmLs_run (R := R) (ws := ws) (b := b) (τ := τ2)
    (by rw [hv2 "W" (by decide) (by decide), P0.hW]) (by omega)
    (by rw [hv2 "rR" (by decide) (by decide), P0.hrR]) L2
    (by rw [hv2 "z0" (by decide) (by decide)]; simpa [scR, scW_dn] using hsc 0 (by omega))
    (by rw [hv2 "bl" (by decide) (by decide), P0.hbl]) (fun j hj => by rw [ha2 "y" (by decide)]; exact P0.hy j hj)
    ar2 hl2
  rw [hv2 "ovf" (by decide) (by decide), hov] at ov3
  have hpo2 : τ2.vars "po" = (frames F').length := F2.pos
  have hF'0 : F' = [] := by simp [F', List.length_eq_zero_iff.1 hF0]
  have hbig2 : BigRoom W R (finL1 G P Q s k₀ q₀ d i 1 ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1))) b
      (τ0.vars "nx") (τ0.vars "mw") → RoomOK W R τ2 ws b := by
    intro hB
    refine roomOK_of_big (L := finL1 G P Q s k₀ q₀ d i 1 ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i 1)))
      ((List.sublist_append_left ws _).trans (by rw [finL1_ws, List.append_assoc]; try exact List.sublist_append_left _ _))
      ?_ (by rw [hv2 "nx" (by decide) (by decide), hv2 "mw" (by decide) (by decide)]; exact hB)
    rw [hpo2, hF'0]; simp [frames]
  by_cases hr3 : RoomOK W R τ2 ws b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
    have hrun : Run (W + 1) (bFt (fE atC)) τ0 τ3 (kFt b ws F' (kFA G P Q s k₀ q₀ d i) 0) := by
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_skip (by rw [ov3]; omega)
        (by rw [ov3]; omega))))).mono ?_
      have hA : asgK [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)] = 9 := rfl
      rw [hA]; unfold kFt; clear * -; omega
    exact ⟨τ3, _, hrun, by unfold kFt; omega, fun h => by rw [ov3] at h; omega, fun hB => absurd (hbig2 hB) hr3⟩
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
  have hS2 := room_bound hr3 hR
  obtain ⟨hT1, hT2, hT3, hT4⟩ := sOfV_ge (τ := τ2) (ws := ws) (b := b)
  rw [hpo2, length_frames] at hT1
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have ar3 : ArrW W τ3 := fun b' => by rw [a3]; exact ar2 b'
  have L3 : Lib ws τ3 := L2.of (by rw [f3 "m" (by decide)]) (by rw [f3 "lt" (by decide)]) (by rw [a3])
    (by rw [a3]) (by rw [a3])
  have hv3 : ∀ y, y ∉ rmLs.wvars → y ∉ faV → y ∉ ["m0", "oc", "os", "yo"] → τ3.vars y = τ0.vars y :=
    fun y h0 h1 h2 => by rw [f3 y h0, hv2 y h1 h2]
  -- step 4: the empty word
  obtain ⟨τ4, r4, L4, f4, a4, ar4, o4, i4⟩ := apE_run L3 ar3 (by omega)
  have hpc4 : τ4.vars "pc" = F.length := by
    rw [f4 "pc" (by decide), f3 "pc" (by decide), pc2]; simp [F']
  -- step 5: the scalars of the copy
  obtain ⟨τ5, r5, s5, f5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4)
    (l := [("ls", .lit 0), ("lN", .var "pc")]) (f := fun y => if y = "ls" then 0 else F.length)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [if_true]; exact evalB_lit (by omega)
      · simp only [show ("lN" : String) ≠ "ls" by decide, if_false]
        exact ev_var hpc4 (by rw [← hpc4]; exact (Run.envLt r4 hl3).vars _))
    (by decide)
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 (Run.envLt r4 hl3)
  have L5 : Lib (ws ++ [[]]) τ5 := L4.of (by rw [f5 "m" (by decide)]) (by rw [f5 "lt" (by decide)])
    (by rw [a5]) (by rw [a5]) (by rw [a5])
  -- step 6: the filtered words
  have hOB : τ5.arrs "OB" = τ2.arrs "OB" := by rw [a5, a4 "OB" (by decide), a3]
  have hseg : SegAt "OB" 0 (frames F') τ5 := fun j hj => by
    rw [hOB, Nat.zero_add]; exact F2.get j hj
  have hFv : ∀ w ∈ F', ∀ v ∈ w, v ≤ W := by
    intro w hw v hv
    have hm : v ∈ frames F' := by
      simp only [frames, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨w, hw, rfl⟩, List.mem_cons_of_mem _ hv⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    have := hl2.arrs "OB" _ (List.mem_of_getElem? (F2.get j hj))
    omega
  have htF : total F' + F'.length = (frames F').length := (length_frames F').symm
  obtain ⟨τ6, r6, L6, ls6, f6, a6, l6, o6, i6⟩ := lbFr_run (W := W) (src := "OB") (L := F') (p := 0) L5
    (by rw [s5 "ls" (by simp)]; simp) (by rw [s5 "lN" (by simp)]; simp [F']) hseg (by decide)
    (by rw [a5, ar4 "a"]; simp only [total_append, total_single, List.length_nil]; omega)
    (by rw [a5, ar4 "st"]; simp; omega) (by rw [a5, ar4 "ln"]; simp; omega)
    (by
      have e1 : total (ws ++ [[]]) = total ws := by simp [total]
      rw [e1, List.length_append, List.length_singleton]; omega) hFv
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have ar6 : ArrW W τ6 := fun b' => by rw [l6, a5]; exact ar4 b'
  rw [List.append_assoc, List.singleton_append] at L6
  set L := ws ++ ([] :: F')
  have hLl : L.length = ws.length + 1 + F.length := by simp [L, F']; omega
  have fr6 : ∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] → y ∉ apV → y ∉ rmLs.wvars → y ∉ faV →
      y ∉ ["m0", "oc", "os", "yo"] → τ6.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
    have h1a : y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a3, a4, a5, a6⟩
    have h1' : y ∉ [("ls", Expr.lit 0), ("lN", Expr.var "pc")].map Prod.fst := by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨a6, a7⟩
    rw [f6 y h1a, f5 y h1', f4 y h2, hv3 y h3 h4 h5]
  have hpc6 : τ6.vars "pc" = F.length := by
    rw [f6 "pc" (by decide), f5 "pc" (by decide)]; exact hpc4
  -- step 7: the test
  have hc7 : (Cond.eq (.var "pc") (.lit 0)).evalB (W + 1) τ6 = some true := by
    rw [evalB_condEq (ev_var hpc6 (by rw [← hpc6]; exact hl6.vars _)) (evalB_lit (by omega))]
    rw [show F.length = 0 from hF0]; rfl
  -- step 8: the end of the item
  have hm06 : τ6.vars "m0" = ws.length := by
    rw [f6 _ (by decide), f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), P2.vars _ (by decide)]
    exact hm01
  have hC0 : coW G P Q s k₀ q₀ t = [] := by
    have hF' : faP G (dataOf G P Q s k₀ q₀) t = [] := List.length_eq_zero_iff.1 hF0
    simp only [coW, hF', List.map_nil]
  have hm : 1 + 1 = nDn G P Q s k₀ q₀ d i := by omega
  have hsR : ∀ y ∈ scR, y ∉ ["fk", "ci", "lt", "m", "lL", "ls", "lN"] ∧ y ∉ apV ∧ y ∉ rmLs.wvars ∧
      y ∉ faV ∧ y ∉ ["m0", "oc", "os", "yo"] := by decide
  have M6 : FinMid W (scW G P Q s k₀ q₀ (.dn d i 1)) b (ws ++ [] :: coW G P Q s k₀ q₀ t) τ0 τ6 := by
    refine ⟨?_, ar6, hl6, by
      have e : L = ws ++ [] :: coW G P Q s k₀ q₀ t := by simp only [L, hF'0, hC0]
      rw [← e]; exact L6, fun j h => ?_, fun y hy => ?_, ?_, ?_, ?_⟩
    · rw [fr6 "W" (by decide) (by decide) (by decide) (by decide) (by decide), P0.hW]
    · obtain ⟨e1, e2, e3, e4, e5⟩ := hsR _ (List.getElem_mem (l := scR) (n := j) (by simp [scR]; omega))
      rw [fr6 _ e1 e2 e3 e4 e5]
      exact hsc j h
    · exact fr6 y (by revert y; decide) (by revert y; decide) (by revert y; decide) (by revert y; decide)
        (by revert y; decide)
    · rw [a6 "y" (by decide), a5, a4 "y" (by decide), a3, ha2 "y" (by decide)]
    · rw [f6 "ovf" (by decide), f5 "ovf" (by decide), f4 "ovf" (by decide), ov3]
    · rw [o6, o5, o4, u3, P2.out, o1]; exact P0.hout
  obtain ⟨τ', K, r, hK, hO, hB⟩ := fE_ok G P Q s k₀ q₀ hAt hAV hk hkq hd hi hm P0 M6 hm06
  have hrun : Run (W + 1) (bFt (fE atC)) τ0 τ' (kFt b ws F' (kFA G P Q s k₀ q₀ d i)
      (kFE G P Q s k₀ q₀ d i 1 b + 104 + kBr G P Q s k₀ q₀ hAt hAV d i 1 b (next G P Q s k₀ q₀ (.dn d i 1)))) := by
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_run (by rw [ov3]) (by omega)
      (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.ite_true hc7 r)))))))).mono ?_
    have hA : asgK [("m0", .var "m"), ("oc", .lit 0), ("os", .lit 1), ("yo", .lit plF)] = 9 := rfl
    have hB : asgK [("ls", .lit 0), ("lN", .var "pc")] = 5 := rfl
    rw [hA, hB]; simp only [Cond.size, Expr.size]; unfold kFt; omega
  exact ⟨τ', _, hrun, le_rfl, hO, hB⟩

end Lax185574Proofs.ResolveRam.Glue
