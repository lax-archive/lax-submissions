import Lax185574Proofs.ResolveRam.Glue.SemDn
import Lax185574Proofs.ResolveRam.Glue.CaseLib

/-!
The case of a later round after the rank shift of an item on the way
down (position `dn d i 0`).

The case appends the empty word and the answer of the shift to the
library, takes the state of `dn d i 1` as ranges (`psRep1`, `case_shift`)
and prepares the far tree of the item: the item word is word
`4 + |SG| + offL d + i` of the library, the scatter type is the range
`4, …, 4 + |SG| - 1`, and the cut is `k + 1` with `k` the entry `2` of
the item word (`bShift_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam

/-- The fixed answers cut at the end of the answer of a rank shift. -/
noncomputable def dlS : ℕ := yB0.length + yC0.length + yE0.length + yF0.length

/-- The scalars of the new head and of the far tree. -/
def hdS : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit 1), ("Nd", .var "dd"), ("Ni", .var "ii"), ("Nm", .lit 1),
    ("NSG", .var "nSG"), ("NFA", .var "nFA"), ("NCO", .var "nCO"), ("NLV", .var "nLV"),
    ("ox", .add (.add (.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO")) (.var "oL")) (.var "ii")),
    ("flo", .lit 4), ("fN", .var "nSG"), ("qk", .lit 1), ("po", .lit 0)]

/-- The plan `psRep1`. -/
def plS : List (Expr × Expr) :=
  [(.lit 0, .lit 1), (.add (.var "m0") (.lit 1), .lit 1), (.lit 2, .sub (.var "m0") (.lit 2))]

/-- The case after the rank shift. -/
noncomputable def bShift : Com :=
  .seq (.assign "m0" (.var "m")) (.seq apE (.seq (apY 0 dlS) (.seq sumLL (.seq (asgs hdS)
    (.seq (.assign "ck" (.add (.get "a" (.add (.get "st" (.var "ox")) (.lit 2))) (.lit 1))) (stPlan plS))))))

/-- The cost of the case after the rank shift. -/
def kShift (b : List ℕ) (d : ℕ) : ℕ := b.length * 18 + d * 20 + 2000

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem dLen_shift (τ : TypeTree) : dLen (.shift τ) = dlS := by
  simp [dLen, dlS]; omega

set_option maxHeartbeats 1600000 in
/-- **The case after the rank shift.** -/
theorem bShift_ok {d i W R : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hR : 1 ≤ R) :
    BodyCall bShift W R (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.dn d i 0))
      (swAt G P Q s k₀ q₀ (.dn d i 0)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.dn d i 0)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 0)))
      ((swAt G P Q s k₀ q₀ (.dn d i 0)).ws ++ [[], toWord (shOf G (itm G P Q s k₀ q₀ d i).2)])
      (psRep1 (swAt G P Q s k₀ q₀ (.dn d i 0)).ws.length)
      (kindOf (callOf G P Q s k₀ q₀ (.dn d i 1))) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1)))
      (tagOf G P Q s k₀ q₀ (.dn d i 1)) (winOf G P Q s k₀ q₀ (.dn d i 1)) (scW G P Q s k₀ q₀ (.dn d i 1))
      (kShift (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 0))) d) := by
  intro τ0 P0 hov hkq
  have hn2 := two_le_nDn G P Q s k₀ q₀ hi
  set t := (itm G P Q s k₀ q₀ d i).2
  have hc0 : callOf G P Q s k₀ q₀ (.dn d i 0) = .shift t := by
    rw [callOf_dn' hi (by omega)]; simp [t]
  have hc1 : callOf G P Q s k₀ q₀ (.dn d i 1) = .ftree t := by
    rw [callOf_dn' hi (by omega)]; simp [t]
  rw [hc0] at P0 ⊢
  rw [hc1]
  set w0 := swAt G P Q s k₀ q₀ (.dn d i 0)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.shift t)
  set Y := toWord (shOf G t)
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  -- the scalars of the state
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i 0)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW_dn] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW_dn] using hsc 11 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW_dn] using hsc 13 (by omega)
  have hFA : τ0.vars "nFA" = 0 := by simpa [scR, scW_dn, w0, FA_dn0] using hsc 14 (by omega)
  have hCO : τ0.vars "nCO" = 0 := by simpa [scR, scW_dn, w0, CO_dn0] using hsc 15 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW_dn] using hsc 16 (by omega)
  have hwsl : ws.length = 4 + w0.SG.length + w0.FA.length + w0.CO.length + w0.LV.length + w0.OU.length := by
    simp only [ws, SW.ws, List.length_append, List.length_cons, List.length_nil]
  have hwsW : ws.length + 2 ≤ W := by omega
  -- step 1: m0
  set τ1 := τ0.setVar "m0" ws.length
  have r1 : Run (W + 1) (.assign "m0" (.var "m")) τ0 τ1 2 := Run.assign (ev_var P0.hlib.m (by omega))
  have L1 : Lib ws τ1 := P0.hlib.of (by simp [τ1]) (by simp [τ1]) rfl rfl rfl
  have ar1 : ArrW W τ1 := P0.harr
  -- step 2: the empty word
  obtain ⟨τ2, r2, L2, f2, a2, ar2, o2, i2⟩ := apE_run L1 ar1 (by omega)
  -- step 3: the answer
  have hyb : SegAt "y" 0 b τ2 := fun j hj => by rw [a2 "y" (by decide)]; exact P0.hy j hj
  have hbv : ∀ v ∈ b, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := P0.hy j hj
    have := hl0.arrs "y" _ (List.mem_of_getElem? (by simpa using this))
    omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.shift t)
  have hdl : dlS ≤ b.length := by
    rw [← dLen_shift t, ← hpp]; simp only [b, hsp, List.length_append]; omega
  obtain ⟨τ3, r3, L3, f3, a3, ar3, o3, i3⟩ := apY_run (pl := 0) (dl := dlS) L2 ar2
    (by rw [f2 "bl" (by decide), show τ1.vars "bl" = τ0.vars "bl" by simp [τ1], P0.hbl]) hyb hdl
    (by omega) (by simp only [total_append, total_single, List.length_append, List.length_cons,
      List.length_nil]; omega) hbv
  have hYw : (b.drop 0).take (b.length - dlS) = Y := by
    have := realY_seg G k₀ q₀ (.shift t)
    rw [dLen_shift] at this; exact this
  rw [hYw, List.append_assoc] at L3
  set L := ws ++ [[], Y]
  have hL3 : (L[3]'(by simp [L]; omega)) = w0.LL := by
    simp only [L, ws, SW.ws]; simp
  have hLL : w0.LL = llW G P Q s k₀ q₀ d ++ [(nxL G P Q s k₀ q₀ d i).length] := LL_dn G P Q s k₀ q₀ d i 0
  have fr3 : ∀ y, y ∉ apV → y ≠ "m0" → τ3.vars y = τ0.vars y := fun y h1 h2 => by
    rw [f3 y h1, f2 y h1]; simp [τ1, h2]
  have ar3' : ∀ b', b' ∉ ["a", "st", "ln"] → τ3.arrs b' = τ0.arrs b' := fun b' hb => by
    rw [a3 b' hb, a2 b' hb]; rfl
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt (Run.seq r1 (Run.seq r2 r3)) hl0
  have hLl : L.length = ws.length + 2 := by simp [L]
  -- step 4: the offset of level d
  have hlvs : offL G P Q s k₀ q₀ d ≤ w0.LV.length := by
    rw [LV_dn, List.length_append, length_lvsW, offL_succ]; omega
  have hLLl : d ≤ (L[3]'(by omega)).length := by rw [hL3, hLL]; simp [llW]; omega
  have hsum : ((L[3]'(by omega)).take d).sum = offL G P Q s k₀ q₀ d := by rw [hL3]; exact sum_LL G P Q s k₀ q₀
  obtain ⟨τ4, r4, s4, f4, a4, o4, i4⟩ := sumLL_run (W := W) (d := d) (L := L) L3.at_ (by omega)
    (by rw [fr3 "dd" (by decide) (by decide), hdd]) hLLl (by rw [hsum]; omega) hl3 ar3 (by omega)
  rw [hsum] at s4
  have fr4 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ4.vars y = τ0.vars y := fun y h1 h2 h3 h4 => by
    rw [f4 y h3 h4, fr3 y h1 h2]
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  -- step 5: the head scalars and the far tree
  have hitem := ws_item' G P Q s k₀ q₀ (m := 0) hi
  rw [FA_dn0, CO_dn0] at hitem
  simp only [List.length_nil, Nat.add_zero] at hitem
  set iw := 4 + w0.SG.length + offL G P Q s k₀ q₀ d + i
  have hiw : iw < ws.length := (List.getElem?_eq_some_iff.1 hitem).1
  have hv4 : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ4 = some v := fun y v h1 h2 h3 h4 h =>
    ev_var (by rw [fr4 y h1 h2 h3 h4, h]) (by rw [← h, ← fr4 y h1 h2 h3 h4]; exact hl4.vars _)
  let fS : String → ℕ := fun y =>
    if y = "Nt" ∨ y = "Nph" ∨ y = "Nm" ∨ y = "qk" then 1 else if y = "Nd" then d else if y = "Ni" then i
    else if y = "NSG" ∨ y = "fN" then w0.SG.length else if y = "NLV" then w0.LV.length
    else if y = "ox" then iw else if y = "flo" then 4 else 0
  obtain ⟨τ5, r5, s5, f5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4) (l := hdS) (f := fS)
    (by
      intro p hp
      simp only [hdS, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show fS "Nt" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nw" = 0 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nph" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nd" = d by simp [fS]]
        exact hv4 "dd" _ (by decide) (by decide) (by decide) (by decide) hdd
      · rw [show fS "Ni" = i by simp [fS]]
        exact hv4 "ii" _ (by decide) (by decide) (by decide) (by decide) hii
      · rw [show fS "Nm" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "NSG" = w0.SG.length by simp [fS]]
        exact hv4 "nSG" _ (by decide) (by decide) (by decide) (by decide) hSG
      · rw [show fS "NFA" = 0 by simp [fS]]
        exact hv4 "nFA" _ (by decide) (by decide) (by decide) (by decide) hFA
      · rw [show fS "NCO" = 0 by simp [fS]]
        exact hv4 "nCO" _ (by decide) (by decide) (by decide) (by decide) hCO
      · rw [show fS "NLV" = w0.LV.length by simp [fS]]
        exact hv4 "nLV" _ (by decide) (by decide) (by decide) (by decide) hLV
      · rw [show fS "ox" = iw by simp [fS]]
        have e1 := hv4 "nSG" _ (by decide) (by decide) (by decide) (by decide) hSG
        have e2 := hv4 "nFA" _ (by decide) (by decide) (by decide) (by decide) hFA
        have e3 := hv4 "nCO" _ (by decide) (by decide) (by decide) (by decide) hCO
        have e4 := hv4 "ii" _ (by decide) (by decide) (by decide) (by decide) hii
        have e5 : (Expr.var "oL").evalB (W + 1) τ4 = some (offL G P Q s k₀ q₀ d) := ev_var s4 (by omega)
        rw [show iw = 4 + w0.SG.length + 0 + 0 + offL G P Q s k₀ q₀ d + i by simp [iw]]
        exact ev_add (ev_add (ev_add (ev_add (ev_add (evalB_lit (by omega)) e1 (by omega)) e2 (by omega)) e3
          (by omega)) e5 (by omega)) e4 (by omega)
      · rw [show fS "flo" = 4 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "fN" = w0.SG.length by simp [fS]]
        exact hv4 "nSG" _ (by decide) (by decide) (by decide) (by decide) hSG
      · rw [show fS "qk" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "po" = 0 by simp [fS]]; exact evalB_lit (by omega))
    (by decide)
  have fr5 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ hdS.map Prod.fst →
      τ5.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 => by rw [f5 y h5, fr4 y h1 h2 h3 h4]
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  have ar5 : ArrW W τ5 := fun b' => by rw [a5, a4]; exact ar3 b'
  have hw5 : WordsAt L τ5 := L3.at_.of_arrs (by rw [a5, a4]) (by rw [a5, a4]) (by rw [a5, a4])
  have hox : τ5.vars "ox" = iw := by rw [s5 "ox" (by decide)]; simp [fS]
  -- step 6: the cut
  have hLiw : (L[iw]'(by omega)) = itemW (lvR G P Q s k₀ q₀ d)[i] := by
    have h1 : L[iw]? = ws[iw]? := by simp only [L]; rw [List.getElem?_append_left hiw]
    rw [hitem] at h1
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h1)
  have ht : (lvR G P Q s k₀ q₀ d)[i].2 = t := by simp [t, itm_eq G P Q s k₀ q₀ hi]
  have hL2 : (L[iw]'(by omega))[2]'(by rw [hLiw]; simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]) = t.k := by
    simp only [hLiw, itemW, ← ht]; simp [Lax185574Proofs.FarRam.toWord_typeTree]
  have hck0 := ev_wd (j := 2) hw5 hox (by omega) (by rw [hLiw]; simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]) hl5 ar5
  rw [hL2] at hck0
  have htk : t.k + 1 < W + 1 := by
    have hmem : itemW (lvR G P Q s k₀ q₀ d)[i] ∈ ws := List.mem_of_getElem? hitem
    have : t.k ∈ ws.flatten := List.mem_flatten.2 ⟨_, hmem, by
      simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree, ← ht]⟩
    have := le_maxEntry this
    omega
  set τ6 := τ5.setVar "ck" (t.k + 1)
  have r6 : Run (W + 1) (.assign "ck" (.add (.get "a" (.add (.get "st" (.var "ox")) (.lit 2))) (.lit 1))) τ5 τ6
      9 := (Run.assign (ev_add hck0 (evalB_lit (by omega)) htk)).mono (by simp)
  -- step 7: the plan
  have hm06 : τ6.vars "m0" = ws.length := by
    simp only [τ6, Env.setVar, show ("m0" : String) ≠ "ck" by decide, if_false]
    rw [f5 _ (by decide), f4 _ (by decide) (by decide), f3 _ (by decide), f2 _ (by decide)]; simp [τ1]
  obtain ⟨τ7, r7, PR7, np7, f7, a7, l7, o7, i7⟩ := stPlan_run (W := W) (l := plS) (ps := psRep1 ws.length)
    (τ := τ6) rfl (by simp [τ6]; exact ar5 "PR") (by simp [plS]; omega)
    (by
      intro j hj
      simp only [plS, List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨ev_add (ev_var hm06 (by omega)) (evalB_lit (by omega)) (by omega), evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), ev_sub (ev_var hm06 (by omega)) (evalB_lit (by omega)) (by omega)⟩)
    (by decide)
  have fr7 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ∉ hdS.map Prod.fst → y ≠ "ck" → y ≠ "np" →
      τ7.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 h7 => by
    rw [f7 y h7]; simp only [τ6, Env.setVar, if_neg h6]; exact fr5 y h1 h2 h3 h4 h5
  have hS7 : ∀ y, y ∈ hdS.map Prod.fst → τ7.vars y = fS y := fun y hy => by
    rw [f7 y (by intro h; subst h; simp [hdS] at hy)]
    simp only [τ6, Env.setVar, if_neg (show y ≠ "ck" by intro h; subst h; simp [hdS] at hy)]
    exact s5 y hy
  have hrun : Run (W + 1) bShift τ0 τ7 (kShift b d) := by
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    simp only [kShift, asgK, hdS, plS, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt hrun hl0
  have ar7 : ArrW W τ7 := fun b' => by
    by_cases hb : b' = "PR"
    · subst hb; exact l7
    · rw [a7 b' hb]; exact ar5 b'
  have ha7 : ∀ b', b' ≠ "PR" → τ7.arrs b' = τ3.arrs b' := fun b' hb => by
    rw [a7 b' hb]; simp only [τ6]; show τ5.arrs b' = _; rw [a5, a4]
  have hov7 : τ7.vars "ovf" = 0 := by
    rw [fr7 "ovf" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hov]
  have hscR : ∀ y ∈ scR, y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧ y ≠ "fk" ∧ y ∉ hdS.map Prod.fst ∧ y ≠ "ck" ∧
      y ≠ "np" := by decide
  have hv7 : ∀ y v, y ∈ scR → τ0.vars y = v → τ7.vars y = v := fun y v hy h => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hscR y hy
    rw [← h]; exact fr7 y a1 a2 a3 a4 a5 a6 a7
  have g : ∀ j (h : j < 9), τ7.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i 0)).getD j 0 := fun j h =>
    hv7 _ _ (List.getElem_mem _) (hsc j (by omega))
  refine ⟨τ7, kShift b d, hrun, le_rfl, fun _ => ⟨⟨?_, hkq, ar7, hl7, ?_, hR, ?_, ?_, ?_, ?_, ?_, hov7, ?_, ?_,
    PR7, np7, ?_, by simp [psRep1]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => hov7⟩
  · rw [fr7 "W" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), P0.hW]
  · rw [fr7 "rR" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), P0.hrR]
  · refine L3.of ?_ ?_ (ha7 "a" (by decide)) (ha7 "st" (by decide)) (ha7 "ln" (by decide))
    · rw [f7 "m" (by decide)]; simp only [τ6, Env.setVar]; simp; rw [f5 _ (by decide), f4 _ (by decide) (by decide)]
    · rw [f7 "lt" (by decide)]; simp only [τ6, Env.setVar]; simp; rw [f5 _ (by decide), f4 _ (by decide) (by decide)]
  · simpa [scR, scW_dn] using g 0 (by omega)
  · rw [fr7 "bl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), P0.hbl]
  · intro j hj; rw [ha7 "y" (by decide), ar3' "y" (by decide)]; exact P0.hy j hj
  · simpa [scR, scW_dn] using g 1 (by omega)
  · -- the real query of the far tree
    refine ⟨fun h => by simp [kindOf] at h, fun _ => ?_, fun h => by simp [kindOf] at h,
      fun h => by simp [kindOf] at h, by simp [kindOf]⟩
    have hiwL : iw < L.length := by omega
    have hd2 : (L[iw]'hiwL).drop 2 = toWord t := by rw [hLiw]; simp [itemW, ← ht]
    have hsel : selW L 4 w0.SG.length (cutSel (t.k + 1)) = w0.SG.filter (cutSel (t.k + 1)) := by
      simp only [selW, L, ws, SW.ws]; congr 1; simp [List.take_append_of_le_length]
    refine ⟨iw, hiwL, 4, w0.SG.length, t.k + 1, by rw [hLiw]; simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree],
      by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS7 "ox" (by simp [hdS])]; simp [fS]
    · rw [hS7 "flo" (by simp [hdS])]; simp [fS]
    · rw [hS7 "fN" (by simp [hdS])]; simp [fS]
    · rw [f7 "ck" (by decide)]; simp [τ6]
    · rw [realQ_ftree, hd2, hsel, SG_dn]
  · rw [hS7 "qk" (by simp [hdS])]; simp [fS, kindOf]
  · intro p hp; simp [psRep1] at hp; rcases hp with rfl | rfl | rfl <;> simp [hLl] <;> omega
  · rw [hS7 "Nt" (by simp [hdS])]; simp [fS, tagOf_dn]
  · rw [hS7 "Nw" (by simp [hdS])]; simp [fS, winOf_dn]
  · rw [scW_dn, SG_dn, FA_dn1, CO_dn1, LV_dn]
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega); have h5 := g 5 (by omega)
    have h6 := g 6 (by omega); have h7 := g 7 (by omega); have h8 := g 8 (by omega)
    simp only [scR, scW_dn, List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp only [hsV, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      hS7 "Nph" (by simp [hdS]), hS7 "Nd" (by simp [hdS]), hS7 "Ni" (by simp [hdS]), hS7 "Nm" (by simp [hdS]),
      hS7 "NSG" (by simp [hdS]), hS7 "NFA" (by simp [hdS]), hS7 "NCO" (by simp [hdS]),
      hS7 "NLV" (by simp [hdS])]
    simp [fS, w0, SG_dn, LV_dn]
  · rw [hS7 "po" (by simp [hdS])]; simp [fS]
  · rw [fr7 "nx" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [fr7 "mw" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [o7]; simp only [τ6]; show τ5.out = []; rw [o5, o4, o3, o2]; simp [τ1, P0.hout]

end Lax185574Proofs.ResolveRam.Glue
