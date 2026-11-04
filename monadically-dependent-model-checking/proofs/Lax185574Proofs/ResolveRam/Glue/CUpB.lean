import Lax185574Proofs.ResolveRam.Glue.DispDef
import Lax185574Proofs.ResolveRam.Glue.CUpO
import Lax185574Proofs.ResolveRam.Glue.CFinU

/-!
The case after the last call of an item on the way up, when a call
follows (position `up d i m`, `m + 1 = nUp q₀ d`): the output word of the
item is appended to the outputs, and the query of the atom words of the
next item is written (`bUpB_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The cost of the case after an item on the way up, without the atom words. -/
def kUpB (b : List ℕ) (ws : List (List ℕ)) (d : ℕ) : ℕ :=
  60 * b.length + 40 * total ws + d * 20 + 3000

/-- The constant of the cost of the atom words. -/
noncomputable def cAt {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  (atT_run hAt hAV).choose

/-- The exponent of the cost of the atom words. -/
noncomputable def aAt {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  (atT_run hAt hAV).choose_spec.choose

theorem kAtT_mono {L : List (List ℕ)} {b w : List ℕ} {KA KA' : ℕ} (h : KA ≤ KA') :
    kAtT L b w KA ≤ kAtT L b w KA' := by
  unfold kAtT; omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The level of the next item on the way up. -/
noncomputable def nxD (d i : ℕ) : ℕ := if i + 1 < (lvR G P Q s k₀ q₀ d).length then d else d - 1

/-- The index of the next item on the way up. -/
noncomputable def nxI (d i : ℕ) : ℕ := if i + 1 < (lvR G P Q s k₀ q₀ d).length then i + 1 else 0

/-- The number of output words dropped after an item on the way up. -/
noncomputable def pUp (d i : ℕ) : ℕ :=
  if i + 1 < (lvR G P Q s k₀ q₀ d).length then 0 else (ouPre G P Q s k₀ q₀ d).length

theorem next_upB {d i m : ℕ} (hm : m + 1 = nUp q₀ d) (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) :
    next G P Q s k₀ q₀ (.up d i m) = .up (nxD G P Q s k₀ q₀ d i) (nxI G P Q s k₀ q₀ d i) 0 := by
  have h1 : ¬ (m + 1 < nUp q₀ d) := by omega
  simp only [next, if_neg h1] at hnf ⊢
  unfold nxD nxI
  split_ifs at hnf ⊢ with h2 h3 <;> simp_all

theorem lvR_pos_pred {d : ℕ} (h : 0 < (lvR G P Q s k₀ q₀ (d + 1)).length) : 0 < (lvR G P Q s k₀ q₀ d).length := by
  by_contra h0
  rw [← nxL_full, show (lvR G P Q s k₀ q₀ d).length = 0 by omega, nxL_zero] at h
  simp at h

theorem nx_valid {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nUp q₀ d)
    (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) :
    nxD G P Q s k₀ q₀ d i ≤ q₀ ∧ nxI G P Q s k₀ q₀ d i < (lvR G P Q s k₀ q₀ (nxD G P Q s k₀ q₀ d i)).length := by
  have h1 : ¬ (m + 1 < nUp q₀ d) := by omega
  unfold nxD nxI
  split_ifs with h
  · exact ⟨hd, h⟩
  · have hd0 : d ≠ 0 := by
      intro h0; subst h0; apply hnf; simp only [next]; rw [if_neg h1, if_neg h]; simp
    refine ⟨by omega, ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simpa using lvR_pos_pred G P Q s k₀ q₀ (d := e) (by omega)

theorem winOf_upB {d i : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    winOf G P Q s k₀ q₀ (.up d i 0) =
      if q₀ = 0 ∧ i + 1 = (lvR G P Q s k₀ q₀ 0).length then (xIn G k₀ q₀ P Q s).length else 0 := by
  unfold winOf
  simp only [next, nUp]
  by_cases hq : q₀ = 0
  · subst hq
    have hd0 : d = 0 := by omega
    subst hd0
    by_cases h1 : i + 1 < (lvR G P Q s k₀ 0 0).length
    · simp [h1]; omega
    · simp [h1]; omega
  · by_cases h2 : d < q₀
    · simp [h2, hq]
    · have hd0 : d ≠ 0 := by omega
      split_ifs <;> simp_all

theorem sw_upB_same {d i m : ℕ} (hi : i + 1 < (lvR G P Q s k₀ q₀ d).length) :
    swAt G P Q s k₀ q₀ (.up d (i + 1) 0) =
      { swAt G P Q s k₀ q₀ (.up d i m) with
        AT := []
        OU := (swAt G P Q s k₀ q₀ (.up d i m)).OU.drop 0 ++
          [(outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega)] } := by
  rw [List.drop_zero]; exact sw_up_item (by omega)

theorem sw_upB_level {d i m : ℕ} (hd : d + 1 ≤ q₀) (hi : i + 1 = (lvR G P Q s k₀ q₀ (d + 1)).length) :
    swAt G P Q s k₀ q₀ (.up d 0 0) =
      { swAt G P Q s k₀ q₀ (.up (d + 1) i m) with
        AT := []
        OU := (swAt G P Q s k₀ q₀ (.up (d + 1) i m)).OU.drop (ouPre G P Q s k₀ q₀ (d + 1)).length ++
          [(outW G P Q s k₀ q₀ (d + 1))[i]'(by rw [length_outW]; omega)] } := by
  rw [sw_up_level (m := m) hd]
  have e1 : (swAt G P Q s k₀ q₀ (.up (d + 1) i m)).OU.drop (ouPre G P Q s k₀ q₀ (d + 1)).length ++
      [(outW G P Q s k₀ q₀ (d + 1))[i]'(by rw [length_outW]; omega)] = outW G P Q s k₀ q₀ (d + 1) := by
    rw [swAt_up_OU, List.drop_left, ← outP_succ G P Q s k₀ q₀ (by omega), hi, outP_full G P Q s k₀ q₀ (d + 1)]
  have e2 : ((swAt G P Q s k₀ q₀ (.up (d + 1) 0 m)).OU ++ outW G P Q s k₀ q₀ (d + 1)).drop
      (ouPre G P Q s k₀ q₀ (d + 1)).length = outW G P Q s k₀ q₀ (d + 1) := by
    rw [swAt_up_OU, outP, List.take_zero, List.append_nil, List.drop_left]
  rw [e1, e2]
  simp [swAt]

/-- The output word of an item on the way up from the state. -/
theorem outW_upB (hk : 1 ≤ k₀) {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nUp q₀ d) :
    (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega) =
      ((itemW (itm G P Q s k₀ q₀ d i)).drop 2).take 3 ++ (swAt G P Q s k₀ q₀ (.up d i m)).AT ++
        realY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m)) := by
  rcases Nat.lt_or_ge d q₀ with h | h
  · have hm1 : m = 1 := by simp [nUp, h] at hm; omega
    subst hm1
    rw [outWord_succ hk h hi, callOf_up' hi (by omega)]
    simp [itemW]; rfl
  · have hdq : d = q₀ := by omega
    subst hdq
    have hm0 : m = 0 := by simp [nUp] at hm; omega
    subst hm0
    rw [outWord_top hk hi, callOf_up' hi (by omega)]
    simp [itemW, swAt]; rfl

/-- **The plan after an item on the way up gives the state of the next position.** -/
theorem case_upB {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nUp q₀ d)
    (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) (AQ : List ℕ) :
    planW ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++ [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega), AQ])
      (psUp (swAt G P Q s k₀ q₀ (.up d i m)) (swAt G P Q s k₀ q₀ (.up d i m)).ws.length
        ((swAt G P Q s k₀ q₀ (.up d i m)).ws.length + 1) (pUp G P Q s k₀ q₀ d i)) =
      (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))).ws := by
  have hOUl := length_OU_up G P Q s k₀ q₀ d i m
  rw [min_eq_left hi.le] at hOUl
  have hp : pUp G P Q s k₀ q₀ d i ≤ (swAt G P Q s k₀ q₀ (.up d i m)).OU.length := by
    unfold pUp; split_ifs <;> omega
  rw [planW_up _ _ _ hp rfl rfl, next_upB G P Q s k₀ q₀ hm hnf]
  unfold nxD nxI pUp
  by_cases h : i + 1 < (lvR G P Q s k₀ q₀ d).length
  · simp only [if_pos h]
    rw [sw_upB_same G P Q s k₀ q₀ (m := m) h]
  · simp only [if_neg h]
    have hd0 : d ≠ 0 := by
      intro h0; subst h0; apply hnf
      simp only [next]; rw [if_neg (show ¬ (m + 1 < nUp q₀ 0) by omega), if_neg h]; simp
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [sw_upB_level G P Q s k₀ q₀ (m := m) (i := i) (by omega) (by omega)]

set_option maxHeartbeats 6400000 in
/-- **The case after the last call of an item on the way up.** -/
theorem bUpB_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    (hk : 1 ≤ k₀) {d i m W : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m + 1 = nUp q₀ d)
    (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin) :
    BodyCall (bUpB atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.up d i m))
      (swAt G P Q s k₀ q₀ (.up d i m)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.up d i m)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m)))
      ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++
        [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega),
          realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))])
      (psUp (swAt G P Q s k₀ q₀ (.up d i m)) (swAt G P Q s k₀ q₀ (.up d i m)).ws.length
        ((swAt G P Q s k₀ q₀ (.up d i m)).ws.length + 1) (pUp G P Q s k₀ q₀ d i))
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)))
      (kUpB (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m))) (swAt G P Q s k₀ q₀ (.up d i m)).ws d +
        kAtT ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++ [[], (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega)])
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up d i m)))
          (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m))))
          (cAt hAt hAV * ((ctW G P Q).length + 1) *
            ((itemW (itm G P Q s k₀ q₀ (nxD G P Q s k₀ q₀ d i) (nxI G P Q s k₀ q₀ d i))).length +
              (itm G P Q s k₀ q₀ (nxD G P Q s k₀ q₀ d i) (nxI G P Q s k₀ q₀ d i)).2.ℓ +
              rhoPlus (k₀ + 1) q₀ + 1) ^ aAt hAt hAV)) := by
  intro τ0 P0 hov hkq
  obtain ⟨hD, hI⟩ := nx_valid G P Q s k₀ q₀ hd hi hm hnf
  have hnx := next_upB G P Q s k₀ q₀ hm hnf
  rw [hnx]
  set d' := nxD G P Q s k₀ q₀ d i with hd'
  set i' := nxI G P Q s k₀ q₀ d i with hi'
  set σ' := (itm G P Q s k₀ q₀ d' i').2
  have hc1 : callOf G P Q s k₀ q₀ (.up d' i' 0) = .canon (atomQ G P Q s k₀ q₀ σ') := by
    rw [callOf_up' hI (by unfold nUp; split_ifs <;> omega)]; simp [σ']
  obtain ⟨Qc, hcQ⟩ : ∃ Qc, callOf G P Q s k₀ q₀ (.up d i m) = .canon Qc := by
    rw [callOf_up' hi (by omega)]; split_ifs <;> exact ⟨_, rfl⟩
  have hO := outW_upB G P Q s k₀ q₀ hk hd hi hm
  rw [hcQ] at P0 hO ⊢
  rw [hc1]
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  set w0 := swAt G P Q s k₀ q₀ (.up d i m)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.canon Qc)
  set Y := realY G k₀ q₀ (.canon Qc)
  set O := (outW G P Q s k₀ q₀ d)[i]'(by rw [length_outW]; omega)
  set AQ := realQ G k₀ q₀ (.canon (atomQ G P Q s k₀ q₀ σ'))
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hq0W : q₀ + 2 ≤ W := by
    have h4 : 4 ≤ ws.length := length_SW_ws w0
    have h1 := len_le_total (L := ws) (i := 3) (by omega)
    have h3 : ws[3] = llW G P Q s k₀ q₀ q₀ := by
      rw [← LL_up G P Q s k₀ q₀ d i m]; simp [ws, w0, SW.ws_eq]
    rw [h3, length_llW] at h1
    omega
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.up d i m)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW, curW] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW, curW] using hsc 11 (by omega)
  have hgq : τ0.vars "gq" = q₀ := by simpa [scR, scW, curW] using hsc 8 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW, curW] using hsc 13 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW, curW] using hsc 16 (by omega)
  have hnx0 : τ0.vars "nx" = (xIn G k₀ q₀ P Q s).length := by simpa [scR, scW, curW] using hsc 2 (by omega)
  have hz0 : τ0.vars "z0" = 0 := by simpa [scR, scW, curW] using hsc 0 (by omega)
  have hgP : τ0.vars "gP" = P := by simpa [scR, scW, curW] using hsc 4 (by omega)
  have hgQ : τ0.vars "gQ" = Q := by simpa [scR, scW, curW] using hsc 5 (by omega)
  have hgS : τ0.vars "gS" = if s then 1 else 0 := by simpa [scR, scW, curW] using hsc 6 (by omega)
  have hwsl : ws.length = 4 + w0.SG.length + w0.LV.length + w0.OU.length := by
    rw [show ws = w0.ws from rfl, ws_eq_LV w0 (FA_up G P Q s k₀ q₀ d i m) (CO_up G P Q s k₀ q₀ d i m)]
    simp; omega
  have hOUl : w0.OU.length = (ouPre G P Q s k₀ q₀ d).length + min i (lvR G P Q s k₀ q₀ d).length :=
    length_OU_up G P Q s k₀ q₀ d i m
  rw [min_eq_left hi.le] at hOUl
  have hLVl : w0.LV.length = offL G P Q s k₀ q₀ (q₀ + 1) := by rw [LV_up, length_lvsW]
  have hoffd : offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length ≤ w0.LV.length := by
    rw [hLVl, ← offL_succ]; exact offL_mono G P Q s k₀ q₀ (by omega)
  -- step 1: m0
  set τ1 := τ0.setVar "m0" ws.length
  have r1 : Run (W + 1) (.assign "m0" (.var "m")) τ0 τ1 2 := Run.assign (ev_var P0.hlib.m (by omega))
  have L1 : Lib ws τ1 := P0.hlib.of (by simp [τ1]) (by simp [τ1]) rfl rfl rfl
  have ar1 : ArrW W τ1 := P0.harr
  -- step 2: the empty word
  obtain ⟨τ2, r2, L2, f2, a2, ar2, o2, i2⟩ := apE_run L1 ar1 (by omega)
  set L := ws ++ [[]]
  have hLl : L.length = ws.length + 1 := by simp [L]
  have fr2 : ∀ y, y ∉ apV → y ≠ "m0" → τ2.vars y = τ0.vars y := fun y h1 h2 => by
    rw [f2 y h1]; simp [τ1, h2]
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt (Run.seq r1 r2) hl0
  have hL3 : (L[3]'(by omega)) = llW G P Q s k₀ q₀ q₀ := by
    simp only [L, ws, SW.ws]; simp [w0, LL_up]
  have hL2 : (L[2]'(by omega)) = w0.AT := by simp only [L, ws, SW.ws]; simp
  have hLLl : (L[3]'(by omega)).length = q₀ + 1 := by rw [hL3]; simp [llW]
  -- step 3: the offset of level d
  have hsum : ((L[3]'(by omega)).take d).sum = offL G P Q s k₀ q₀ d := by
    rw [hL3]; exact sum_llW G P Q s k₀ q₀ (by omega)
  obtain ⟨τ3, r3, s3, f3, a3, o3, i3⟩ := sumLL_run (W := W) (d := d) (L := L) L2.at_ (by omega)
    (by rw [fr2 "dd" (by decide) (by decide), hdd]) (by omega) (by rw [hsum]; omega) hl2 ar2 (by omega)
  rw [hsum] at s3
  have fr3 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ3.vars y = τ0.vars y := fun y h1 h2 h3 h4 => by
    rw [f3 y h3 h4, fr2 y h1 h2]
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have ar3 : ArrW W τ3 := fun b' => by rw [a3]; exact ar2 b'
  have hv3 : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ3 = some v := fun y v h1 h2 h3 h4 h =>
    ev_var (by rw [fr3 y h1 h2 h3 h4, h]) (by rw [← h, ← fr3 y h1 h2 h3 h4]; exact hl3.vars _)
  -- step 4: the item word
  set iw := 4 + w0.SG.length + offL G P Q s k₀ q₀ d + i
  have eS3 := hv3 "nSG" _ (by decide) (by decide) (by decide) (by decide) hSG
  have eO3 : (Expr.var "oL").evalB (W + 1) τ3 = some (offL G P Q s k₀ q₀ d) := ev_var s3 (by omega)
  have eI3 := hv3 "ii" _ (by decide) (by decide) (by decide) (by decide) hii
  set τ4 := τ3.setVar "ow" iw
  have r4 : Run (W + 1) (.assign "ow" (.add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii"))) τ3 τ4
      (1 + Expr.size (.add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii"))) :=
    Run.assign (ev_add (ev_add (ev_add (evalB_lit (by omega)) eS3 (by omega)) eO3 (by omega)) eI3 (by omega))
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have L4 : Lib L τ4 := L2.of (by simp [τ4]; rw [f3 "m" (by decide) (by decide)])
    (by simp [τ4]; rw [f3 "lt" (by decide) (by decide)]) (by simp [τ4, a3]) (by simp [τ4, a3]) (by simp [τ4, a3])
  have hitem : L[iw]? = some (itemW (itm G P Q s k₀ q₀ d i)) := by
    rw [List.getElem?_append_left (by
      exact (List.getElem?_eq_some_iff.1 (ws_up_item G P Q s k₀ q₀ (e := d) (i' := i) (m := m) hd hi)).1),
      ws_up_item G P Q s k₀ q₀ (e := d) (i' := i) (m := m) hd hi, itm_eq G P Q s k₀ q₀ hi]
  have hiw : iw < L.length := (List.getElem?_eq_some_iff.1 hitem).1
  have hLiw : L[iw] = itemW (itm G P Q s k₀ q₀ d i) := (List.getElem?_eq_some_iff.1 hitem).2
  have hiw5 : 5 ≤ L[iw].length := by
    rw [hLiw]; simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]
  -- step 5: the output word
  have hyb : SegAt "y" 0 b τ4 := fun j hj => by
    simp only [τ4, arrs_setVar]; rw [a3, a2 "y" (by decide)]; exact P0.hy j hj
  have hbv : ∀ v ∈ b, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := P0.hy j hj
    have := hl0.arrs "y" _ (List.mem_of_getElem? (by simpa using this))
    omega
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.canon Qc)
  have hdl : dlK ≤ b.length := by
    rw [← dLen_canon Qc, ← hpp]; simp only [b, hsp, List.length_append]; omega
  have hpd : plK ≤ dlK := by unfold plK dlK; omega
  have hbl4 : τ4.vars "bl" = b.length := by
    simp only [τ4, vars_setVar, show ("bl" : String) ≠ "ow" by decide, if_false]
    rw [fr3 "bl" (by decide) (by decide) (by decide) (by decide), P0.hbl]
  have hwt : total L = total ws := by simp [L, total]
  obtain ⟨τ5, r5, L5, f5, a5, ar5, hl5, o5, i5⟩ := ouC_run (W := W) (pl := plK) (dl := dlK) (iw := iw) (L := L)
    (b := b) (τ := τ4) (fun b' => by simp only [τ4, arrs_setVar]; exact ar3 b') hl4 L4 (by omega) hiw hiw5
    (by simp [τ4]) hbl4 hyb hdl hpd (by rw [hwt]; omega) hbv
  have hYw : (b.drop plK).take (b.length - dlK) = Y := by
    have := realY_seg G k₀ q₀ (.canon Qc)
    rw [dLen_canon, preLen_canon] at this; exact this
  have hOW : ouW L iw b plK dlK = O := by
    rw [hO, ouW, List.getD_eq_getElem _ _ hiw, List.getD_eq_getElem _ _ (by omega), hLiw, hL2, hYw]
  rw [hOW] at L5
  set L' := L ++ [O]
  have hL'l : L'.length = ws.length + 2 := by simp [L', L]
  have fr5 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → y ∉ ouV → τ5.vars y = τ0.vars y :=
    fun y h1 h2 h3 h4 h5 h6 => by
      rw [f5 y h6]; simp only [τ4, vars_setVar, if_neg h5]; exact fr3 y h1 h2 h3 h4
  have hw5 : WordsAt L' τ5 := L5.at_
  have hL'3 : (L'[3]'(by omega)) = llW G P Q s k₀ q₀ q₀ := by
    rw [show L'[3]'(by omega) = L[3]'(by omega) from List.getElem_append_left (by omega), hL3]
  -- step 6: the next item
  have hv5 : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → y ∉ ouV → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ5 = some v := fun y v h1 h2 h3 h4 h5 h6 h =>
    ev_var (by rw [fr5 y h1 h2 h3 h4 h5 h6, h]) (by rw [← h, ← fr5 y h1 h2 h3 h4 h5 h6]; exact hl5.vars _)
  have hoL5 : τ5.vars "oL" = offL G P Q s k₀ q₀ d := by
    rw [f5 "oL" (by decide)]; simp [τ4]; exact s3
  have hm05 : τ5.vars "m0" = ws.length := by
    rw [f5 "m0" (by decide)]; simp [τ4]; rw [f3 _ (by decide) (by decide), f2 _ (by decide)]; simp [τ1]
  have eD5 := hv5 "dd" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdd
  have eI5 := hv5 "ii" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hii
  have eS5 := hv5 "nSG" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSG
  have eV5 := hv5 "nLV" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hLV
  have eO5 : (Expr.var "oL").evalB (W + 1) τ5 = some (offL G P Q s k₀ q₀ d) := ev_var hoL5 (by omega)
  have eM5 : (Expr.var "m0").evalB (W + 1) τ5 = some ws.length := ev_var hm05 (by omega)
  have eLd : (eLL (.var "dd")).evalB (W + 1) τ5 = some (lvR G P Q s k₀ q₀ d).length := by
    rw [← llW_get G P Q s k₀ q₀ hd]
    exact ev_LL3 hw5 (by omega) hL'3 eD5 _ hl5 ar5 (by omega)
  have eOU : eOU.evalB (W + 1) τ5 = some w0.OU.length := by
    unfold eOU
    have := ev_sub (ev_sub (ev_sub eM5 (evalB_lit (n := 4) (by omega)) (by omega)) eS5 (by omega)) eV5 (by omega)
    rw [show ws.length - 4 - w0.SG.length - w0.LV.length = w0.OU.length by omega] at this
    exact this
  have hnxt : ∃ τ6 K6, Run (W + 1) (.ite (.lt (.add (.var "ii") (.lit 1)) (eLL (.var "dd"))) (asgs nxA) (asgs nxB))
      τ5 τ6 K6 ∧ K6 ≤ 80 ∧ τ6.vars "Nd" = d' ∧ τ6.vars "Ni" = i' ∧
      τ6.vars "ow" = 4 + w0.SG.length + offL G P Q s k₀ q₀ d' + i' ∧ τ6.vars "e0" = pUp G P Q s k₀ q₀ d i ∧
      (∀ y, y ∉ ["Nd", "Ni", "ow", "e0"] → τ6.vars y = τ5.vars y) ∧ τ6.arrs = τ5.arrs ∧ τ6.out = τ5.out ∧
      τ6.inp = τ5.inp := by
    have hc := evalB_condLt (ev_add eI5 (evalB_lit (n := 1) (by omega)) (by omega)) eLd
    by_cases h1 : i + 1 < (lvR G P Q s k₀ q₀ d).length
    · rw [decide_eq_true h1] at hc
      have ed : d' = d := by simp [d', nxD, h1]
      have ei : i' = i + 1 := by simp [i', nxI, h1]
      have ep : pUp G P Q s k₀ q₀ d i = 0 := by simp [pUp, h1]
      let f : String → ℕ := fun y => if y = "Nd" then d else if y = "Ni" then i + 1
        else if y = "ow" then iw + 1 else 0
      obtain ⟨τ6, r6, s6, g6, a6, o6, i6⟩ := asgs_run (B := W + 1) (τ := τ5) (l := nxA) (f := f)
        (by
          intro p hp
          simp only [nxA, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact eD5
          · exact ev_add eI5 (evalB_lit (by omega)) (by omega)
          · exact ev_add (ev_add (ev_add (ev_add (evalB_lit (by omega)) eS5 (by omega)) eO5 (by omega)) eI5
              (by omega)) (evalB_lit (by omega)) (by omega)
          · exact evalB_lit (by omega))
        (by decide)
      refine ⟨τ6, _, Run.ite_true hc r6, ?_, ?_, ?_, ?_, ?_, fun y hy => g6 y (by simpa [nxA] using hy), a6, o6,
        i6⟩
      · simp [asgK, nxA, Expr.size, Cond.size, eLL]
      · rw [s6 "Nd" (by simp [nxA]), ed]; simp [f]
      · rw [s6 "Ni" (by simp [nxA]), ei]; simp [f]
      · rw [s6 "ow" (by simp [nxA]), ed, ei]; simp [f, iw]; omega
      · rw [s6 "e0" (by simp [nxA]), ep]; simp [f]
    · rw [decide_eq_false h1] at hc
      have hd0 : d ≠ 0 := by
        intro h0; subst h0; apply hnf
        simp only [next]; rw [if_neg (show ¬ (m + 1 < nUp q₀ 0) by omega), if_neg h1]; simp
      have ed : d' = d - 1 := by simp [d', nxD, h1]
      have ei : i' = 0 := by simp [i', nxI, h1]
      have ep : pUp G P Q s k₀ q₀ d i = w0.OU.length - i := by
        simp only [pUp, if_neg h1]; omega
      have hoff : offL G P Q s k₀ q₀ d = offL G P Q s k₀ q₀ (d - 1) + (lvR G P Q s k₀ q₀ (d - 1)).length := by
        rw [← offL_succ, Nat.sub_add_cancel (by omega)]
      have eLd1 : (eLL (.sub (.var "dd") (.lit 1))).evalB (W + 1) τ5 = some (lvR G P Q s k₀ q₀ (d - 1)).length := by
        rw [← llW_get G P Q s k₀ q₀ (show d - 1 ≤ q₀ by omega)]
        exact ev_LL3 hw5 (by omega) hL'3 (ev_sub eD5 (evalB_lit (n := 1) (by omega)) (by omega)) _ hl5 ar5
          (by omega)
      let f : String → ℕ := fun y => if y = "Nd" then d - 1 else if y = "Ni" then 0
        else if y = "ow" then 4 + w0.SG.length + offL G P Q s k₀ q₀ (d - 1) else w0.OU.length - i
      obtain ⟨τ6, r6, s6, g6, a6, o6, i6⟩ := asgs_run (B := W + 1) (τ := τ5) (l := nxB) (f := f)
        (by
          intro p hp
          simp only [nxB, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact ev_sub eD5 (evalB_lit (n := 1) (by omega)) (by omega)
          · exact evalB_lit (by omega)
          · simp only [f, show ("ow" : String) ≠ "Nd" by decide, show ("ow" : String) ≠ "Ni" by decide, if_false,
              if_true]
            exact ev_sub (ev_add (ev_add (evalB_lit (by omega)) eS5 (by omega)) eO5 (by omega)) eLd1 (by omega)
              |>.trans (by congr 1; omega)
          · exact ev_sub eOU eI5 (by omega))
        (by decide)
      refine ⟨τ6, _, Run.ite_false hc r6, ?_, ?_, ?_, ?_, ?_, fun y hy => g6 y (by simpa [nxB] using hy), a6, o6,
        i6⟩
      · simp [asgK, nxB, Glue.eOU, Expr.size, Cond.size, eLL]
      · rw [s6 "Nd" (by simp [nxB]), ed]; simp [f]
      · rw [s6 "Ni" (by simp [nxB]), ei]; simp [f]
      · rw [s6 "ow" (by simp [nxB]), ed, ei]; simp [f]
      · rw [s6 "e0" (by simp [nxB]), ep]; simp [f]
  obtain ⟨τ6, K6, r6, hK6, hNd6, hNi6, how6, he06, f6, a6, o6, i6⟩ := hnxt
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have fr6 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → y ∉ ouV → y ∉ ["Nd", "Ni", "ow", "e0"] →
      τ6.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 h7 => by rw [f6 y h7, fr5 y h1 h2 h3 h4 h5 h6]
  -- step 7: the head
  have hv6 : ∀ y v, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → y ∉ ouV →
      y ∉ ["Nd", "Ni", "ow", "e0"] → τ0.vars y = v → (Expr.var y).evalB (W + 1) τ6 = some v :=
    fun y v h1 h2 h3 h4 h5 h6 h7 h =>
      ev_var (by rw [fr6 y h1 h2 h3 h4 h5 h6 h7, h]) (by rw [← h, ← fr6 y h1 h2 h3 h4 h5 h6 h7]; exact hl6.vars _)
  let fH : String → ℕ := fun y =>
    if y = "Nt" then 1 else if y = "Nph" then 2 else if y = "NSG" then w0.SG.length
    else if y = "NLV" then w0.LV.length else if y = "qk" then 3 else 0
  obtain ⟨τ7, r7, s7, g7, a7, o7, i7⟩ := asgs_run (B := W + 1) (τ := τ6) (l := hdB) (f := fH)
    (by
      intro p hp
      simp only [hdB, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact evalB_lit (by omega)
      · exact evalB_lit (by omega)
      · exact evalB_lit (by omega)
      · exact evalB_lit (by omega)
      · exact hv6 "nSG" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSG
      · exact evalB_lit (by omega)
      · exact evalB_lit (by omega)
      · exact hv6 "nLV" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hLV
      · exact evalB_lit (by omega)
      · exact evalB_lit (by omega))
    (by decide)
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt r7 hl6
  -- step 8: the window
  have hw7 : WordsAt L' τ7 := hw5.of_arrs (by rw [a7, a6]) (by rw [a7, a6]) (by rw [a7, a6])
  have ar7 : ArrW W τ7 := fun b' => by rw [a7, a6]; exact ar5 b'
  have eG7 : (Expr.var "gq").evalB (W + 1) τ7 = some q₀ := by
    rw [← hv6 "gq" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgq]
    simp [Expr.evalB, g7 "gq" (by decide)]
  have eN7 : (Expr.var "Ni").evalB (W + 1) τ7 = some i' := ev_var (by rw [g7 "Ni" (by decide), hNi6]) (by
    have := hl7.vars "Ni"; rw [g7 "Ni" (by decide), hNi6] at this; exact this)
  have eL0 : (eLL (.lit 0)).evalB (W + 1) τ7 = some (lvR G P Q s k₀ q₀ 0).length := by
    rw [← llW_get G P Q s k₀ q₀ (show 0 ≤ q₀ by omega)]
    exact ev_LL3 hw7 (by omega) hL'3 (evalB_lit (by omega)) _ hl7 ar7 (by omega)
  have hX7 : τ7.vars "nx" = (xIn G k₀ q₀ P Q s).length := by
    rw [g7 "nx" (by decide), fr6 "nx" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hnx0]
  have hLLm : (lvR G P Q s k₀ q₀ d').length ≤ maxEntry ws.flatten := by
    refine le_maxEntry (List.mem_flatten.2 ⟨llW G P Q s k₀ q₀ q₀, ?_, ?_⟩)
    · rw [← LL_up G P Q s k₀ q₀ d i m]; simp [ws, w0, SW.ws]
    · simp only [llW, List.mem_map, List.mem_range]; exact ⟨d', by omega, rfl⟩
  obtain ⟨τ8, K8, r8, hK8, n8t, n8w, f8, a8, o8, i8⟩ := winC_run (W := W) (X := (xIn G k₀ q₀ P Q s).length)
    (ev_condEq eG7 (evalB_lit (n := 0) (by omega)))
    (ev_condEq (ev_add eN7 (evalB_lit (n := 1) (by omega)) (by omega)) eL0)
    hX7 (by omega)
  have hl8 : EnvLt (W + 1) τ8 := Run.envLt r8 hl7
  have fr8 : ∀ y, y ∉ apV → y ≠ "m0" → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → y ∉ ouV → y ∉ ["Nd", "Ni", "ow", "e0"] →
      y ∉ hdB.map Prod.fst → τ8.vars y = τ0.vars y := fun y h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [f8 y (fun h => h8 (by simp [hdB, h])) (fun h => h8 (by simp [hdB, h])), g7 y h8,
      fr6 y h1 h2 h3 h4 h5 h6 h7]
  have L8 : Lib L' τ8 := L5.of (by rw [f8 "m" (by decide) (by decide), g7 "m" (by decide), f6 "m" (by decide)])
    (by rw [f8 "lt" (by decide) (by decide), g7 "lt" (by decide), f6 "lt" (by decide)])
    (by rw [a8, a7, a6]) (by rw [a8, a7, a6]) (by rw [a8, a7, a6])
  -- step 9: the atom words of the next item
  have hitem' : L'[4 + w0.SG.length + offL G P Q s k₀ q₀ d' + i']? = some (itemW (itm G P Q s k₀ q₀ d' i')) := by
    have h : ws[4 + w0.SG.length + offL G P Q s k₀ q₀ d' + i']? = some (itemW (lvR G P Q s k₀ q₀ d')[i']) :=
      ws_up_item G P Q s k₀ q₀ (e := d) (i' := i) (m := m) hD hI
    have hlt := (List.getElem?_eq_some_iff.1 h).1
    rw [List.getElem?_append_left (by simp [L]; omega), List.getElem?_append_left hlt, h,
      itm_eq G P Q s k₀ q₀ hI]
  have hiw' := (List.getElem?_eq_some_iff.1 hitem').1
  have hLiw' := (List.getElem?_eq_some_iff.1 hitem').2
  have hL'0 : (L'[0]'(by omega)) = ctW G P Q := by
    rw [show L'[0]'(by omega) = L[0]'(by omega) from List.getElem_append_left (by omega)]
    simp only [L, ws, SW.ws]; simp [w0, CT_up]
  obtain ⟨ℓ', t', hx'⟩ := lvR_shape G P Q s k₀ q₀ hk hD hI
  have hσ' : σ' = ⟨k₀ + d', q₀ - d', ℓ', t'⟩ := by simp only [σ']; rw [itm_eq G P Q s k₀ q₀ hI, hx']
  have hRk1 : rhoPlus σ'.k σ'.q ≤ rhoPlus (k₀ + 1) q₀ :=
    (congrArg (fun σ : TypeTree => rhoPlus σ.k σ.q) hσ').trans_le (by
      show rhoPlus (k₀ + d') (q₀ - d') ≤ rhoPlus (k₀ + 1) q₀
      unfold rhoPlus
      exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega)))
  have hRk : rhoPlus σ'.k σ'.q + 1 ≤ R := by omega
  have hg : ∀ y v, y ∈ ["W", "rR", "z0", "bl", "ovf", "gP", "gQ", "gS"] → τ0.vars y = v → τ8.vars y = v :=
    fun y v hy h => by
      have hk8 : ∀ y ∈ ["W", "rR", "z0", "bl", "ovf", "gP", "gQ", "gS"], y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧
          y ≠ "fk" ∧ y ≠ "ow" ∧ y ∉ ouV ∧ y ∉ ["Nd", "Ni", "ow", "e0"] ∧ y ∉ hdB.map Prod.fst := by decide
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hk8 y hy
      rw [fr8 y e1 e2 e3 e4 e5 e6 e7 e8, h]
  have how8 : τ8.vars "ow" = 4 + w0.SG.length + offL G P Q s k₀ q₀ d' + i' := by
    rw [f8 "ow" (by decide) (by decide), g7 "ow" (by decide), how6]
  have hy8 : SegAt "y" 0 b τ8 := fun j hj => by
    rw [a8, a7, a6, a5 "y" (by decide)]; simp only [τ4, arrs_setVar]; rw [a3, a2 "y" (by decide)]
    exact P0.hy j hj
  have hAtS := @Exists.choose_spec _ _ (@Exists.choose_spec _ _ (atT_run hAt hAV))
  beta_reduce at hAtS
  obtain ⟨τ9, K9, r9, hK9, hL9, f9, ya9, ar9, hl9, o9, i9, cp9⟩ := hAtS
    (W := W) (R := R) (iw := 4 + w0.SG.length + offL G P Q s k₀ q₀ d' + i') (p := (itm G P Q s k₀ q₀ d' i').1.1)
    (g := (itm G P Q s k₀ q₀ d' i').1.2) (P := P) (Q := Q) (sg := if s then 1 else 0) (σ := σ') (L := L')
    (b := b) (τ := τ8) (hg "W" _ (by simp) P0.hW) (by omega) (fun b' => by rw [a8]; exact ar7 b') hl8 L8
    (hg "rR" _ (by simp) P0.hrR) (hg "z0" _ (by simp) hz0) (hg "bl" _ (by simp) P0.hbl)
    hy8
    (hg "ovf" _ (by simp) hov) how8 hiw' (by omega) hLiw' (by rw [hL'0]; exact isCT_ctW G P Q)
    (hg "gP" _ (by simp) hgP) (hg "gQ" _ (by simp) hgQ) (hg "gS" _ (by simp) hgS) (by split_ifs <;> omega) hRk
  have hAQ : atQW (L'[0]'(by omega)) P Q (if s then 1 else 0) σ' = AQ := by
    rw [hL'0, atQW_eq G P Q s k₀ q₀]; rfl
  rw [hAQ] at hK9 hL9 cp9
  -- step 10: the plan
  have hk9 : ∀ y ∈ ["m0", "nSG", "nLV", "e0", "Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV",
      "qk", "nx", "mw", "W", "rR", "bl", "z0", "gX"], y ∉ atTV ∧ y ∈ atKeep := by decide
  have fr9 : ∀ y ∈ ["m0", "nSG", "nLV", "e0", "Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV",
      "qk", "nx", "mw", "W", "rR", "bl", "z0", "gX"], τ9.vars y = τ8.vars y := fun y hy =>
    f9 y (hk9 y hy).1 (hAV y (hk9 y hy).2)
  have hm09 : τ9.vars "m0" = ws.length := by
    rw [fr9 "m0" (by simp), f8 "m0" (by decide) (by decide), g7 "m0" (by decide), f6 "m0" (by decide), hm05]
  have he09 : τ9.vars "e0" = pUp G P Q s k₀ q₀ d i := by
    rw [fr9 "e0" (by simp), f8 "e0" (by decide) (by decide), g7 "e0" (by decide), he06]
  have hv9 : ∀ y v, y ∈ ["nSG", "nLV"] → τ0.vars y = v → (Expr.var y).evalB (W + 1) τ9 = some v := by
    have hk9' : ∀ y ∈ ["nSG", "nLV"], y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧
        y ≠ "fk" ∧ y ≠ "ow" ∧ y ∉ ouV ∧ y ∉ ["Nd", "Ni", "ow", "e0"] ∧ y ∉ hdB.map Prod.fst := by decide
    intro y v hy h
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hk9' y hy
    have hk9'' : ∀ y ∈ ["nSG", "nLV"], y ∈ ["m0", "nSG", "nLV", "e0", "Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG",
        "NFA", "NCO", "NLV", "qk", "nx", "mw", "W", "rR", "bl", "z0", "gX"] := by decide
    have e9 := hk9'' y hy
    have hv : τ9.vars y = v := by rw [fr9 y e9, fr8 y e1 e2 e3 e4 e5 e6 e7 e8, h]
    exact ev_var hv (by rw [← hv]; exact hl9.vars _)
  have eM9 : (Expr.var "m0").evalB (W + 1) τ9 = some ws.length := ev_var hm09 (by omega)
  have eOU9 : Glue.eOU.evalB (W + 1) τ9 = some w0.OU.length := by
    unfold Glue.eOU
    have := ev_sub (ev_sub (ev_sub eM9 (evalB_lit (n := 4) (by omega)) (by omega)) (hv9 "nSG" _ (by simp) hSG)
      (by omega)) (hv9 "nLV" _ (by simp) hLV) (by omega)
    rw [show ws.length - 4 - w0.SG.length - w0.LV.length = w0.OU.length by omega] at this
    exact this
  have hpU : pUp G P Q s k₀ q₀ d i ≤ w0.OU.length := by
    unfold pUp; split_ifs
    · omega
    · rw [hOUl]; omega
  have eE9 : (Expr.var "e0").evalB (W + 1) τ9 = some (pUp G P Q s k₀ q₀ d i) := ev_var he09 (by omega)
  obtain ⟨τ10, r10, PR10, np10, f10, a10, l10, o10, i10⟩ := stPlan_run (W := W) (l := plUp)
    (ps := psUp w0 ws.length (ws.length + 1) (pUp G P Q s k₀ q₀ d i)) (τ := τ9) rfl (ar9 "PR")
    (by simp [plUp]; omega)
    (by
      intro j hj
      simp only [plUp, List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨eM9, evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), ev_sub (ev_sub eM9 (evalB_lit (by omega)) (by omega)) eOU9 (by omega)⟩
      · exact ⟨ev_add (ev_sub eM9 eOU9 (by omega)) eE9 (by omega), ev_sub eOU9 eE9 (by omega)⟩
      · exact ⟨ev_add eM9 (evalB_lit (by omega)) (by omega), evalB_lit (by omega)⟩)
    (by decide)
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
    (Run.seq r8 (Run.seq r9 r10))))))))
  have hl10 : EnvLt (W + 1) τ10 := Run.envLt hrun hl0
  have ar10 : ArrW W τ10 := fun b' => by
    by_cases hb : b' = "PR"
    · subst hb; exact l10
    · rw [a10 b' hb]; exact ar9 b'
  have hov10 : τ10.vars "ovf" = τ9.vars "ovf" := f10 "ovf" (by decide)
  have g10 : ∀ y ∈ ["m0", "nSG", "nLV", "e0", "Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV",
      "qk", "nx", "mw", "W", "rR", "bl", "z0", "gX"], τ10.vars y = τ8.vars y := fun y hy => by
    rw [f10 y (by intro h; subst h; simp at hy), fr9 y hy]
  have hscR : ∀ y ∈ scR, y ∉ apV ∧ y ≠ "m0" ∧ y ≠ "oL" ∧ y ≠ "fk" ∧ y ≠ "ow" ∧ y ∉ ouV ∧
      y ∉ ["Nd", "Ni", "ow", "e0"] ∧ y ∉ hdB.map Prod.fst ∧ y ∉ atTV ∧ y ∈ atKeep ∧ y ≠ "np" := by decide
  have g : ∀ j (h : j < 9), τ10.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.up d i m)).getD j 0 := fun j h => by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hscR _ (List.getElem_mem _)
    rw [f10 _ e11, f9 _ e9 (hAV _ e10), fr8 _ e1 e2 e3 e4 e5 e6 e7 e8]; exact hsc j (by omega)
  have hk10 : ∀ y ∈ ["Nph", "Nm", "NSG", "NFA", "NCO", "NLV", "qk"], y ∈ ["m0", "nSG", "nLV", "e0", "Nt", "Nw",
      "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV", "qk", "nx", "mw", "W", "rR", "bl", "z0", "gX"] ∧
      y ≠ "Nt" ∧ y ≠ "Nw" ∧ y ∈ hdB.map Prod.fst := by decide
  have hH : ∀ y, y ∈ ["Nph", "Nm", "NSG", "NFA", "NCO", "NLV", "qk"] → τ10.vars y = fH y := fun y hy => by
    obtain ⟨e1, e2, e3, e4⟩ := hk10 y hy
    rw [g10 y e1, f8 y e2 e3, s7 y e4]
  have hNd10 : τ10.vars "Nd" = d' := by
    rw [g10 "Nd" (by simp), f8 "Nd" (by decide) (by decide), g7 "Nd" (by decide), hNd6]
  have hNi10 : τ10.vars "Ni" = i' := by
    rw [g10 "Ni" (by simp), f8 "Ni" (by decide) (by decide), g7 "Ni" (by decide), hNi6]
  have hnx10 : τ10.vars "nx" = τ0.vars "nx" := by
    rw [g10 "nx" (by simp), fr8 "nx" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have hmw10 : τ10.vars "mw" = τ0.vars "mw" := by
    rw [g10 "mw" (by simp), fr8 "mw" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have hnx8 : τ8.vars "nx" = τ0.vars "nx" := fr8 "nx" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hmw8 : τ8.vars "mw" = τ0.vars "mw" := fr8 "mw" (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨τ10, _, hrun, ?_, fun h0 => ?_, fun hB => ?_⟩
  · -- the cost
    have hA1 : asgK hdB ≤ 40 := by decide
    have hP : plUp.length * ((plUp.map fun p => p.1.size + p.2.size).sum + 6) + 4 ≤ 400 := by decide
    have hC : (Cond.eq (.var "gq") (.lit 0)).size + (Cond.eq (.add (.var "Ni") (.lit 1)) (eLL (.lit 0))).size ≤ 30 := by
      decide
    have hE4 : Expr.size (.add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii")) ≤ 10 := by decide
    have hL2t : (L[2]'(by omega)).length ≤ total ws := by
      rw [hL2]
      have h4 : 4 ≤ ws.length := length_SW_ws w0
      have h1 := len_le_total (L := ws) (i := 2) (by omega)
      have h2' : ∀ w : SW, (h : 2 < w.ws.length) → w.ws[2] = w.AT := fun w h => by simp [SW.ws]
      rw [h2' w0 (lt_of_lt_of_le (by norm_num : 2 < 4) h4)] at h1; exact h1
    rw [hLiw', hL'0] at hK9
    have hct : (ctW G P Q).length = (L'[0]'(by omega)).length := by rw [hL'0]
    simp only [L'] at hK9
    have eL : L ++ [O] = ws ++ [[], O] := by simp [L]
    rw [eL] at hK9
    have hKA : (atT_run hAt hAV).choose * ((ctW G P Q).length + 1) *
        ((itemW (itm G P Q s k₀ q₀ d' i')).length + σ'.ℓ + rhoPlus σ'.k σ'.q + 1) ^
          (atT_run hAt hAV).choose_spec.choose ≤
        cAt hAt hAV * ((ctW G P Q).length + 1) *
          ((itemW (itm G P Q s k₀ q₀ d' i')).length + σ'.ℓ + rhoPlus (k₀ + 1) q₀ + 1) ^ aAt hAt hAV :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hKA' := kAtT_mono (L := ws ++ [[], O]) (b := b) (w := AQ) hKA
    unfold kUpB
    omega
  · rw [hov10] at h0
    obtain ⟨L9, hoe9, hpo9⟩ := hL9 h0
    refine ⟨⟨?_, hkq, ar10, hl10, ?_, hR, ?_, ?_, ?_, ?_, ?_, by rw [hov10]; exact h0, ?_, ?_, PR10, np10, ?_,
      by simp [psUp]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g10 "W" (by simp), hg "W" _ (by simp) P0.hW]
    · rw [g10 "rR" (by simp), hg "rR" _ (by simp) P0.hrR]
    · have := L9.of (τ' := τ10) (f10 "m" (by decide)) (f10 "lt" (by decide)) (a10 "a" (by decide))
        (a10 "st" (by decide)) (a10 "ln" (by decide))
      simpa [L', L, List.append_assoc] using this
    · rw [g10 "z0" (by simp), hg "z0" _ (by simp) hz0]
    · rw [g10 "bl" (by simp), hg "bl" _ (by simp) P0.hbl]
    · intro j hj
      rw [a10 "y" (by decide), ya9, a8, a7, a6, a5 "y" (by decide)]; simp only [τ4, arrs_setVar]
      rw [a3, a2 "y" (by decide)]; exact P0.hy j hj
    · simpa [scR, scW, curW] using g 1 (by omega)
    · refine ⟨fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h,
        fun h => by simp [kindOf] at h, fun _ => ?_, by simp [kindOf]⟩
      refine ⟨L'.length, by simp [L', L], by rw [f10 "oe" (by decide), hoe9], ?_⟩
      simp [L', L]
    · rw [hH "qk" (by simp)]; simp [fH, kindOf]
    · intro p hp
      simp [psUp] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [L', L] <;> omega
    · rw [g10 "Nt" (by simp), n8t, tagOf, winOf_upB G P Q s k₀ q₀ hD hI, s7 "Nt" (by simp [hdB])]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> simp [fH]
    · rw [g10 "Nw" (by simp), n8w, winOf_upB G P Q s k₀ q₀ hD hI, s7 "Nw" (by simp [hdB])]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> simp [fH]
    · rw [hsV_of (by simp [scW]) g (hH "Nph" (by simp)) hNd10 hNi10 (hH "Nm" (by simp)) (hH "NSG" (by simp))
        (hH "NFA" (by simp)) (hH "NCO" (by simp)) (hH "NLV" (by simp)),
        scW_eq G P Q s k₀ q₀ (.up d i m) (.up d' i' 0)]
      simp [fH, curW, w0, SG_up, LV_up, FA_up, CO_up]
    · rw [f10 "po" (by decide), hpo9]
    · rw [hnx10]
    · rw [hmw10]
    · rw [o10, o9, o8, o7, o6, o5]; simp only [τ4, out_setVar]; rw [o3, o2]; simp [τ1, P0.hout]
  · rw [hov10]
    have eLb : ws ++ [[], O, AQ] = L' ++ [AQ] := by simp [L', L]
    have hB' : BigRoom W R (L' ++ [AQ]) b (τ8.vars "nx") (τ8.vars "mw") := by
      rw [hnx8, hmw8, ← eLb]; exact hB
    exact cp9 (L' ++ [AQ]) (List.Sublist.refl _) hB'

end Lax185574Proofs.ResolveRam.Glue
