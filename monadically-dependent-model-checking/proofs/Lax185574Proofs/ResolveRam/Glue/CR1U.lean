import Lax185574Proofs.ResolveRam.Glue.CR1D

/-!
The case of round `1` when the way down has no level (`q₀ = 0`).

After `r1A 0` (the length `n`, the color table, the item words of level
`0` and the words of the scatter type) the next position is `up 0 0 0`,
the canonical form of the atom words of the first item of level `0`.
The case appends the word of the atom words (`atT1`, with the color
table at index `5`), and the window of the new head is the whole input
if level `0` has a single item, since then the next call is the last
one (`bR1up_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The test of a single item. -/
def c1R1 : Cond := .eq (.var "gn") (.lit 1)

/-- The case of round `1` when the way down has no level. -/
noncomputable def bR1up (atC : Com) : Com :=
  .seq (r1A 0) (gate (.seq (.assign "ow" (.lit 6)) (.seq (atT1 5 atC)
    (gate (.seq (.seq (asgs (hdR1 2 3)) (stPlan plR1)) (winC c1R1 c1R1))))))

/-- The constant of the query of the atom words in round `1`. -/
noncomputable def cR1 {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ℕ := (atT1_run hAt hAV).choose

/-- The exponent of the query of the atom words in round `1`. -/
noncomputable def aR1 {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ℕ := (atT1_run hAt hAV).choose_spec.choose

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The word of the atom words of the first item of level `0`. -/
noncomputable def aqR1 : List ℕ := toWord (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ 0 0).2)

/-- The cost of the case of round `1` when the way down has no level. -/
noncomputable def kR1up {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  kR1A G P Q s k₀ q₀ 0 + kAtT (libR1 G P Q s k₀ q₀ 0) (rY G k₀ q₀ .stp) (aqR1 G P Q s k₀ q₀)
    (cR1 hAt hAV * ((ctW G P Q).length + 1) *
      ((itemW (itm G P Q s k₀ q₀ 0 0)).length + (itm G P Q s k₀ q₀ 0 0).2.ℓ +
        rhoPlus (itm G P Q s k₀ q₀ 0 0).2.k (itm G P Q s k₀ q₀ 0 0).2.q + 1) ^ aR1 hAt hAV) + 300

theorem winOf_up00 (hq : q₀ = 0) (hn : 1 ≤ n) :
    winOf G P Q s k₀ q₀ (.up 0 0 0) = if n = 1 then (xIn G k₀ q₀ P Q s).length else 0 := by
  subst hq
  have hl := lvR_zero_length G P Q s k₀ 0
  by_cases h1 : n = 1
  · simp [winOf, next, nUp, hl, h1]
  · simp [winOf, next, nUp, hl, h1, show 1 < n by omega]

/-- **The state of round `1` as a plan, no way down.** -/
theorem planW_r1up (hq : q₀ = 0) :
    planW (libR1 G P Q s k₀ q₀ 0 ++ [aqR1 G P Q s k₀ q₀])
        (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
      (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)).ws := by
  rw [next_stp_up G P Q s k₀ q₀ hq, sw_stp_up hq, planW_r1]
  simp [SW.ws]

theorem itm00_eta : itm G P Q s k₀ q₀ 0 0 =
    (((itm G P Q s k₀ q₀ 0 0).1.1, (itm G P Q s k₀ q₀ 0 0).1.2), (itm G P Q s k₀ q₀ 0 0).2) := rfl

theorem r1_keep : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw", "gn", "NSG", "gP", "gQ", "gS", "ovf"],
    y ∉ r1AV ∨ y = "NSG" ∨ y = "ovf" := by decide

set_option maxHeartbeats 3200000 in
/-- **The case of round `1` when the way down has no level.** -/
theorem bR1up_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    {W : ℕ} (hk : 1 ≤ k₀) (hn : 1 ≤ n) (hq : q₀ = 0) :
    BodyCall (bR1up atC) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) (libR1 G P Q s k₀ q₀ 0 ++ [aqR1 G P Q s k₀ q₀])
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (kR1up G P Q s k₀ q₀ hAt hAV) := by
  intro τ0 P0 hov hkq
  rw [next_stp_up G P Q s k₀ q₀ hq]
  have hc0 : callOf G P Q s k₀ q₀ .stp = .stp := rfl
  rw [hc0] at P0 ⊢
  have hi0 : 0 < (lvR G P Q s k₀ q₀ 0).length := by rw [lvR_zero_length]; omega
  rw [callOf_up0 G P Q s k₀ q₀ hi0]
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  set SG := (Lax185574.ScatterTypes.stp G k₀ q₀).words with hSG
  set L := libR1 G P Q s k₀ q₀ 0 with hLdef
  set σ := (itm G P Q s k₀ q₀ 0 0).2 with hσ
  set AQ := aqR1 G P Q s k₀ q₀ with hAQ
  have hLl : L.length = 6 + n + SG.length := length_libR1 G P Q s k₀ q₀ 0
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ .stp).getD j 0 := P0.hsc
  have hgn : τ0.vars "gn" = n := by simpa [scR, scW_stp] using hsc 3 (by omega)
  have hnx : τ0.vars "nx" = (xIn G k₀ q₀ P Q s).length := by simpa [scR, scW_stp] using hsc 2 (by omega)
  have hgP : τ0.vars "gP" = P := by simpa [scR, scW_stp] using hsc 4 (by omega)
  have hgQ : τ0.vars "gQ" = Q := by simpa [scR, scW_stp] using hsc 5 (by omega)
  have hgS : τ0.vars "gS" = (if s then 1 else 0) := by simpa [scR, scW_stp] using hsc 6 (by omega)
  have hz0 : τ0.vars "z0" = 0 := by simpa [scR, scW_stp] using hsc 0 (by omega)
  have hroom0 : RoomOK W R τ0 (swAt G P Q s k₀ q₀ .stp).ws (rY G k₀ q₀ .stp) := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS0 := room_bound hroom0 hR
  obtain ⟨hS01, -, -, -⟩ := sOfV_ge (τ := τ0) (ws := (swAt G P Q s k₀ q₀ .stp).ws) (b := rY G k₀ q₀ .stp)
  rw [hnx] at hS01
  obtain ⟨τ1, K1, r1, hK1, hL1, fr1, ya1, ar1, hl1, o1, i1, big1⟩ :=
    r1A_run G P Q s k₀ q₀ (z := 0) (by omega) hR hkq P0 hov
  have hsubL : ∀ Lb, (L ++ [AQ]).Sublist Lb → L.Sublist Lb := fun Lb h =>
    (List.sublist_append_left L [AQ]).trans h
  by_cases h1 : τ1.vars "ovf" = 0
  swap
  · refine ⟨τ1, _, Run.seq r1 (gate_skip h1 (hl1.vars _)), ?_, fun h => absurd h h1,
      fun hB => absurd (big1 _ (List.sublist_append_left L [AQ]) hB) h1⟩
    unfold kR1up; omega
  obtain ⟨L1, nsg1⟩ := hL1 h1
  have hm1 : L.length < W + 1 := by rw [← L1.m]; exact hl1.vars _
  -- the index of the item word
  set τ2 := τ1.setVar "ow" 6
  have r2 : Run (W + 1) (.assign "ow" (.lit 6)) τ1 τ2 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have v2 : ∀ y, y ≠ "ow" → τ2.vars y = τ1.vars y := fun y hy => by simp [τ2, hy]
  have g2 : ∀ y, y ∉ r1AV → y ≠ "ow" → τ2.vars y = τ0.vars y := fun y a b => by rw [v2 y b, fr1 y a]
  -- the atom words
  obtain ⟨h6, hL6⟩ := libR1_get6 G P Q s k₀ q₀ 0 hn []
  obtain ⟨h5, hL5⟩ := libR1_get5 G P Q s k₀ q₀ 0 []
  simp only [List.append_nil] at h6 hL6 h5 hL5
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk (d := 0) (by omega) hi0
  have hσ' : σ = ⟨k₀ + 0, q₀ - 0, ℓ, t⟩ := by rw [hσ, itm_eq G P Q s k₀ q₀ hi0, hx]
  have hRk : rhoPlus σ.k σ.q + 1 ≤ R := by
    have : rhoPlus (k₀ + 0) (q₀ - 0) ≤ rhoPlus (k₀ + 1) q₀ := by
      unfold rhoPlus
      exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
    rw [hσ']; simp only at this ⊢; omega
  obtain ⟨τ3, K3, r3, hK3, hL3, fr3, ya3, ar3, hl3, o3, i3, cp3⟩ :=
    @Exists.choose_spec _ _ (atT1_run hAt hAV).choose_spec W R 6 5
      (itm G P Q s k₀ q₀ 0 0).1.1 (itm G P Q s k₀ q₀ 0 0).1.2 P Q
      (if s then 1 else 0) σ L (rY G k₀ q₀ .stp) τ2
      (by rw [g2 "W" (by decide) (by decide), P0.hW]) (by omega) ar1 hl2
      (L1.of (v2 "m" (by decide)) (v2 "lt" (by decide)) rfl rfl rfl)
      (by rw [g2 "rR" (by decide) (by decide), P0.hrR]) (by rw [g2 "z0" (by decide) (by decide), hz0])
      (by rw [g2 "bl" (by decide) (by decide), P0.hbl]) (fun j hj => by simp only [τ2, arrs_setVar]; rw [ya1]; exact P0.hy j hj)
      (by rw [v2 "ovf" (by decide), h1]) (by simp [τ2]) h6 h5 (by rw [hL6]) (by rw [hL5]; exact isCT_ctW G P Q)
      (by rw [g2 "gP" (by decide) (by decide), hgP]) (by rw [g2 "gQ" (by decide) (by decide), hgQ])
      (by rw [g2 "gS" (by decide) (by decide), hgS]) (by split_ifs <;> omega) hRk
  have hAQ5 : atQW L[5] P Q (if s then 1 else 0) σ = AQ := by
    rw [hL5, atQW_eq]; rfl
  rw [hAQ5] at hK3 hL3 cp3
  rw [hL5, hL6] at hK3
  have hnx2 : τ2.vars "nx" = τ0.vars "nx" := g2 "nx" (by decide) (by decide)
  have hmw2 : τ2.vars "mw" = τ0.vars "mw" := g2 "mw" (by decide) (by decide)
  have hrunA : ∀ {τ' : Env} {K' : ℕ}, Run (W + 1) (gate (.seq (.seq (asgs (hdR1 2 3)) (stPlan plR1))
      (winC c1R1 c1R1))) τ3 τ' K' → Run (W + 1) (bR1up atC) τ0 τ' (K1 + (2 + (K3 + K') + 4)) :=
    fun h => Run.seq r1 (gate_run h1 (by omega) (Run.seq r2 (Run.seq r3 h)))
  by_cases h3 : τ3.vars "ovf" = 0
  swap
  · refine ⟨τ3, _, hrunA (gate_skip h3 (hl3.vars _)), ?_, fun h => absurd h h3,
      fun hB => absurd (cp3 _ (List.Sublist.refl _) (by rw [hnx2, hmw2]; exact hB)) h3⟩
    unfold kR1up cR1 aR1
    rw [← hLdef, ← hAQ, ← hσ]
    omega
  obtain ⟨L3, oe3, -⟩ := hL3 h3
  have fr3' : ∀ y, y ∉ r1AV → y ≠ "ow" → y ∉ atTV → y ∉ atV → τ3.vars y = τ0.vars y := fun y a b c d => by
    rw [fr3 y c d, g2 y a b]
  have hgn3 : τ3.vars "gn" = n := by rw [fr3' "gn" (by decide) (by decide) (by decide) (hAV _ (by decide)), hgn]
  have hnsg3 : τ3.vars "NSG" = SG.length := by
    rw [fr3 "NSG" (by decide) (hAV _ (by decide)), v2 "NSG" (by decide), nsg1]
  obtain ⟨τ4, r4, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, nox, n11, n12, PR4, np4, v4, a4, ar4, hl4,
    o4, i4⟩ := hdR1_run (ph := 2) (k := 3) (nn := n) (nS := SG.length) ar3 hl3 (by omega) (by omega)
      (by omega) hgn3 hnsg3 (by omega)
  have fr4 : ∀ y, y ∉ r1AV → y ≠ "ow" → y ∉ atTV → y ∉ atV → y ≠ "np" → y ∉ hdR1N →
      τ4.vars y = τ0.vars y := fun y a b c d e f => by rw [v4 y e f, fr3' y a b c d]
  have hgn4 : τ4.vars "gn" = n := by rw [v4 "gn" (by decide) (by decide), hgn3]
  have hnx4 : τ4.vars "nx" = (xIn G k₀ q₀ P Q s).length := by
    rw [fr4 "nx" (by decide) (by decide) (by decide) (hAV _ (by decide)) (by decide) (by decide), hnx]
  have hc1 : c1R1.evalB (W + 1) τ4 = some (n == 1) :=
    evalB_condEq (ev_var hgn4 (by omega)) (evalB_lit (by omega))
  obtain ⟨τ5, K5, r5, hK5, t5, w5, v5, a5, o5, i5⟩ := winC_run (X := (xIn G k₀ q₀ P Q s).length) hc1 hc1 hnx4
    (by omega)
  have fr5 : ∀ y, y ∉ r1AV → y ≠ "ow" → y ∉ atTV → y ∉ atV → y ≠ "np" → y ∉ hdR1N →
      τ5.vars y = τ0.vars y := fun y a b c d e f => by
    rw [v5 y (fun h => f (by simp [h, hdR1N])) (fun h => f (by simp [h, hdR1N])), fr4 y a b c d e f]
  have kp : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"], τ5.vars y = τ0.vars y := by
    intro y hy
    have hk' : y ∈ atKeep := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact fr5 y (by revert hy; revert y; decide) (by revert hy; revert y; decide)
      (by revert hy; revert y; decide) (hAV y hk') (by revert hy; revert y; decide)
      (by revert hy; revert y; decide)
  have v54 : ∀ y, y ≠ "Nt" → y ≠ "Nw" → τ5.vars y = τ4.vars y := v5
  have hov5 : τ5.vars "ovf" = 0 := by
    rw [v54 "ovf" (by decide) (by decide), v4 "ovf" (by decide) (by decide), h3]
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  have ar5 : ArrW W τ5 := fun b' => by rw [a5]; exact ar4 b'
  have hy5 : τ5.arrs "y" = τ0.arrs "y" := by
    rw [a5, a4 "y" (by decide), ya3]; simp only [τ2, arrs_setVar]; rw [ya1]
  have hrun := hrunA (gate_run h3 (by omega) (Run.seq r4 r5))
  have g : ∀ j (h : j < 9), τ5.vars (scR[j]'(by simp [scR]; omega)) = (scW G P Q s k₀ q₀ .stp).getD j 0 :=
    fun j h => by
      have hm : scR[j]'(by simp [scR]; omega) ∈ scR := List.getElem_mem _
      rw [fr5 _ ((scR_r1 _ hm).1) (by revert hm; generalize scR[j]'(by simp [scR]; omega) = y; revert y; decide)
        (by revert hm; generalize scR[j]'(by simp [scR]; omega) = y; revert y; decide)
        (hAV _ (scR_atKeep _ hm)) ((scR_r1 _ hm).2.1) ((scR_r1 _ hm).2.2)]
      exact hsc j (by omega)
  have hLA : (L ++ [AQ]).length = 7 + n + SG.length := by simp [hLl]; omega
  refine ⟨τ5, _, hrun, ?_, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => hov5⟩
  · have := Nat.zero_le 0
    unfold kR1up cR1 aR1
    rw [← hLdef, ← hAQ, ← hσ]
    simp only [c1R1, Cond.size, Expr.size] at hK5
    omega
  · refine tailIn_of P0 (by simp [scW_stp]) (by simp [scW_stp]) hkq hR hl5 ar5 (fun y hy => kp y (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)) hy5
      (L3.of (by rw [v54 "m" (by decide) (by decide), v4 "m" (by decide) (by decide)])
        (by rw [v54 "lt" (by decide) (by decide), v4 "lt" (by decide) (by decide)])
        (by rw [a5, a4 "a" (by decide)]) (by rw [a5, a4 "st" (by decide)]) (by rw [a5, a4 "ln" (by decide)]))
      hov5 ?_ (by rw [v54 "qk" (by decide) (by decide), n11]; rfl)
      (fun j hj => by rw [a5]; exact PR4 j hj) (by rw [v54 "np" (by decide) (by decide), np4]; rfl)
      (fun p hp => ?_) (by simp [psR1])
    · refine ⟨fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h,
        fun _ => ⟨L.length, by simp, ?_, ?_⟩, by simp [kindOf]⟩
      · rw [v54 "oe" (by decide) (by decide), v4 "oe" (by decide) (by decide), oe3]
      · rw [realQ_canon]; simp [hAQ, aqR1, hσ]
    · simp only [psR1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rw [hLA]
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · rw [t5, n1, tagOf, winOf_up00 G P Q s k₀ q₀ hq hn]
    by_cases h : n = 1 <;> simp [h]
  · rw [w5, n2, winOf_up00 G P Q s k₀ q₀ hq hn]
    by_cases h : n = 1 <;> simp [h]
  · rw [hsV_of (by simp [scW_stp]) g (by rw [v54 "Nph" (by decide) (by decide), n3])
      (by rw [v54 "Nd" (by decide) (by decide), n4]) (by rw [v54 "Ni" (by decide) (by decide), n5])
      (by rw [v54 "Nm" (by decide) (by decide), n6]) (by rw [v54 "NSG" (by decide) (by decide), n7])
      (by rw [v54 "NFA" (by decide) (by decide), n8]) (by rw [v54 "NCO" (by decide) (by decide), n9])
      (by rw [v54 "NLV" (by decide) (by decide), n10]), scW_eq G P Q s k₀ q₀ .stp (.up 0 0 0), sw_stp_up hq]
    simp [curW, length_lvW_zero]
    rfl
  · rw [v54 "po" (by decide) (by decide), n12]
  · exact kp "nx" (by simp)
  · exact kp "mw" (by simp)
  · rw [o5, o4, o3]; simp only [τ2, out_setVar]; rw [o1, P0.hout]

end Lax185574Proofs.ResolveRam.Glue
