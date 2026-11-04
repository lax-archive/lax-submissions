import Lax185574Proofs.ResolveRam.Glue.CR1P

/-!
The case of round `1` when the way down has a level (`q₀ ≠ 0`).

After `r1A 1` (the lengths `n, 0`, the color table, the item words of
level `0` and the words of the scatter type) the next position is
`dn 0 0 0`, the rank shift of the first item of level `0`, whose query
is the tree of the item word `6` of the library (`bR1dn_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoPlus)

/-- The case of round `1` when the way down has a level. -/
noncomputable def bR1dn : Com := .seq (r1A 1) (gate (.seq (asgs (hdR1 1 0)) (stPlan plR1)))

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The cost of the case of round `1` when the way down has a level. -/
noncomputable def kR1dn : ℕ := kR1A G P Q s k₀ q₀ 1 + 210

theorem next_stp_dn (hq : q₀ ≠ 0) : next G P Q s k₀ q₀ .stp = .dn 0 0 0 := by simp [next, hq]

theorem next_stp_up (hq : q₀ = 0) : next G P Q s k₀ q₀ .stp = .up 0 0 0 := by simp [next, hq]

theorem lvW_zero_get (hn : 1 ≤ n) :
    (lvW G P Q s k₀ q₀ 0)[0]'(by rw [length_lvW_zero]; omega) = itemW (itm G P Q s k₀ q₀ 0 0) := by
  have h := lvW_get G P Q s k₀ q₀ (d := 0) (j := 0) (by rw [lvR_zero_length]; omega)
  rw [List.getElem?_eq_getElem (by rw [length_lvW_zero]; omega)] at h
  exact Option.some.inj h

theorem libR1_get6 (z : ℕ) (hn : 1 ≤ n) (X : List (List ℕ)) :
    ∃ h : 6 < (libR1 G P Q s k₀ q₀ z ++ X).length,
      (libR1 G P Q s k₀ q₀ z ++ X)[6] = itemW (itm G P Q s k₀ q₀ 0 0) := by
  have hl := length_lvW_zero G P Q s k₀ q₀
  have key : (libR1 G P Q s k₀ q₀ z ++ X)[6]? = some (itemW (itm G P Q s k₀ q₀ 0 0)) := by
    rw [show libR1 G P Q s k₀ q₀ z ++ X = [[], [], [], [], n :: List.replicate z 0, ctW G P Q] ++
      (lvW G P Q s k₀ q₀ 0 ++ ((Lax185574.ScatterTypes.stp G k₀ q₀).words ++ X)) by
        simp [libR1, midR1, ws_stp]]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp [hl]; omega)]
    exact lvW_get G P Q s k₀ q₀ (d := 0) (j := 0) (by rw [lvR_zero_length]; omega)
  exact List.getElem?_eq_some_iff.1 key

theorem libR1_get5 (z : ℕ) (X : List (List ℕ)) :
    ∃ h : 5 < (libR1 G P Q s k₀ q₀ z ++ X).length, (libR1 G P Q s k₀ q₀ z ++ X)[5] = ctW G P Q := by
  refine ⟨by simp [libR1, midR1, ws_stp]; try omega, ?_⟩
  simp [libR1, midR1, ws_stp]

theorem length_libR1 (z : ℕ) :
    (libR1 G P Q s k₀ q₀ z).length = 6 + n + (Lax185574.ScatterTypes.stp G k₀ q₀).words.length := by
  simp [libR1, midR1, ws_stp, length_lvW_zero]; omega

/-- **The state of round `1` as a plan, the way down.** -/
theorem planW_r1dn (hq : q₀ ≠ 0) :
    planW (libR1 G P Q s k₀ q₀ 1) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
      (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)).ws := by
  rw [next_stp_dn G P Q s k₀ q₀ hq, sw_stp_dn, ← List.append_nil (libR1 G P Q s k₀ q₀ 1), planW_r1]
  simp [SW.ws]

theorem sub_libR1 (z : ℕ) (X : List (List ℕ)) :
    (swAt G P Q s k₀ q₀ .stp).ws.Sublist (libR1 G P Q s k₀ q₀ z ++ X) := by
  rw [libR1, List.append_assoc, List.append_assoc]; exact List.sublist_append_left _ _

theorem scR_r1 : ∀ y ∈ scR, y ∉ r1AV ∧ y ≠ "np" ∧ y ∉ hdR1N := by decide

set_option maxHeartbeats 3200000 in
/-- **The case of round `1` when the way down has a level.** -/
theorem bR1dn_ok {W : ℕ} (hn : 1 ≤ n) (hq : q₀ ≠ 0) :
    BodyCall bR1dn W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) (libR1 G P Q s k₀ q₀ 1)
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (kR1dn G P Q s k₀ q₀) := by
  intro τ0 P0 hov hkq
  rw [next_stp_dn G P Q s k₀ q₀ hq]
  have hc0 : callOf G P Q s k₀ q₀ .stp = .stp := rfl
  rw [hc0] at P0 ⊢
  have hi0 : 0 < (lvR G P Q s k₀ q₀ 0).length := by rw [lvR_zero_length]; omega
  rw [callOf_dn0 G P Q s k₀ q₀ hi0]
  set R := rhoPlus (k₀ + 1) q₀ + 2
  have hR : 1 ≤ R := by omega
  set SG := (Lax185574.ScatterTypes.stp G k₀ q₀).words with hSG
  set L := libR1 G P Q s k₀ q₀ 1 with hLdef
  have hLl : L.length = 6 + n + SG.length := length_libR1 G P Q s k₀ q₀ 1
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ .stp).getD j 0 := P0.hsc
  have hgn : τ0.vars "gn" = n := by simpa [scR, scW_stp] using hsc 3 (by omega)
  obtain ⟨τ1, K1, r1, hK1, hL1, fr1, ya1, ar1, hl1, o1, i1, big1⟩ :=
    r1A_run G P Q s k₀ q₀ (z := 1) (by omega) hR hkq P0 hov
  by_cases h1 : τ1.vars "ovf" = 0
  swap
  · refine ⟨τ1, _, Run.seq r1 (gate_skip h1 (hl1.vars _)), ?_, fun h => absurd h h1,
      fun hB => absurd (big1 L (List.Sublist.refl _) hB) h1⟩
    unfold kR1dn; omega
  obtain ⟨L1, nsg1⟩ := hL1 h1
  have hgn1 : τ1.vars "gn" = n := by rw [fr1 "gn" (by decide), hgn]
  have hm1 : L.length < W + 1 := by rw [← L1.m]; exact hl1.vars _
  obtain ⟨τ2, r2, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, nox, n11, n12, PR2, np2, v2, a2, ar2, hl2,
    o2, i2⟩ := hdR1_run (ph := 1) (k := 0) (nn := n) (nS := SG.length) ar1 hl1 (by omega) (by omega)
      (by omega) hgn1 nsg1 (by omega)
  have hrun : Run (W + 1) bR1dn τ0 τ2 (K1 + (200 + 4)) := Run.seq r1 (gate_run h1 (by omega) r2)
  have fr : ∀ y, y ∉ r1AV → y ≠ "np" → y ∉ hdR1N → τ2.vars y = τ0.vars y := fun y a b c => by
    rw [v2 y b c, fr1 y a]
  have hov2 : τ2.vars "ovf" = 0 := by rw [v2 "ovf" (by decide) (by decide), h1]
  have g : ∀ j (h : j < 9), τ2.vars (scR[j]'(by simp [scR]; omega)) = (scW G P Q s k₀ q₀ .stp).getD j 0 :=
    fun j h => by
      obtain ⟨a, b, c⟩ := scR_r1 (scR[j]'(by simp [scR]; omega)) (List.getElem_mem _)
      rw [fr _ a b c]; exact hsc j (by omega)
  obtain ⟨h6, hL6⟩ := libR1_get6 G P Q s k₀ q₀ 1 hn []
  simp only [List.append_nil] at h6 hL6
  refine ⟨τ2, _, hrun, by unfold kR1dn; omega, fun _ => ⟨?_, ?_, ?_, ?_, n12, ?_, ?_, ?_⟩,
    fun _ => hov2⟩
  · refine tailIn_of P0 (by simp [scW_stp]) (by simp [scW_stp]) hkq hR hl2 ar2 (fun y hy => ?_)
      (by rw [a2 "y" (by decide), ya1]) (L1.of (v2 "m" (by decide) (by decide)) (v2 "lt" (by decide) (by decide))
        (a2 "a" (by decide)) (a2 "st" (by decide)) (a2 "ln" (by decide))) hov2 ?_ n11 PR2
      (by rw [np2]; rfl) (fun p hp => ?_) (by simp [psR1])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact fr _ (by decide) (by decide) (by decide)
    · refine ⟨fun _ => ⟨6, h6, ?_, nox, ?_⟩, fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h,
        fun h => by simp [kindOf] at h, by simp [kindOf]⟩
      · rw [hL6]; simp [itemW]
      · rw [hL6, realQ_shift, toWord_itm]
    · simp only [psR1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · rw [n1, tagOf_dn]
  · rw [n2, winOf_dn]
  · rw [hsV_of (by simp [scW_stp]) g n3 n4 n5 n6 n7 n8 n9 n10, scW_eq G P Q s k₀ q₀ .stp (.dn 0 0 0),
      sw_stp_dn]
    simp [curW, length_lvW_zero]
    rfl
  · rw [fr "nx" (by decide) (by decide) (by decide)]
  · rw [fr "mw" (by decide) (by decide) (by decide)]
  · rw [o2, o1, P0.hout]

end Lax185574Proofs.ResolveRam.Glue
