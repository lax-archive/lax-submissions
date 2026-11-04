import Lax185574Proofs.ResolveRam.Glue.CFinLL
import Lax185574Proofs.ResolveRam.Glue.CFinH
import Lax185574Proofs.ResolveRam.Glue.CFinAt
import Lax185574Proofs.ResolveRam.Glue.CFinB

/-!
The end of a round that finishes an item on the way down and whose next
call is the canonical form of the atom words of an item, at the start of
the way up.

`brUp ez cw atC eph ed` sets `lvZ` to the number of new empty levels
(`ez`), appends the new lengths of the levels (`llC`), sets the index
`ow` of the item word (`cw`), appends the atom words of the item
(`atT atC`), and writes the new head and the plan (`brUp_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoPlus)

/-- The end of a round whose next call is the canonical form of atom words. -/
def brUp (ez : Expr) (cw atC : Com) (eph ed : Expr) : Com :=
  .seq (.assign "lvZ" ez) (.seq llC (.seq cw (.seq (atT atC) (.seq (asgs (hdFn eph ed (.lit 0) 3)) (stPlan plFn)))))

/-- The scalars that the end of a round keeps through the piece of the atom words. -/
def upKeep : List String :=
  ["m0", "e0", "ne", "dd", "ii", "gq", "nSG", "nFA", "nCO", "nLV", "W", "rR", "bl", "gX", "z0", "nx", "mw",
    "gn", "gP", "gQ", "gS", "gK", "ph", "mm"]

theorem upKeep_atTV : ∀ y ∈ upKeep, y ∉ atTV := by decide
theorem upKeep_atKeep : ∀ y ∈ upKeep, y ∈ atKeep := by decide
theorem upKeep_llCV : ∀ y ∈ upKeep, y ∉ llCV ∧ y ≠ "lvZ" ∧ y ≠ "ow" := by decide

/-- The scalars that `brUp` may write besides those of the piece. -/
def brUpV : List String := ["lvZ", "ow", "np"] ++ llCV ++ atTV ++ hdNames

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
/-- **The end of a round whose next call is the canonical form of atom words.** -/
theorem brUp_run {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ∃ cA aA : ℕ, ∀ {ez eph ed : Expr} {cw : Com} {W R d e z iw p g P Q sg M0 e0 nS nF nC nL a1 a2 Kw : ℕ}
    {σ : TypeTree} {L : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hW24 : 2 ^ 24 < W) (hL : Lib L τ)
    (h3 : 3 < L.length) (hdd : τ.vars "dd" = d) (hd : d + 1 < L[3].length) (htN : τ.vars "lvN" = L[3][d + 1])
    (hne : τ.vars "ne" = e) (hv : L[3][d + 1] + e ≤ W) (hroom : 2 * total L + L.length + d + z + 8 ≤ W)
    (hez : ez.evalB (W + 1) τ = some z)
    (hcw : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → ρ.vars y = τ.vars y) → EnvLt (W + 1) ρ →
      ∃ K', Run (W + 1) cw ρ (ρ.setVar "ow" iw) K' ∧ K' ≤ Kw)
    (hrR : τ.vars "rR" = min R W) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length)
    (hy : SegAt "y" 0 b τ) (hov : τ.vars "ovf" = 0) (hiw : iw < L.length)
    (hitem : L[iw] = itemW ((p, g), σ)) (hct : IsCT L[0]) (hgP : τ.vars "gP" = P)
    (hgQ : τ.vars "gQ" = Q) (hgS : τ.vars "gS" = sg) (hsg : sg ≤ 1) (hRk : rhoPlus σ.k σ.q + 1 ≤ R)
    (hm0 : τ.vars "m0" = M0) (he0 : τ.vars "e0" = e0)
    (hnS : τ.vars "nSG" = nS) (hnF : τ.vars "nFA" = nF) (hnC : τ.vars "nCO" = nC) (hnL : τ.vars "nLV" = nL)
    (h1 : ∀ ρ : Env, (∀ y ∈ upKeep, ρ.vars y = τ.vars y) →
      eph.evalB (W + 1) ρ = some a1 ∧ ed.evalB (W + 1) ρ = some a2)
    (hrd : ∀ y ∈ hdNames, y ∉ exRv eph ∧ y ∉ exRv ed)
    (hsum : nL + e < W + 1) (h4 : 4 + nS + nF + nC < W + 1),
    ∃ τ' K, Run (W + 1) (brUp ez cw atC eph ed) τ τ' K ∧
      K ≤ ez.size + 40 * (d + z) + Kw + kAtT (L ++ [llNew L[3] d e z]) b (atQW L[0] P Q sg σ)
        (cA * (L[0].length + 1) * (L[iw].length + σ.ℓ + rhoPlus σ.k σ.q + 1) ^ aA) +
        asgK (hdFn eph ed (.lit 0) 3) + 500 ∧
      (τ'.vars "ovf" = 0 → Lib (L ++ [llNew L[3] d e z, atQW L[0] P Q sg σ]) τ' ∧
        τ'.vars "oe" = L.length + 1) ∧
      τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧ τ'.vars "Nph" = a1 ∧ τ'.vars "Nd" = a2 ∧ τ'.vars "Ni" = 0 ∧
      τ'.vars "Nm" = 0 ∧ τ'.vars "NSG" = nS ∧ τ'.vars "NFA" = 0 ∧ τ'.vars "NCO" = 0 ∧
      τ'.vars "NLV" = nL + e ∧ τ'.vars "qk" = 3 ∧ τ'.vars "po" = 0 ∧
      PreAt "PR" (prW (psFn M0 L.length e0 e nS nF nC nL)) τ' ∧ τ'.vars "np" = 7 ∧
      (∀ y, y ∉ brUpV → y ∉ atV → τ'.vars y = τ.vars y) ∧ τ'.arrs "y" = τ.arrs "y" ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp ∧
      (∀ Lb : List (List ℕ), (L ++ [llNew L[3] d e z, atQW L[0] P Q sg σ]).Sublist Lb →
        BigRoom W R Lb b (τ.vars "nx") (τ.vars "mw") → τ'.vars "ovf" = 0) := by
  obtain ⟨cA, aA, hA⟩ := atT_run hAt hAV
  refine ⟨cA, aA, ?_⟩
  intro ez eph ed cw W R d e z iw p g P Q sg M0 e0 nS nF nC nL a1 a2 Kw σ L b τ hW har hlt hW24 hL h3 hdd hd
    htN hne hv hroom hez hcw hrR hz hbl hy hov hiw hitem hct hgP hgQ hgS hsg hRk hm0 he0 hnS hnF hnC hnL h1 hrd
    hsum h4
  -- step 1
  have r1 : Run (W + 1) (.assign "lvZ" ez) τ (τ.setVar "lvZ" z) (1 + ez.size) := Run.assign hez
  set τ1 := τ.setVar "lvZ" z
  have v1 : ∀ y, y ≠ "lvZ" → τ1.vars y = τ.vars y := fun y hy => by simp [τ1, hy]
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  have L1 : Lib L τ1 := hL.of (by rw [v1 "m" (by decide)]) (by rw [v1 "lt" (by decide)]) rfl rfl rfl
  -- step 2
  obtain ⟨τ2, r2, L2, iL2, v2, a2', ar2, hl2, o2, i2⟩ := llC_run (W := W) (d := d) (e := e) (z := z)
    (τ := τ1) (by rw [v1 "W" (by decide), hW]) har hl1 L1 h3 (by rw [v1 "dd" (by decide), hdd]) hd
    (by rw [v1 "lvN" (by decide), htN]) (by rw [v1 "ne" (by decide), hne]) (by simp [τ1]) hv hroom
  have fr2 : ∀ y, y ∉ llCV → y ≠ "lvZ" → τ2.vars y = τ.vars y := fun y h1 h2 => by rw [v2 y h1, v1 y h2]
  -- step 3
  obtain ⟨K3, r3, hK3⟩ := hcw τ2 fr2 hl2
  set τ3 := τ2.setVar "ow" iw
  have fr3 : ∀ y, y ∉ llCV → y ≠ "lvZ" → y ≠ "ow" → τ3.vars y = τ.vars y := fun y h1 h2 h3 => by
    simp only [τ3, vars_setVar, if_neg h3]; exact fr2 y h1 h2
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  set L' := L ++ [llNew L[3] d e z]
  have hL'l : L'.length = L.length + 1 := by simp [L']
  have g3 : ∀ y v, y ∉ llCV → y ≠ "lvZ" → y ≠ "ow" → τ.vars y = v → τ3.vars y = v :=
    fun y v a b c h => by rw [fr3 y a b c, h]
  have hiw' : iw < L'.length := by omega
  have hitem' : L'[iw] = itemW ((p, g), σ) := by
    simp only [L']; rw [List.getElem_append_left hiw]; exact hitem
  have hct' : IsCT L'[0] := by
    simp only [L']; rw [List.getElem_append_left (by omega)]; exact hct
  have h0L : L'[0] = L[0] := by simp only [L']; rw [List.getElem_append_left (by omega)]
  -- step 4
  obtain ⟨τ4, K4, r4, hK4, hL4, fr4, ya4, ar4, hl4, o4, i4, cp4⟩ := hA (W := W) (R := R) (iw := iw) (p := p)
    (g := g) (P := P) (Q := Q) (sg := sg) (σ := σ) (L := L') (b := b) (τ := τ3)
    (g3 "W" _ (by decide) (by decide) (by decide) hW) hW24 (fun b' => by simp only [τ3, arrs_setVar]; exact ar2 b')
    hl3 (L2.of (by simp [τ3]) (by simp [τ3]) rfl rfl rfl) (g3 "rR" _ (by decide) (by decide) (by decide) hrR)
    (g3 "z0" _ (by decide) (by decide) (by decide) hz) (g3 "bl" _ (by decide) (by decide) (by decide) hbl)
    (fun j hj => by
      simp only [τ3, arrs_setVar]; rw [a2' "y" (by decide)]; simp only [τ1, arrs_setVar]; exact hy j hj)
    (g3 "ovf" _ (by decide) (by decide) (by decide) hov) (by simp [τ3]) hiw' (by omega) hitem' hct'
    (g3 "gP" _ (by decide) (by decide) (by decide) hgP) (g3 "gQ" _ (by decide) (by decide) (by decide) hgQ)
    (g3 "gS" _ (by decide) (by decide) (by decide) hgS) hsg hRk
  rw [h0L] at hK4 hL4 cp4
  have hiw4 : (L'[iw]).length = L[iw].length := by rw [hitem', hitem]
  rw [hiw4] at hK4
  have kp4 : ∀ y, y ∈ upKeep → τ4.vars y = τ.vars y := fun y hy => by
    have k1 : y ∉ atTV := upKeep_atTV y hy
    have k2 : y ∉ atV := hAV y (upKeep_atKeep y hy)
    obtain ⟨k3, k4, k5⟩ := upKeep_llCV y hy
    rw [fr4 y k1 k2, fr3 y k3 k4 k5]
  have hiL4 : τ4.vars "iL" = L.length := by
    rw [fr4 "iL" (by decide) (hAV "iL" (by decide))]; simp only [τ3, vars_setVar, if_neg (by decide : ¬ ("iL" = "ow"))]
    exact iL2
  obtain ⟨e1, e2⟩ := h1 τ4 kp4
  have g4 : ∀ y v, y ∈ upKeep → τ.vars y = v → τ4.vars y = v := fun y v hy h => by rw [kp4 y hy, h]
  -- step 5
  obtain ⟨τ5, r5, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR5, np5, v5, a5, ar5, hl5, o5, i5⟩ :=
    hdFn_run (W := W) (M0 := M0) (iLL := L.length) (e0 := e0) (nE := e) (nS := nS) (nF := nF) (nC := nC)
      (nL := nL) (k := 3) (eph := eph) (ed := ed) (ei := .lit 0) (a3 := 0) (τ := τ4) ar4 hl4 (by omega)
      (g4 "m0" _ (by decide) hm0) hiL4 (g4 "e0" _ (by decide) he0) (g4 "ne" _ (by decide) hne)
      (g4 "nSG" _ (by decide) hnS) (g4 "nFA" _ (by decide) hnF) (g4 "nCO" _ (by decide) hnC)
      (g4 "nLV" _ (by decide) hnL) e1 e2 (evalB_lit (by omega))
      (fun y hy => ⟨(hrd y hy).1, (hrd y hy).2, by simp [exRv]⟩) (by omega) hsum h4
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))
  have hov5 : τ5.vars "ovf" = τ4.vars "ovf" := v5 "ovf" (by decide) (by decide)
  refine ⟨τ5, _, hrun, by omega, fun h0 => ?_, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR5, np5,
    fun y hy hy' => ?_, ?_, ar5, hl5, ?_, ?_, fun Lb hsub hB => ?_⟩
  · rw [hov5] at h0
    obtain ⟨hL4', hoe, -⟩ := hL4 h0
    refine ⟨?_, ?_⟩
    · have := hL4'.of (τ' := τ5) (v5 "m" (by decide) (by decide)) (v5 "lt" (by decide) (by decide))
        (a5 "a" (by decide)) (a5 "st" (by decide)) (a5 "ln" (by decide))
      simpa [L', List.append_assoc] using this
    · rw [v5 "oe" (by decide) (by decide), hoe, hL'l]
  · have hz1 : y ≠ "lvZ" := fun h => hy (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (by simp [h]))))
    have hz2 : y ≠ "ow" := fun h => hy (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (by simp [h]))))
    have hz3 : y ≠ "np" := fun h => hy (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (by simp [h]))))
    have hz4 : y ∉ llCV := fun h => hy (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h)))
    have hz5 : y ∉ atTV := fun h => hy (List.mem_append_left _ (List.mem_append_right _ h))
    have hz6 : y ∉ hdNames := fun h => hy (List.mem_append_right _ h)
    rw [v5 y hz3 hz6, fr4 y hz5 hy']
    simp only [τ3, vars_setVar, if_neg hz2]
    exact fr2 y hz4 hz1
  · rw [a5 "y" (by decide), ya4]; simp only [τ3, arrs_setVar]; rw [a2' "y" (by decide)]; simp [τ1]
  · rw [o5, o4]; simp only [τ3, out_setVar]; rw [o2]; simp [τ1]
  · rw [i5, i4]; simp only [τ3, inp_setVar]; rw [i2]; simp [τ1]
  · rw [hov5]
    refine cp4 Lb (by simpa [L', List.append_assoc] using hsub) ?_
    have hnx : τ3.vars "nx" = τ.vars "nx" := fr3 "nx" (by decide) (by decide) (by decide)
    have hmw : τ3.vars "mw" = τ.vars "mw" := fr3 "mw" (by decide) (by decide) (by decide)
    rw [hnx, hmw]; exact hB

theorem scR_brUpV : ∀ y ∈ scR, y ∉ brUpV := by decide
theorem scR_atKeep : ∀ y ∈ scR, y ∈ atKeep := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
/-- **The end of a round whose next call is the canonical form of atom words, with the head.** -/
theorem finUp_ok {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ∃ cA aA : ℕ, ∀ {ez eph ed : Expr} {cw : Com} {W R X d e z iw p g P Q sg M0 e0 nS nF nC nL a1 a2 Kw : ℕ}
    {σ : TypeTree} {sc wx b : List ℕ} {ws L : List (List ℕ)} {τ0 τ : Env}
    (P0 : PreR W R sc ws wx b τ0) (hX : sc.getD 1 0 = X) (hz0 : sc.getD 0 0 = 0) (hkq : kq0 < W)
    (hR : 1 ≤ R) (hsl : 9 ≤ sc.length) (M : FinMid W sc b L τ0 τ)
    (h3 : 3 < L.length) (hdd : τ.vars "dd" = d) (hd : d + 1 < (L[3]'h3).length) (htN : τ.vars "lvN" = ((L[3]'h3)[d + 1]'hd))
    (hne : τ.vars "ne" = e) (hv : ((L[3]'h3)[d + 1]'hd) + e ≤ W) (hroom : 2 * total L + L.length + d + z + 8 ≤ W)
    (hez : ez.evalB (W + 1) τ = some z)
    (hcw : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → ρ.vars y = τ.vars y) → EnvLt (W + 1) ρ →
      ∃ K', Run (W + 1) cw ρ (ρ.setVar "ow" iw) K' ∧ K' ≤ Kw)
    (hiw : iw < L.length) (hitem : (L[iw]'hiw) = itemW ((p, g), σ)) (hct : IsCT (L[0]'(Nat.lt_trans (by decide : 0 < 3) h3))) (hgP : τ.vars "gP" = P)
    (hgQ : τ.vars "gQ" = Q) (hgS : τ.vars "gS" = sg) (hsg : sg ≤ 1) (hRk : rhoPlus σ.k σ.q + 1 ≤ R)
    (hm0 : τ.vars "m0" = M0) (he0 : τ.vars "e0" = e0)
    (hnS : τ.vars "nSG" = nS) (hnF : τ.vars "nFA" = nF) (hnC : τ.vars "nCO" = nC) (hnL : τ.vars "nLV" = nL)
    (h1 : ∀ ρ : Env, (∀ y ∈ upKeep, ρ.vars y = τ.vars y) →
      eph.evalB (W + 1) ρ = some a1 ∧ ed.evalB (W + 1) ρ = some a2)
    (hrd : ∀ y ∈ hdNames, y ∉ exRv eph ∧ y ∉ exRv ed)
    (hsum : nL + e < W + 1) (h4 : 4 + nS + nF + nC < W + 1)
    (hps : ∀ p ∈ psFn M0 L.length e0 e nS nF nC nL, p.1 + p.2 ≤ L.length + 2),
    ∃ τ' K, Run (W + 1) (brUp ez cw atC eph ed) τ τ' K ∧
      K ≤ ez.size + 40 * (d + z) + Kw + kAtT (L ++ [llNew (L[3]'h3) d e z]) b (atQW (L[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q sg σ)
        (cA * ((L[0]'(Nat.lt_trans (by decide : 0 < 3) h3)).length + 1) * ((L[iw]'hiw).length + σ.ℓ + rhoPlus σ.k σ.q + 1) ^ aA) +
        asgK (hdFn eph ed (.lit 0) 3) + 500 ∧
      (τ'.vars "ovf" = 0 →
        TailIn W R X (L ++ [llNew (L[3]'h3) d e z, atQW (L[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q sg σ]) (psFn M0 L.length e0 e nS nF nC nL) 3
          (atQW (L[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q sg σ) b τ' ∧
        τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧
        hsV.map τ'.vars = sc.take 9 ++ [a1, a2, 0, 0, nS, 0, 0, nL + e] ∧ τ'.vars "po" = 0 ∧
        τ'.vars "nx" = τ0.vars "nx" ∧ τ'.vars "mw" = τ0.vars "mw" ∧ τ'.out = []) ∧
      (BigRoom W R (L ++ [llNew (L[3]'h3) d e z, atQW (L[0]'(Nat.lt_trans (by decide : 0 < 3) h3)) P Q sg σ]) b (τ0.vars "nx") (τ0.vars "mw") →
        τ'.vars "ovf" = 0) := by
  obtain ⟨cA, aA, hB⟩ := brUp_run hAt hAV
  refine ⟨cA, aA, ?_⟩
  intro ez eph ed cw W R X d e z iw p g P Q sg M0 e0 nS nF nC nL a1 a2 Kw σ sc wx b ws L τ0 τ P0 hX hz0 hkq hR
    hsl M h3 hdd hd htN hne hv hroom hez hcw hiw hitem hct hgP hgQ hgS hsg hRk hm0 he0 hnS hnF hnC hnL h1 hrd
    hsum h4 hps
  have hfr : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"], τ.vars y = τ0.vars y := M.hfr
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨τ', K, r, hK, hLo, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR, np, fr, ya, ar, hl, o, -,
    cp⟩ := hB (ez := ez) (eph := eph) (ed := ed) (cw := cw) (R := R) (iw := iw) (p := p) (g := g) (σ := σ)
      (b := b) M.hW M.harr M.hlt (by omega) M.hlib h3 hdd hd htN hne hv hroom hez hcw
      (by rw [hfr "rR" (by simp), P0.hrR]) (by
        have h0 : τ0.vars "z0" = sc.getD 0 0 := P0.hsc 0 (by omega)
        rw [hfr "z0" (by simp), h0, hz0])
      (by rw [hfr "bl" (by simp), P0.hbl]) (fun j hj => by rw [M.hy]; exact P0.hy j hj) M.hov hiw hitem hct
      hgP hgQ hgS hsg hRk hm0 he0 hnS hnF hnC hnL h1 hrd hsum h4
  have fr' : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"], τ'.vars y = τ.vars y := fun y hy => by
    apply fr
    · revert y; decide
    · exact hAV y (by revert y; decide)
  have g : ∀ j (h : j < 9), τ'.vars (scR[j]'(by simp [scR]; omega)) = sc.getD j 0 := fun j h => by
    rw [fr _ (scR_brUpV _ (List.getElem_mem _)) (hAV _ (scR_atKeep _ (List.getElem_mem _)))]
    exact M.hsc j (by omega)
  refine ⟨τ', K, r, hK, fun hov => ?_, fun hB => cp _ (List.Sublist.refl _) (by
    rw [hfr "nx" (by simp), hfr "mw" (by simp)]; exact hB)⟩
  obtain ⟨L', oe⟩ := hLo hov
  refine ⟨tailIn_of P0 hX hz0 hkq hR hl ar (fun y hy => ?_) ?_ L' hov ?_ n11 PR
    (by rw [np]; rfl) (fun p hp => by have := hps p hp; simp; omega) (by simp [psFn]), n1, n2,
    hsV_of hsl g n3 n4 n5 n6 n7 n8 n9 n10, n12, ?_, ?_, by rw [o, M.hout]⟩
  · have hy' : y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h | h | h | h <;> simp [h]
    rw [fr' y hy', M.hfr y hy']
  · rw [ya, M.hy]
  · refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun _ => ⟨L.length + 1, by simp, oe, ?_⟩, by omega⟩
    simp
  · rw [fr' "nx" (by simp), M.hfr "nx" (by simp)]
  · rw [fr' "mw" (by simp), M.hfr "mw" (by simp)]

end Lax185574Proofs.ResolveRam.Glue
