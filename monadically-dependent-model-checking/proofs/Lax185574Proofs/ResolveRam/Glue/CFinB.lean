import Lax185574Proofs.ResolveRam.Glue.CFinLL
import Lax185574Proofs.ResolveRam.Glue.CFinH

/-!
The end of a round that finishes an item on the way down and whose next
call is the rank shift of an item.

`brDn ez cx eph ed ei` sets `lvZ` to the number of new empty levels
(`ez`), appends the new lengths of the levels (`llC`), sets the index
`ox` of the next item word (`cx`), and writes the new head and the plan
(`hdFn`, `plFn`) (`brDn_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- The end of a round whose next call is the rank shift of an item. -/
def brDn (ez : Expr) (cx : Com) (eph ed ei : Expr) : Com :=
  .seq (.assign "lvZ" ez) (.seq llC (.seq cx (.seq (asgs (hdFn eph ed ei 0)) (stPlan plFn))))

/-- The scalars that `brDn` may write. -/
def brDnV : List String := ["lvZ", "ox", "np"] ++ llCV ++ hdNames

set_option maxHeartbeats 1600000 in
/-- **The end of a round whose next call is the rank shift of an item.** -/
theorem brDn_run {ez eph ed ei : Expr} {cx : Com} {W d e z ox M0 e0 nS nF nC nL a1 a2 a3 Kx : ℕ}
    {L : List (List ℕ)} {τ : Env}
    (hW : τ.vars "W" = W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hW64 : 64 ≤ W) (hL : Lib L τ)
    (h3 : 3 < L.length) (hdd : τ.vars "dd" = d) (hd : d + 1 < L[3].length) (htN : τ.vars "lvN" = L[3][d + 1])
    (hne : τ.vars "ne" = e) (hv : L[3][d + 1] + e ≤ W) (hroom : 2 * total L + L.length + d + z + 8 ≤ W)
    (hez : ez.evalB (W + 1) τ = some z)
    (hcx : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → ρ.vars y = τ.vars y) → EnvLt (W + 1) ρ →
      ∃ K', Run (W + 1) cx ρ (ρ.setVar "ox" ox) K' ∧ K' ≤ Kx)
    (hm0 : τ.vars "m0" = M0) (he0 : τ.vars "e0" = e0)
    (hnS : τ.vars "nSG" = nS) (hnF : τ.vars "nFA" = nF) (hnC : τ.vars "nCO" = nC) (hnL : τ.vars "nLV" = nL)
    (h1 : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → y ≠ "ox" → ρ.vars y = τ.vars y) →
      eph.evalB (W + 1) ρ = some a1 ∧ ed.evalB (W + 1) ρ = some a2 ∧ ei.evalB (W + 1) ρ = some a3)
    (hrd : ∀ y ∈ hdNames, y ∉ exRv eph ∧ y ∉ exRv ed ∧ y ∉ exRv ei)
    (hsum : nL + e < W + 1) (h4 : 4 + nS + nF + nC < W + 1) :
    ∃ τ' K, Run (W + 1) (brDn ez cx eph ed ei) τ τ' K ∧
      K ≤ ez.size + 40 * (d + z) + Kx + asgK (hdFn eph ed ei 0) + 500 ∧
      Lib (L ++ [llNew L[3] d e z]) τ' ∧ τ'.vars "ox" = ox ∧
      τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧ τ'.vars "Nph" = a1 ∧ τ'.vars "Nd" = a2 ∧ τ'.vars "Ni" = a3 ∧
      τ'.vars "Nm" = 0 ∧ τ'.vars "NSG" = nS ∧ τ'.vars "NFA" = 0 ∧ τ'.vars "NCO" = 0 ∧
      τ'.vars "NLV" = nL + e ∧ τ'.vars "qk" = 0 ∧ τ'.vars "po" = 0 ∧
      PreAt "PR" (prW (psFn M0 L.length e0 e nS nF nC nL)) τ' ∧ τ'.vars "np" = 7 ∧
      (∀ y, y ∉ brDnV → τ'.vars y = τ.vars y) ∧
      (∀ b, b ∉ ["a", "st", "ln", "OB", "PR"] → τ'.arrs b = τ.arrs b) ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
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
  obtain ⟨K3, r3, hK3⟩ := hcx τ2 fr2 hl2
  set τ3 := τ2.setVar "ox" ox
  have fr3 : ∀ y, y ∉ llCV → y ≠ "lvZ" → y ≠ "ox" → τ3.vars y = τ.vars y := fun y h1 h2 h3 => by
    simp only [τ3, vars_setVar, if_neg h3]; exact fr2 y h1 h2
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  obtain ⟨e1, e2, e3⟩ := h1 τ3 fr3
  have g3 : ∀ y v, y ∉ llCV → y ≠ "lvZ" → y ≠ "ox" → τ.vars y = v → τ3.vars y = v :=
    fun y v a b c h => by rw [fr3 y a b c, h]
  -- step 4
  obtain ⟨τ4, r4, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR4, np4, v4, a4, ar4, hl4, o4, i4⟩ :=
    hdFn_run (W := W) (M0 := M0) (iLL := L.length) (e0 := e0) (nE := e) (nS := nS) (nF := nF) (nC := nC)
      (nL := nL) (k := 0) (eph := eph) (ed := ed) (ei := ei) (τ := τ3) (fun b => by simp only [τ3]; exact ar2 b)
      hl3 hW64 (g3 "m0" _ (by decide) (by decide) (by decide) hm0)
      (by simp only [τ3]; rw [vars_setVar, if_neg (by decide : ¬ ("iL" = "ox"))]; exact iL2)
      (g3 "e0" _ (by decide) (by decide) (by decide) he0) (g3 "ne" _ (by decide) (by decide) (by decide) hne)
      (g3 "nSG" _ (by decide) (by decide) (by decide) hnS) (g3 "nFA" _ (by decide) (by decide) (by decide) hnF)
      (g3 "nCO" _ (by decide) (by decide) (by decide) hnC) (g3 "nLV" _ (by decide) (by decide) (by decide) hnL)
      e1 e2 e3 hrd (by omega) hsum h4
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 r4))
  refine ⟨τ4, _, hrun, by omega, ?_, ?_, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR4, np4,
    fun y hy => ?_, fun b hb => ?_, ar4, hl4, ?_, ?_⟩
  · refine L2.of ?_ ?_ (a4 "a" (by decide)) (a4 "st" (by decide)) (a4 "ln" (by decide))
    · rw [v4 "m" (by decide) (by decide)]; simp [τ3]
    · rw [v4 "lt" (by decide) (by decide)]; simp [τ3]
  · rw [v4 "ox" (by decide) (by decide)]; simp [τ3]
  · have hz1 : y ≠ "lvZ" := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (by simp [h])))
    have hz2 : y ≠ "ox" := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (by simp [h])))
    have hz3 : y ≠ "np" := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (by simp [h])))
    have hz4 : y ∉ llCV := fun h => hy (List.mem_append_left _ (List.mem_append_right _ h))
    have hz6 : y ∉ hdNames := fun h => hy (List.mem_append_right _ h)
    rw [v4 y hz3 hz6]
    simp only [τ3, vars_setVar, if_neg hz2]
    exact fr2 y hz4 hz1
  · have hb1 : b ≠ "PR" := fun h => hb (by simp [h])
    have hb2 : b ∉ ["a", "st", "ln", "OB"] := fun h => hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    rw [a4 b hb1]
    simp only [τ3, arrs_setVar]
    rw [a2' b hb2]; simp [τ1]
  · rw [o4]; simp only [τ3, out_setVar]; rw [o2]; simp [τ1]
  · rw [i4]; simp only [τ3, inp_setVar]; rw [i2]; simp [τ1]

/-- The environment of a round in the middle of the finishing of an item:
the scalars of the state are those at the start of the round, the
library is `L`. -/
structure FinMid (W : ℕ) (sc b : List ℕ) (L : List (List ℕ)) (τ0 τ : Env) : Prop where
  hW : τ.vars "W" = W
  harr : ArrW W τ
  hlt : EnvLt (W + 1) τ
  hlib : Lib L τ
  hsc : ∀ j (h : j < 17), τ.vars (scR[j]'(by simp [scR]; omega)) = sc.getD j 0
  hfr : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"], τ.vars y = τ0.vars y
  hy : τ.arrs "y" = τ0.arrs "y"
  hov : τ.vars "ovf" = 0
  hout : τ.out = []

theorem FinMid.var {W : ℕ} {sc b : List ℕ} {L : List (List ℕ)} {τ0 τ : Env} (M : FinMid W sc b L τ0 τ)
    (j : ℕ) (hj : j < 17) :
    (Expr.var (scR[j]'(by simp [scR]; omega))).evalB (W + 1) τ = some (sc.getD j 0) :=
  ev_var (M.hsc j hj) (by rw [← M.hsc j hj]; exact M.hlt.vars _)

theorem scR_brDnV : ∀ y ∈ scR, y ∉ brDnV := by decide

set_option maxHeartbeats 1600000 in
/-- **The end of a round whose next call is the rank shift of an item, with the head.** -/
theorem finDn_ok {ez eph ed ei : Expr} {cx : Com} {W R X d e z ox M0 e0 nS nF nC nL a1 a2 a3 Kx : ℕ}
    {sc wx b : List ℕ} {ws L : List (List ℕ)} {τ0 τ : Env}
    (P0 : PreR W R sc ws wx b τ0) (hX : sc.getD 1 0 = X) (hz0 : sc.getD 0 0 = 0) (hkq : kq0 < W)
    (hR : 1 ≤ R) (hsl : 9 ≤ sc.length) (M : FinMid W sc b L τ0 τ)
    (h3 : 3 < L.length) (hdd : τ.vars "dd" = d) (hd : d + 1 < L[3].length) (htN : τ.vars "lvN" = L[3][d + 1])
    (hne : τ.vars "ne" = e) (hv : L[3][d + 1] + e ≤ W) (hroom : 2 * total L + L.length + d + z + 8 ≤ W)
    (hez : ez.evalB (W + 1) τ = some z)
    (hcx : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → ρ.vars y = τ.vars y) → EnvLt (W + 1) ρ →
      ∃ K', Run (W + 1) cx ρ (ρ.setVar "ox" ox) K' ∧ K' ≤ Kx)
    (hm0 : τ.vars "m0" = M0) (he0 : τ.vars "e0" = e0)
    (hnS : τ.vars "nSG" = nS) (hnF : τ.vars "nFA" = nF) (hnC : τ.vars "nCO" = nC) (hnL : τ.vars "nLV" = nL)
    (h1 : ∀ ρ : Env, (∀ y, y ∉ llCV → y ≠ "lvZ" → y ≠ "ox" → ρ.vars y = τ.vars y) →
      eph.evalB (W + 1) ρ = some a1 ∧ ed.evalB (W + 1) ρ = some a2 ∧ ei.evalB (W + 1) ρ = some a3)
    (hrd : ∀ y ∈ hdNames, y ∉ exRv eph ∧ y ∉ exRv ed ∧ y ∉ exRv ei)
    (hsum : nL + e < W + 1) (h4 : 4 + nS + nF + nC < W + 1)
    (hox : ox < L.length) (h2ox : 2 ≤ L[ox].length)
    (hps : ∀ p ∈ psFn M0 L.length e0 e nS nF nC nL, p.1 + p.2 ≤ L.length + 1) :
    ∃ τ' K, Run (W + 1) (brDn ez cx eph ed ei) τ τ' K ∧
      K ≤ ez.size + 40 * (d + z) + Kx + asgK (hdFn eph ed ei 0) + 500 ∧
      TailIn W R X (L ++ [llNew L[3] d e z]) (psFn M0 L.length e0 e nS nF nC nL) 0 (L[ox].drop 2) b τ' ∧
      τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧
      hsV.map τ'.vars = sc.take 9 ++ [a1, a2, a3, 0, nS, 0, 0, nL + e] ∧ τ'.vars "po" = 0 ∧
      τ'.vars "nx" = τ0.vars "nx" ∧ τ'.vars "mw" = τ0.vars "mw" ∧ τ'.out = [] ∧ τ'.vars "ovf" = 0 := by
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨τ', K, r, hK, L', ox', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, PR, np, fr, fa, ar, hl, o, -⟩ :=
    brDn_run (ez := ez) (eph := eph) (ed := ed) (ei := ei) (cx := cx) M.hW M.harr M.hlt (by omega) M.hlib h3
      hdd hd htN hne hv hroom hez hcx hm0 he0 hnS hnF hnC hnL h1 hrd hsum h4
  have fr' : ∀ y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw", "ovf"], τ'.vars y = τ.vars y := fun y hy => by
    apply fr; revert y; decide
  have hov : τ'.vars "ovf" = 0 := by rw [fr' "ovf" (by simp), M.hov]
  have g : ∀ j (h : j < 9), τ'.vars (scR[j]'(by simp [scR]; omega)) = sc.getD j 0 := fun j h => by
    rw [fr _ (scR_brDnV _ (List.getElem_mem _))]; exact M.hsc j (by omega)
  refine ⟨τ', K, r, hK, tailIn_of P0 hX hz0 hkq hR hl ar (fun y hy => ?_) ?_ L' hov ?_ n11 PR
    (by rw [np]; rfl) (fun p hp => by have := hps p hp; simp; omega) (by simp [psFn]), n1, n2,
    hsV_of hsl g n3 n4 n5 n6 n7 n8 n9 n10, n12, ?_, ?_, by rw [o, M.hout], hov⟩
  · have hy' : y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h | h | h | h <;> simp [h]
    have hy2 : y ∈ ["W", "rR", "bl", "gX", "z0", "nx", "mw", "ovf"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h | h | h | h <;> simp [h]
    rw [fr' y hy2, M.hfr y hy']
  · rw [fa "y" (by decide), M.hy]
  · refine ⟨fun _ => ⟨ox, by simp; omega, ?_, ox', ?_⟩, fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), by omega⟩
    · rw [List.getElem_append_left hox]; exact h2ox
    · rw [List.getElem_append_left hox]
  · rw [fr' "nx" (by simp), M.hfr "nx" (by simp)]
  · rw [fr' "mw" (by simp), M.hfr "mw" (by simp)]

end Lax185574Proofs.ResolveRam.Glue
