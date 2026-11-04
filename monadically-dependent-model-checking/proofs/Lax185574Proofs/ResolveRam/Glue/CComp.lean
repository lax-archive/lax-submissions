import Lax185574Proofs.ResolveRam.Glue.CShift

/-!
The case of a later round after a composition of an item on the way
down that is not the last one (position `dn d i m`, `2 ≤ m`,
`m + 1 < nDn d i`).

The case appends the empty word and the answer of the composition to
the library, takes the state of `dn d i (m + 1)` as ranges (`psComp`,
`planW_comp`), and prepares the next composition: the answer of the
rank shift is word `1` of the library and the next member of the far
tree is word `4 + |SG| + m - 1` (`bComp_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam

/-- The fixed answers cut at the end of the answer of a composition. -/
noncomputable def dlC : ℕ := yA0.length + yB0.length + yE0.length + yF0.length

/-- The fixed answers in front of the answer of a composition. -/
noncomputable def plC : ℕ := yA0.length + yB0.length

/-- The scalars of the new head and of the next composition. -/
def hdC2 : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit 1), ("Nd", .var "dd"), ("Ni", .var "ii"),
    ("Nm", .add (.var "mm") (.lit 1)),
    ("NSG", .var "nSG"), ("NFA", .var "nFA"), ("NCO", .add (.var "nCO") (.lit 1)), ("NLV", .var "nLV"),
    ("os", .lit 1), ("of", .sub (.add (.add (.lit 4) (.var "nSG")) (.var "mm")) (.lit 1)),
    ("qk", .lit 2), ("po", .lit 0)]

/-- The plan of the state after a composition. -/
def psComp (M0 a l : ℕ) : List (ℕ × ℕ) := [(0, a), (M0 + 1, 1), (a, l)]

/-- The plan as expressions. -/
def plC2 : List (Expr × Expr) :=
  [(.lit 0, .add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO")), (.add (.var "m0") (.lit 1), .lit 1),
    (.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO"), .var "nLV")]

/-- The case after a composition that is not the last one. -/
noncomputable def bComp : Com :=
  .seq (.assign "m0" (.var "m")) (.seq apE (.seq (apY plC dlC) (.seq (asgs hdC2) (stPlan plC2))))

/-- The cost of the case after a composition. -/
def kComp (b : List ℕ) : ℕ := b.length * 18 + 2000

theorem planW_comp (w : SW) (Y : List ℕ) (hOU : w.OU = []) :
    planW (w.ws ++ [[], Y]) (psComp w.ws.length (4 + w.SG.length + w.FA.length + w.CO.length) w.LV.length) =
      ({ w with CO := w.CO ++ [Y] } : SW).ws := by
  set A := w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO) with hA
  have hws : w.ws = A ++ w.LV := by simp [SW.ws, hA, hOU]
  have hAl : A.length = 4 + w.SG.length + w.FA.length + w.CO.length := by simp [hA]; omega
  simp only [planW, psComp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have r1 : rng (w.ws ++ [[], Y]) 0 (4 + w.SG.length + w.FA.length + w.CO.length) = A := by
    rw [rng_append_left (by rw [hws]; simp; omega), hws, ← hAl, rng_append_left (by omega), rng_full]
  have r2 : rng (w.ws ++ [[], Y]) (w.ws.length + 1) 1 = [Y] := by
    rw [rng_one (by simp)]; simp
  have r3 : rng (w.ws ++ [[], Y]) (4 + w.SG.length + w.FA.length + w.CO.length) w.LV.length = w.LV := by
    rw [rng_append_left (by rw [hws]; simp; omega), hws, ← hAl]
    have := rng_append_right (L := A) (M := w.LV) (lo := 0) (N := w.LV.length)
    simp only [Nat.add_zero] at this; rw [this]; simp [rng]
  rw [r1, r2, r3]
  simp [SW.ws, hA, hOU]

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem dLen_comp (σ ν : TypeTree) : dLen (.compose σ ν) = dlC := by
  simp [dLen, dlC]; omega

theorem preLen_comp (σ ν : TypeTree) : preLen (.compose σ ν) = plC := rfl

theorem OU_dn (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.dn d i m)).OU = [] := by simp [swAt]

theorem next_comp {d i m : ℕ} (h : m + 1 < nDn G P Q s k₀ q₀ d i) :
    next G P Q s k₀ q₀ (.dn d i m) = .dn d i (m + 1) := by
  simp only [next]; rw [if_pos h]

set_option maxHeartbeats 1600000 in
/-- **The case after a composition that is not the last one.** -/
theorem bComp_ok {d i m W R : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hmn : m + 1 < nDn G P Q s k₀ q₀ d i) (hR : 1 ≤ R) :
    BodyCall bComp W R (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ (.dn d i m))
      (swAt G P Q s k₀ q₀ (.dn d i m)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (.dn d i m)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))
      ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [[], realY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))])
      (psComp (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
        (4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
          (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length) (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length)
      (kindOf (callOf G P Q s k₀ q₀ (.dn d i (m + 1))))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i (m + 1))))
      (tagOf G P Q s k₀ q₀ (.dn d i (m + 1))) (winOf G P Q s k₀ q₀ (.dn d i (m + 1)))
      (scW G P Q s k₀ q₀ (.dn d i (m + 1)))
      (kComp (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))) := by
  intro τ0 P0 hov hkq
  set t := (itm G P Q s k₀ q₀ d i).2
  set F := faP G (dataOf G P Q s k₀ q₀) t
  have hnd := nDn_itm hi
  rw [← show F = faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2 from rfl] at hnd
  have hF1 : m - 1 < F.length := by omega
  obtain ⟨hb0, hc0⟩ := callOf_dn_comp G P Q s k₀ q₀ hi hm2 (by omega)
  obtain ⟨hb1, hc1⟩ := callOf_dn_comp G P Q s k₀ q₀ (m := m + 1) hi (by omega) hmn
  simp only [show m + 1 - 2 = m - 1 by omega] at hc1
  rw [hc0] at P0 ⊢
  rw [hc1]
  set w0 := swAt G P Q s k₀ q₀ (.dn d i m)
  set ws := w0.ws
  set b := rY G k₀ q₀ (.compose (shOf G t) F[m - 2])
  set Y := realY G k₀ q₀ (.compose (shOf G t) F[m - 2])
  have hSH : w0.SH = toWord (shOf G t) := by simp [w0, swAt, show 1 ≤ m by omega, t]
  have hFAw : w0.FA = F.map toWord := by simp [w0, swAt, hm2, F, t]
  have hCOl : w0.CO.length = m - 2 := by
    simp [w0, swAt, length_coW]; rw [← show F = faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2 from rfl]
    omega
  have hroom : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS := room_bound hroom hR
  obtain ⟨hS1, hS2, hS3, hS4⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hl0 := P0.hlt
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i m)).getD j 0 := P0.hsc
  have hdd : τ0.vars "dd" = d := by simpa [scR, scW_dn] using hsc 10 (by omega)
  have hii : τ0.vars "ii" = i := by simpa [scR, scW_dn] using hsc 11 (by omega)
  have hmm : τ0.vars "mm" = m := by simpa [scR, scW_dn] using hsc 12 (by omega)
  have hSG : τ0.vars "nSG" = w0.SG.length := by simpa [scR, scW_dn] using hsc 13 (by omega)
  have hFA : τ0.vars "nFA" = w0.FA.length := by simpa [scR, scW_dn] using hsc 14 (by omega)
  have hCO : τ0.vars "nCO" = w0.CO.length := by simpa [scR, scW_dn] using hsc 15 (by omega)
  have hLV : τ0.vars "nLV" = w0.LV.length := by simpa [scR, scW_dn] using hsc 16 (by omega)
  have hOU := OU_dn G P Q s k₀ q₀ d i m
  have hwsl : ws.length = 4 + w0.SG.length + w0.FA.length + w0.CO.length + w0.LV.length + w0.OU.length := by
    simp only [ws, SW.ws, List.length_append, List.length_cons, List.length_nil]
  rw [hOU] at hwsl
  simp only [List.length_nil, Nat.add_zero] at hwsl
  have hFAl : w0.FA.length = F.length := by rw [hFAw]; simp
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
  obtain ⟨pre, post, hsp, hpre, hpp⟩ := rY_split G k₀ q₀ (.compose (shOf G t) F[m - 2])
  have hdl : dlC ≤ b.length := by
    rw [← dLen_comp (shOf G t) F[m - 2], ← hpp]; simp only [b, hsp, List.length_append]; omega
  have hpd : plC ≤ dlC := by unfold plC dlC; omega
  obtain ⟨τ3, r3, L3, f3, a3, ar3, o3, i3⟩ := apY_run (pl := plC) (dl := dlC) L2 ar2
    (by rw [f2 "bl" (by decide), show τ1.vars "bl" = τ0.vars "bl" by simp [τ1], P0.hbl]) hyb hdl hpd
    (by have : plC ≤ b.length := by omega
        simp only [total_append, total_single, List.length_append, List.length_cons, List.length_nil]; omega) hbv
  have hYw : (b.drop plC).take (b.length - dlC) = Y := by
    have := realY_seg G k₀ q₀ (.compose (shOf G t) F[m - 2])
    rw [dLen_comp, preLen_comp] at this; exact this
  rw [hYw, List.append_assoc] at L3
  set L := ws ++ [[], Y]
  have fr3 : ∀ y, y ∉ apV → y ≠ "m0" → τ3.vars y = τ0.vars y := fun y h1 h2 => by
    rw [f3 y h1, f2 y h1]; simp [τ1, h2]
  have ar3' : ∀ b', b' ∉ ["a", "st", "ln"] → τ3.arrs b' = τ0.arrs b' := fun b' hb => by
    rw [a3 b' hb, a2 b' hb]; rfl
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt (Run.seq r1 (Run.seq r2 r3)) hl0
  have hLl : L.length = ws.length + 2 := by simp [L]
  -- step 4: the head scalars and the next composition
  have hv3 : ∀ y v, y ∉ apV → y ≠ "m0" → τ0.vars y = v → (Expr.var y).evalB (W + 1) τ3 = some v :=
    fun y v h1 h2 h => ev_var (by rw [fr3 y h1 h2, h]) (by rw [← h, ← fr3 y h1 h2]; exact hl3.vars _)
  let fS : String → ℕ := fun y =>
    if y = "Nt" ∨ y = "Nph" ∨ y = "os" then 1 else if y = "Nd" then d else if y = "Ni" then i
    else if y = "Nm" then m + 1 else if y = "NSG" then w0.SG.length else if y = "NFA" then w0.FA.length
    else if y = "NCO" then w0.CO.length + 1 else if y = "NLV" then w0.LV.length
    else if y = "of" then 4 + w0.SG.length + m - 1 else if y = "qk" then 2 else 0
  obtain ⟨τ4, r4, s4, f4, a4, o4, i4⟩ := asgs_run (B := W + 1) (τ := τ3) (l := hdC2) (f := fS)
    (by
      intro p hp
      simp only [hdC2, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show fS "Nt" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nw" = 0 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nph" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "Nd" = d by simp [fS]]; exact hv3 "dd" _ (by decide) (by decide) hdd
      · rw [show fS "Ni" = i by simp [fS]]; exact hv3 "ii" _ (by decide) (by decide) hii
      · rw [show fS "Nm" = m + 1 by simp [fS]]
        exact ev_add (hv3 "mm" _ (by decide) (by decide) hmm) (evalB_lit (by omega)) (by omega)
      · rw [show fS "NSG" = w0.SG.length by simp [fS]]; exact hv3 "nSG" _ (by decide) (by decide) hSG
      · rw [show fS "NFA" = w0.FA.length by simp [fS]]; exact hv3 "nFA" _ (by decide) (by decide) hFA
      · rw [show fS "NCO" = w0.CO.length + 1 by simp [fS]]
        exact ev_add (hv3 "nCO" _ (by decide) (by decide) hCO) (evalB_lit (by omega)) (by omega)
      · rw [show fS "NLV" = w0.LV.length by simp [fS]]; exact hv3 "nLV" _ (by decide) (by decide) hLV
      · rw [show fS "os" = 1 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "of" = 4 + w0.SG.length + m - 1 by simp [fS]]
        exact ev_sub (ev_add (ev_add (evalB_lit (by omega)) (hv3 "nSG" _ (by decide) (by decide) hSG) (by omega))
          (hv3 "mm" _ (by decide) (by decide) hmm) (by omega)) (evalB_lit (by omega)) (by omega)
      · rw [show fS "qk" = 2 by simp [fS]]; exact evalB_lit (by omega)
      · rw [show fS "po" = 0 by simp [fS]]; exact evalB_lit (by omega))
    (by decide)
  have fr4 : ∀ y, y ∉ apV → y ≠ "m0" → y ∉ hdC2.map Prod.fst → τ4.vars y = τ0.vars y :=
    fun y h1 h2 h3 => by rw [f4 y h3, fr3 y h1 h2]
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have ar4 : ArrW W τ4 := fun b' => by rw [a4]; exact ar3 b'
  -- step 5: the plan
  have hm04 : τ4.vars "m0" = ws.length := by
    rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide)]; simp [τ1]
  have hv4 : ∀ y v, y ∉ apV → y ≠ "m0" → y ∉ hdC2.map Prod.fst → τ0.vars y = v →
      (Expr.var y).evalB (W + 1) τ4 = some v :=
    fun y v h1 h2 h3 h => ev_var (by rw [fr4 y h1 h2 h3, h]) (by rw [← h, ← fr4 y h1 h2 h3]; exact hl4.vars _)
  have ea : (Expr.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO")).evalB (W + 1) τ4 =
      some (4 + w0.SG.length + w0.FA.length + w0.CO.length) :=
    ev_add (ev_add (ev_add (evalB_lit (by omega)) (hv4 "nSG" _ (by decide) (by decide) (by decide) hSG) (by omega))
      (hv4 "nFA" _ (by decide) (by decide) (by decide) hFA) (by omega))
      (hv4 "nCO" _ (by decide) (by decide) (by decide) hCO) (by omega)
  obtain ⟨τ5, r5, PR5, np5, f5, a5, l5, o5, i5⟩ := stPlan_run (W := W) (l := plC2)
    (ps := psComp ws.length (4 + w0.SG.length + w0.FA.length + w0.CO.length) w0.LV.length)
    (τ := τ4) rfl (ar4 "PR") (by simp [plC2]; omega)
    (by
      intro j hj
      simp only [plC2, List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), ea⟩
      · exact ⟨ev_add (ev_var hm04 (by omega)) (evalB_lit (by omega)) (by omega), evalB_lit (by omega)⟩
      · exact ⟨ea, hv4 "nLV" _ (by decide) (by decide) (by decide) hLV⟩)
    (by decide)
  have fr5 : ∀ y, y ∉ apV → y ≠ "m0" → y ∉ hdC2.map Prod.fst → y ≠ "np" → τ5.vars y = τ0.vars y :=
    fun y h1 h2 h3 h4 => by rw [f5 y h4, fr4 y h1 h2 h3]
  have hS5 : ∀ y, y ∈ hdC2.map Prod.fst → τ5.vars y = fS y := fun y hy => by
    rw [f5 y (by intro h; subst h; simp [hdC2] at hy)]; exact s4 y hy
  have hrun : Run (W + 1) bComp τ0 τ5 (kComp b) := by
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    simp only [kComp, asgK, hdC2, plC2, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt hrun hl0
  have ar5 : ArrW W τ5 := fun b' => by
    by_cases hb : b' = "PR"
    · subst hb; exact l5
    · rw [a5 b' hb]; exact ar4 b'
  have ha5 : ∀ b', b' ≠ "PR" → τ5.arrs b' = τ3.arrs b' := fun b' hb => by rw [a5 b' hb, a4]
  have hov5 : τ5.vars "ovf" = 0 := by
    rw [fr5 "ovf" (by decide) (by decide) (by decide) (by decide), hov]
  have hscR : ∀ y ∈ scR, y ∉ apV ∧ y ≠ "m0" ∧ y ∉ hdC2.map Prod.fst ∧ y ≠ "np" := by decide
  have g : ∀ j (h : j < 9), τ5.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ (.dn d i m)).getD j 0 := fun j h => by
    obtain ⟨a1, a2, a3, a4⟩ := hscR _ (List.getElem_mem _)
    rw [fr5 _ a1 a2 a3 a4]; exact hsc j (by omega)
  -- the new state
  have hFm : m - 1 < w0.FA.length := by omega
  have hjf : 4 + w0.SG.length + (m - 1) < L.length := by omega
  refine ⟨τ5, kComp b, hrun, le_rfl, fun _ => ⟨⟨?_, hkq, ar5, hl5, ?_, hR, ?_, ?_, ?_, ?_, ?_, hov5, ?_, ?_,
    PR5, np5, ?_, by simp [psComp]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => hov5⟩
  · rw [fr5 "W" (by decide) (by decide) (by decide) (by decide), P0.hW]
  · rw [fr5 "rR" (by decide) (by decide) (by decide) (by decide), P0.hrR]
  · refine L3.of ?_ ?_ (ha5 "a" (by decide)) (ha5 "st" (by decide)) (ha5 "ln" (by decide))
    · rw [f5 "m" (by decide), f4 _ (by decide)]
    · rw [f5 "lt" (by decide), f4 _ (by decide)]
  · simpa [scR, scW_dn] using g 0 (by omega)
  · rw [fr5 "bl" (by decide) (by decide) (by decide) (by decide), P0.hbl]
  · intro j hj; rw [ha5 "y" (by decide), ar3' "y" (by decide)]; exact P0.hy j hj
  · simpa [scR, scW_dn] using g 1 (by omega)
  · -- the real query of the composition
    refine ⟨fun h => by simp [kindOf] at h, fun h => by simp [kindOf] at h, fun _ => ?_,
      fun h => by simp [kindOf] at h, by simp [kindOf]⟩
    have h1 : (L[1]'(by omega)) = toWord (shOf G t) := by
      rw [← hSH]; simp [L, ws, SW.ws]
    have h2 : (L[4 + w0.SG.length + (m - 1)]'hjf) = toWord F[m - 1] := by
      have hws' : ws = ([w0.CT, w0.SH, w0.AT, w0.LL] ++ w0.SG) ++ (w0.FA ++ (w0.CO ++ w0.LV ++ w0.OU)) := by
        simp [ws, SW.ws]
      have : L[4 + w0.SG.length + (m - 1)]? = w0.FA[m - 1]? := by
        simp only [L]
        rw [List.getElem?_append_left (by omega), hws', List.getElem?_append_right (by simp; omega),
          List.getElem?_append_left (by simp; omega)]
        congr 1; simp; omega
      rw [hFAw] at this
      simp only [List.getElem?_map, List.getElem?_eq_getElem hF1, Option.map_some] at this
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
    refine ⟨1, 4 + w0.SG.length + (m - 1), by omega, hjf, ?_, ?_, ?_⟩
    · rw [hS5 "os" (by simp [hdC2])]; simp [fS]
    · rw [hS5 "of" (by simp [hdC2])]; simp [fS]; omega
    · rw [realQ_compose, h1, h2]
  · rw [hS5 "qk" (by simp [hdC2])]; simp [fS, kindOf]
  · intro p hp; simp [psComp] at hp; rcases hp with rfl | rfl | rfl <;> simp [hLl] <;> omega
  · rw [hS5 "Nt" (by simp [hdC2])]; simp [fS, tagOf_dn]
  · rw [hS5 "Nw" (by simp [hdC2])]; simp [fS, winOf_dn]
  · have hsw := sw_compose (d := d) (i := i) hm2 (by omega)
    rw [scW_dn, hsw]
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega); have h5 := g 5 (by omega)
    have h6 := g 6 (by omega); have h7 := g 7 (by omega); have h8 := g 8 (by omega)
    simp only [scR, scW_dn, List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp only [hsV, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      hS5 "Nph" (by simp [hdC2]), hS5 "Nd" (by simp [hdC2]), hS5 "Ni" (by simp [hdC2]), hS5 "Nm" (by simp [hdC2]),
      hS5 "NSG" (by simp [hdC2]), hS5 "NFA" (by simp [hdC2]), hS5 "NCO" (by simp [hdC2]),
      hS5 "NLV" (by simp [hdC2])]
    simp [fS, w0]
  · rw [hS5 "po" (by simp [hdC2])]; simp [fS]
  · rw [fr5 "nx" (by decide) (by decide) (by decide) (by decide)]
  · rw [fr5 "mw" (by decide) (by decide) (by decide) (by decide)]
  · rw [o5, o4, o3, o2]; simp [τ1, P0.hout]

/-- **The plan after a composition gives the state of the next position.** -/
theorem case_comp {d i m : ℕ} (hm2 : 2 ≤ m)
    (hr : m - 2 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    planW ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [[], toWord (coOf G (shOf G (itm G P Q s k₀ q₀ d i).2)
        ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2)[m - 2]))])
      (psComp (swAt G P Q s k₀ q₀ (.dn d i m)).ws.length
        (4 + (swAt G P Q s k₀ q₀ (.dn d i m)).SG.length + (swAt G P Q s k₀ q₀ (.dn d i m)).FA.length +
          (swAt G P Q s k₀ q₀ (.dn d i m)).CO.length) (swAt G P Q s k₀ q₀ (.dn d i m)).LV.length) =
      (swAt G P Q s k₀ q₀ (.dn d i (m + 1))).ws := by
  rw [planW_comp _ _ (OU_dn G P Q s k₀ q₀ d i m), sw_compose hm2 hr]

end Lax185574Proofs.ResolveRam.Glue
