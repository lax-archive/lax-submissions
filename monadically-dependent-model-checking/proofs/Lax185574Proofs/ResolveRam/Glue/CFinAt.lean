import Lax185574Proofs.ResolveRam.Glue.CaseKit

/-!
The query of the atom words of an item, appended to the word library.

`atT atC` checks the room, runs the piece `atC` of the atom words on the
item word `ow` (with the color table at `oc`), checks the room again and
appends the word that the piece wrote to the library, at the index
`oe` (`atT_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The query of the atom words. -/
def atT (atC : Com) : Com :=
  .seq (asgs [("po", .lit 0), ("oc", .lit 0)]) (.seq rmLs (gate (.seq atC (.seq rmLs (gate
    (.seq (asgs [("ls", .lit 0), ("lL", .var "po"), ("oe", .var "m")]) (.seq (lbApp "OB")
      (.assign "po" (.lit 0)))))))))

/-- The scalars that the rounds keep through a piece. -/
def atKeep : List String :=
  ["W", "rR", "z0", "bl", "gX", "nx", "mw", "ovf", "m", "lt", "m0", "e0", "iL", "ne", "ow", "ii", "dd",
    "gP", "gQ", "gS", "gK", "gq", "nSG", "nFA", "nCO", "nLV", "Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG",
    "NFA", "NCO", "NLV", "qk", "ox", "oL", "lvN", "lvL", "lvZ", "np", "gn", "ph", "mm"]

/-- The scalars that `atT` may write besides those of the piece. -/
def atTV : List String := ["po", "oc", "ls", "lL", "oe", "ci", "lt", "m"] ++ rmLs.wvars

/-- The word of the atom words of a tree. -/
def atQW (CT : List ℕ) (P Q sg : ℕ) (σ : TypeTree) : List ℕ :=
  toWord ((candW σ.k σ.q σ.ℓ (ctCols CT)).filter (newAtomW (dwOf P Q sg CT) (listWords (toWord σ) 3)))

/-- The cost of `atT`. -/
def kAtT (L : List (List ℕ)) (b w : List ℕ) (KA : ℕ) : ℕ :=
  2 * (30 * total L + 30 * b.length + 500) + KA + 18 * w.length + 200

theorem ell_mem_item {p g : ℕ} {σ : TypeTree} : σ.ℓ ∈ itemW ((p, g), σ) := by
  simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]

set_option maxHeartbeats 3200000 in
/-- **The query of the atom words.** -/
theorem atT_run {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) :
    ∃ cA aA : ℕ, ∀ {W R iw p g P Q sg : ℕ} {σ : TypeTree} {L : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ)
    (hL : Lib L τ) (hrR : τ.vars "rR" = min R W) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length)
    (hy : SegAt "y" 0 b τ) (hov : τ.vars "ovf" = 0) (how : τ.vars "ow" = iw) (hiw : iw < L.length)
    (h0 : 0 < L.length) (hitem : L[iw] = itemW ((p, g), σ)) (hct : IsCT L[0]) (hgP : τ.vars "gP" = P)
    (hgQ : τ.vars "gQ" = Q) (hgS : τ.vars "gS" = sg) (hsg : sg ≤ 1) (hRk : rhoPlus σ.k σ.q + 1 ≤ R),
    ∃ τ' K, Run (W + 1) (atT atC) τ τ' K ∧
      K ≤ kAtT L b (atQW L[0] P Q sg σ) (cA * (L[0].length + 1) * (L[iw].length + σ.ℓ + rhoPlus σ.k σ.q + 1) ^ aA) ∧
      (τ'.vars "ovf" = 0 → Lib (L ++ [atQW L[0] P Q sg σ]) τ' ∧ τ'.vars "oe" = L.length ∧
        τ'.vars "po" = 0) ∧
      (∀ y, y ∉ atTV → y ∉ atV → τ'.vars y = τ.vars y) ∧ τ'.arrs "y" = τ.arrs "y" ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp ∧
      (∀ Lb : List (List ℕ), (L ++ [atQW L[0] P Q sg σ]).Sublist Lb →
        BigRoom W R Lb b (τ.vars "nx") (τ.vars "mw") → τ'.vars "ovf" = 0) := by
  obtain ⟨cA, aA, hA⟩ := hAt
  refine ⟨cA, aA, ?_⟩
  intro W R iw p g P Q sg σ L b τ hW hW24 har hlt hL hrR hz hbl hy hov how hiw h0 hitem hct hgP hgQ hgS hsg hRk
  set AQ := atQW L[0] P Q sg σ with hAQ
  have hR1 : 1 ≤ R := by omega
  -- step 1
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ)
    (l := [("po", .lit 0), ("oc", .lit 0)]) (f := fun _ => 0)
    (by
      intro pr hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> exact evalB_lit (by omega))
    (by decide)
  have v1 : ∀ y, y ≠ "po" → y ≠ "oc" → τ1.vars y = τ.vars y := fun y h1 h2 => g1 y (by simp [h1, h2])
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  have ar1 : ArrW W τ1 := fun b' => by rw [a1]; exact har b'
  have L1 : Lib L τ1 := hL.of (by rw [v1 "m" (by decide) (by decide)]) (by rw [v1 "lt" (by decide) (by decide)])
    (by rw [a1]) (by rw [a1]) (by rw [a1])
  have hpo1 : τ1.vars "po" = 0 := by rw [s1 "po" (by simp)]
  -- step 2: the room check
  obtain ⟨τ2, r2, ov2, f2, a2, u2, i2⟩ := rmLs_run (R := R) (ws := L) (b := b) (τ := τ1)
    (by rw [v1 "W" (by decide) (by decide), hW]) hW24 (by rw [v1 "rR" (by decide) (by decide), hrR]) L1
    (by rw [v1 "z0" (by decide) (by decide), hz]) (by rw [v1 "bl" (by decide) (by decide), hbl])
    (fun j hj => by rw [a1]; exact hy j hj) ar1 hl1
  rw [v1 "ovf" (by decide) (by decide), hov] at ov2
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have hnx1 : τ1.vars "nx" = τ.vars "nx" := v1 "nx" (by decide) (by decide)
  have hmw1 : τ1.vars "mw" = τ.vars "mw" := v1 "mw" (by decide) (by decide)
  have frT : ∀ y, y ∉ atTV → y ≠ "po" ∧ y ≠ "oc" ∧ y ∉ rmLs.wvars := by
    intro y hy
    simp only [atTV, List.mem_append, not_or] at hy
    exact ⟨fun h => hy.1 (by simp [h]), fun h => hy.1 (by simp [h]), hy.2⟩
  by_cases hr2 : RoomOK W R τ1 L b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ1 L b * sOfV τ1 L b < W from hr2)] at ov2
    have hrun : Run (W + 1) (atT atC) τ τ2 _ :=
      Run.seq r1 (Run.seq r2 (gate_skip (by rw [ov2]; omega) (by rw [ov2]; omega)))
    refine ⟨τ2, _, hrun, ?_, fun h => by rw [ov2] at h; omega, fun y hy _ => ?_, by rw [a2, a1],
      fun b' => by rw [a2]; exact ar1 b', hl2, by rw [u2, o1], by rw [i2, i1],
      fun Lb hsub hB => absurd (roomOK_of_big ((List.sublist_append_left _ _).trans hsub)
        (by rw [hpo1]; omega) (by rw [hnx1, hmw1]; exact hB)) hr2⟩
    · simp only [asgK, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      unfold kAtT; omega
    · obtain ⟨a, b1, c⟩ := frT y hy
      rw [f2 y c, v1 y a b1]
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ1 L b * sOfV τ1 L b < W from hr2)] at ov2
  obtain ⟨hT1, hT2, hT3, hT4⟩ := sOfV_ge (τ := τ1) (ws := L) (b := b)
  have hS2 := room_bound hr2 hR1
  -- step 3: the piece
  have hℓ : σ.ℓ ≤ maxEntry L.flatten := by
    have hm : σ.ℓ ∈ L[iw] := by rw [hitem]; exact ell_mem_item
    exact le_maxEntry (List.mem_flatten.2 ⟨_, List.getElem_mem _, hm⟩)
  have hroom : Room W (rhoPlus σ.k σ.q) (ySz (toWord L) + ([] : List ℕ).length + σ.ℓ) := by
    refine room_of_ok hr2 hRk ?_
    have := ySz_toWord_le L
    simp only [List.length_nil]
    omega
  have hPW : P ≤ W := by rw [← hgP]; have := hlt.vars "gP"; omega
  have hQW : Q ≤ W := by rw [← hgQ]; have := hlt.vars "gQ"; omega
  have v2 : ∀ y, y ∉ rmLs.wvars → y ≠ "po" → y ≠ "oc" → τ2.vars y = τ.vars y := fun y h0 h1 h2 => by
    rw [f2 y h0, v1 y h1 h2]
  obtain ⟨τ3, r3, F3, P3⟩ := hA W τ2 L [] 0 iw P Q sg p g σ h0 hiw
    (by rw [v2 "W" (by decide) (by decide) (by decide), hW]) (fun b' => by rw [a2]; exact ar1 b')
    (L1.at_.of_arrs (by rw [a2]) (by rw [a2]) (by rw [a2]))
    (by rw [f2 "oc" (by decide), s1 "oc" (by simp)]) (by rw [v2 "ow" (by decide) (by decide) (by decide), how])
    (by rw [v2 "gP" (by decide) (by decide) (by decide), hgP]) (by rw [v2 "gQ" (by decide) (by decide) (by decide), hgQ])
    hPW hQW (by rw [v2 "gS" (by decide) (by decide) (by decide), hgS]) hsg hct hitem
    ⟨by rw [f2 "po" (by decide), hpo1]; rfl, fun j hj => absurd hj (by simp)⟩ hroom
  simp only [List.nil_append] at F3
  change Filled "OB" "po" AQ τ3 at F3
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have ar3 : ArrW W τ3 := fun b' => by rw [P3.len, a2]; exact ar1 b'
  have v3 : ∀ y, y ∉ atV → y ∉ rmLs.wvars → y ≠ "po" → y ≠ "oc" → τ3.vars y = τ.vars y :=
    fun y h h0 h1 h2 => by rw [P3.vars y h, v2 y h0 h1 h2]
  have ha3 : ∀ b', b' ∈ keepA → τ3.arrs b' = τ.arrs b' := fun b' hb => by rw [P3.arrs b' hb, a2, a1]
  have kp : ∀ y ∈ ["W", "rR", "z0", "bl", "m", "lt", "nx", "mw", "ovf"], y ∉ atV :=
    fun y hy => hAV y (by simp at hy; rcases hy with h | h | h | h | h | h | h | h | h <;> simp [atKeep, h])
  have L3 : Lib L τ3 := hL.of (by rw [v3 "m" (kp "m" (by simp)) (by decide) (by decide) (by decide)])
    (by rw [v3 "lt" (kp "lt" (by simp)) (by decide) (by decide) (by decide)])
    (ha3 "a" (by decide)) (ha3 "st" (by decide)) (ha3 "ln" (by decide))
  -- step 4: the second room check
  obtain ⟨τ4, r4, ov4, f4, a4, u4, i4⟩ := rmLs_run (R := R) (ws := L) (b := b) (τ := τ3)
    (by rw [v3 "W" (kp "W" (by simp)) (by decide) (by decide) (by decide), hW]) hW24
    (by rw [v3 "rR" (kp "rR" (by simp)) (by decide) (by decide) (by decide), hrR]) L3
    (by rw [v3 "z0" (kp "z0" (by simp)) (by decide) (by decide) (by decide), hz])
    (by rw [v3 "bl" (kp "bl" (by simp)) (by decide) (by decide) (by decide), hbl])
    (fun j hj => by rw [ha3 "y" (by decide)]; exact hy j hj) ar3 hl3
  rw [P3.vars "ovf" (kp "ovf" (by simp)), ov2] at ov4
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have hpo3 : τ3.vars "po" = AQ.length := F3.pos
  have hnx3 : τ3.vars "nx" = τ.vars "nx" := v3 "nx" (kp "nx" (by simp)) (by decide) (by decide) (by decide)
  have hmw3 : τ3.vars "mw" = τ.vars "mw" := v3 "mw" (kp "mw" (by simp)) (by decide) (by decide) (by decide)
  by_cases hr4 : RoomOK W R τ3 L b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ3 L b * sOfV τ3 L b < W from hr4)] at ov4
    have hrun : Run (W + 1) (atT atC) τ τ4 _ :=
      Run.seq r1 (Run.seq r2 (gate_run ov2 (by omega) (Run.seq r3 (Run.seq r4
        (gate_skip (by rw [ov4]; omega) (by rw [ov4]; omega))))))
    refine ⟨τ4, _, hrun, ?_, fun h => by rw [ov4] at h; omega, fun y hy hy' => ?_,
      by rw [a4]; exact ha3 "y" (by decide), fun b' => by rw [a4]; exact ar3 b', hl4,
      by rw [u4, P3.out, u2, o1], by rw [i4, P3.inp, i2, i1],
      fun Lb hsub hB => absurd (roomOK_of_big ((List.sublist_append_left _ _).trans hsub) ?_
        (by rw [hnx3, hmw3]; exact hB)) hr4⟩
    · simp only [asgK, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Cond.size]
      unfold kAtT; omega
    · obtain ⟨a, b1, c⟩ := frT y hy
      rw [f4 y c, v3 y hy' c a b1]
    · rw [hpo3]
      have h1 := total_le_of_sub hsub
      simp only [total_append, total_single] at h1
      omega
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ3 L b * sOfV τ3 L b < W from hr4)] at ov4
  obtain ⟨hU1, hU2, hU3, hU4⟩ := sOfV_ge (τ := τ3) (ws := L) (b := b)
  rw [hpo3] at hU1
  have hS4 := room_bound hr4 hR1
  have ar4 : ArrW W τ4 := fun b' => by rw [a4]; exact ar3 b'
  have L4 : Lib L τ4 := L3.of (by rw [f4 "m" (by decide)]) (by rw [f4 "lt" (by decide)]) (by rw [a4])
    (by rw [a4]) (by rw [a4])
  -- step 5: the copy
  have hpo4 : τ4.vars "po" = AQ.length := by rw [f4 "po" (by decide), hpo3]
  have hm4 : τ4.vars "m" = L.length := L4.m
  have hl4' := hl4
  obtain ⟨τ5, r5, s5, g5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4)
    (l := [("ls", .lit 0), ("lL", .var "po"), ("oe", .var "m")])
    (f := fun y => if y = "ls" then 0 else if y = "lL" then AQ.length else L.length)
    (by
      intro pr hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simp
      · simp only [show ("lL" : String) ≠ "ls" by decide, if_false, if_true]
        exact ev_var hpo4 (by omega)
      · simp only [show ("oe" : String) ≠ "ls" by decide, show ("oe" : String) ≠ "lL" by decide, if_false]
        exact ev_var hm4 (by omega))
    (by decide)
  have L5 : Lib L τ5 := L4.of (by rw [g5 "m" (by decide)]) (by rw [g5 "lt" (by decide)]) (by rw [a5])
    (by rw [a5]) (by rw [a5])
  have hseg : SegAt "OB" 0 AQ τ5 := fun j hj => by
    rw [a5, a4, Nat.zero_add]; exact F3.get j hj
  have hAv : ∀ v ∈ AQ, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := hl3.arrs "OB" _ (List.mem_of_getElem? (F3.get j hj))
    omega
  have hAr : ∀ b', (τ5.arrs b').length = W + 1 := fun b' => by rw [a5]; exact ar4 b'
  obtain ⟨τ6, r6, L6, f6, a6, l6, o6, i6⟩ := lbApp_run (W := W) (src := "OB") (s := 0) L5
    (by rw [s5 "ls" (by simp)]; simp) (by rw [s5 "lL" (by simp)]; simp) hseg (by decide) (by simp)
    (by rw [hAr]; omega) (by rw [hAr]; omega) (by rw [hAr]; omega) (by omega) (by omega) hAv
  set τ7 := τ6.setVar "po" 0
  have r7 : Run (W + 1) (.assign "po" (.lit 0)) τ6 τ7 2 := Run.assign (evalB_lit (by omega))
  have hrun : Run (W + 1) (atT atC) τ τ7 _ :=
    Run.seq r1 (Run.seq r2 (gate_run ov2 (by omega) (Run.seq r3 (Run.seq r4
      (gate_run ov4 (by omega) (Run.seq r5 (Run.seq r6 r7)))))))
  refine ⟨τ7, _, hrun, ?_, fun _ => ⟨L6.of (by simp [τ7]) (by simp [τ7]) rfl rfl rfl, ?_, by simp [τ7]⟩,
    fun y hy hy' => ?_, ?_, fun b' => by simp only [τ7, arrs_setVar]; rw [l6]; exact hAr b', Run.envLt hrun hlt, ?_, ?_,
    fun _ _ _ => ?_⟩
  · simp only [asgK, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Cond.size]
    unfold kAtT; omega
  · simp only [τ7]; rw [vars_setVar, if_neg (by decide : ¬ ("oe" = "po")), f6 "oe" (by decide), s5 "oe" (by simp)]; simp
  · obtain ⟨a, b1, c⟩ := frT y hy
    have hy2 : y ∉ ["ls", "lL", "oe", "ci", "lt", "m"] := fun h => hy (by simp [atTV] at h ⊢; tauto)
    simp only [τ7]
    rw [vars_setVar, if_neg a, f6 y (by simp at hy2 ⊢; tauto), g5 y (by simp at hy2 ⊢; tauto), f4 y c,
      v3 y hy' c a b1]
  · simp only [τ7, arrs_setVar]; rw [a6 "y" (by decide), a5, a4]; exact ha3 "y" (by decide)
  · simp only [τ7, out_setVar]; rw [o6, o5, u4, P3.out, u2, o1]
  · simp only [τ7, inp_setVar]; rw [i6, i5, i4, P3.inp, i2, i1]
  · simp only [τ7]
    rw [vars_setVar, if_neg (by decide : ¬ ("ovf" = "po")), f6 "ovf" (by decide), g5 "ovf" (by decide), ov4]

end Lax185574Proofs.ResolveRam.Glue
