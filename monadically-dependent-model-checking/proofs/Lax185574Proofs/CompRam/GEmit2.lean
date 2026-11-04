import Lax185574Proofs.CompRam.GBase

/-!
Two writers of the glue command of lem:compose: the query of a
restriction (`emRe`) and the word of the atoms of a new frame
(`emAtoms`).

`emRe` writes `[|w|, |dSq|, 1] ++ w ++ [0]` for the word
`w = [kk + 1, d - 1, l1 + 1 + l2] ++ R ++ (l1 + l2 + 1) :: J` of the
restriction, where `J` lists the values of `moveLast l1 l2` and the
length `|w|` is filled in after `w` is written. `emAtoms` writes the
word of the atoms of the first node followed by those of the second
node, with the positions of the second moved behind the first tuple
(`renAtom`). The atoms of the first node are one segment of `x`, those
of the second are copied entry by entry.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574Proofs.TreeAlgo

/-! ### Small tools -/

private theorem ofr_run {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) {xs : List String}
    (hw : c.wvars ⊆ xs) (ha : ∀ a ∈ c.warrs, a = "OB") (ho : c.NoWrite) (hr : ¬ c.reads) :
    OFr σ σ' xs :=
  ⟨fun y hy => h.frame_var_sub y hw hy, fun b hb => h.frame_arr b (fun hm => hb (ha b hm)),
    run_length_arrs h "OB", h.out_eq ho, h.frame_inp hr⟩

private theorem xg_get {X : List ℕ} {i : ℕ} (h : i < X.length) : X[i]? = some (xg X i) := by
  simp [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem length_frames_ge (ws : List (List ℕ)) : ws.length ≤ (frames ws).length := by
  induction ws with
  | nil => simp [frames]
  | cons u ws ih => simp only [frames, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at ih ⊢; omega

private theorem pv_run {W M : ℕ} {σ : Env} {pre : List ℕ} {e : Expr} {v : ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (he : e.evalB (W + 1) σ = some v) (hB : pre.length + 1 ≤ W) :
    ∃ σ', Run (W + 1) (pv e) σ σ' (6 + e.size) ∧ Filled "OB" "po" (pre ++ [v]) σ' ∧
      OFr σ σ' ["po"] :=
  push1_ofr hF he (by rw [hC.ol]; omega) hB

private theorem emSeg_run {W M : ℕ} {σ : Env} {pre w : List ℕ} {s l : String} (hs : s ∉ ["po", "ci"])
    (hl : l ∉ ["po", "ci"]) (hC : Ctx W M σ) (hF : Filled "OB" "po" pre σ) (hseg : SegIs M σ s l w)
    (hpre : pre.length + M ≤ W) :
    ∃ σ', Run (W + 1) (emSeg s l) σ σ' (20 * w.length + 6) ∧ Filled "OB" "po" (pre ++ w) σ' ∧
      OFr σ σ' ["ci", "po"] := by
  obtain ⟨h1, h2, h3⟩ := hseg
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs hl
  have hM := hC.room
  obtain ⟨σ', r, F, O⟩ := cpSeg_ofr (W := W) (src := "x") (by decide) rfl h1 hs.1 hs.2 hl.1 hl.2 hF
    (by rw [hC.xl]; omega) (by rw [hC.ol]; omega) (by omega) (by omega)
    (fun v hv => by have := hC.xv v (mem_seg hv); omega)
  rw [h3] at F
  exact ⟨σ', r.mono (by omega), F, O⟩

/-! ### Moving through frames -/

private theorem skipK_run' {W M : ℕ} {σ : Env} {k : String} (hk : k ∉ ["y", "sk"]) (hC : Ctx W M σ) {f : ℕ}
    {ws : List (List ℕ)} {r : List ℕ} (hx : (σ.arrs "x").drop f = frames ws ++ r) (hy : σ.vars "y" = f)
    (hK : σ.vars k ≤ ws.length) (hf : f + (frames ws).length ≤ M) :
    ∃ σ', Run (W + 1) (skipK k) σ σ' (20 * σ.vars k + 10) ∧
      σ'.vars "y" = skipFr (σ.arrs "x") f (σ.vars k) ∧ OFr σ σ' ["y", "sk"] := by
  set Xa := σ.arrs "x" with hX
  set n := σ.vars k with hn
  have hM := hC.room
  have hfr := length_frames_ge ws
  have hXl : Xa.length = W + 1 := hC.xl
  let I : ℕ → Env → Prop := fun j τ => τ.vars "y" = skipFr Xa f j ∧ OFr σ τ ["y", "sk"]
  obtain ⟨σ', r, ⟨hy', O⟩, -⟩ := forUp_run (B := W + 1) (i := "sk") (e := V k) (body := stepY) (N := n)
    (K := 7) I (by omega)
    (fun j _ τ hI _ => by
      rw [show n = τ.vars k from (hI.2.vars k hk).symm]
      exact evalB_var (by rw [hI.2.vars k hk]; omega))
    ⟨by simp [skipFr, hy], OFr.setVar σ "sk" 0 |>.mono (by simp)⟩
    (fun j hj τ hI hj' => by
      obtain ⟨hyj, O⟩ := hI
      obtain ⟨e1, e2⟩ := skipFr_frames hx (j := j) (by omega)
      obtain ⟨e3, -⟩ := skipFr_frames hx (j := j + 1) (by omega)
      have hlt : skipFr Xa f j < Xa.length := by
        have := length_frames_take_le ws j; have := length_frames_take_le ws (j + 1)
        have : (frames (ws.take j)).length < (frames (ws.take (j + 1))).length := by
          rw [length_frames_take_succ (by omega)]; omega
        omega
      have hxa : τ.arrs "x" = Xa := O.arrs "x" (by decide)
      have hsucc := skipFr_succ' Xa f j
      have hle : skipFr Xa f (j + 1) ≤ M := by
        have := length_frames_take_le ws (j + 1); omega
      refine ⟨τ.setVar "y" (skipFr Xa f (j + 1)), (Run.assign ?_).mono le_rfl, by simp [hj'],
        by simp, (O.trans (OFr.setVar τ "y" _)).trans (OFr.setVar _ "sk" _) |>.mono (by simp)⟩
      have hv : xg Xa (skipFr Xa f j) < M := hC.xv _ (List.mem_of_getElem? (xg_get hlt))
      have e0 : (V "y").evalB (W + 1) τ = some (skipFr Xa f j) := by
        rw [← hyj]; exact evalB_var (by omega)
      have e1' : (X (V "y")).evalB (W + 1) τ = some (xg Xa (skipFr Xa f j)) :=
        evalB_get e0 (by rw [hxa]; exact xg_get hlt) (by omega)
      have e2' := evalB_bin (op := .add) e0 e1' (by simp only [Bop.apply_add]; omega)
      have e3' := evalB_bin (op := .add) e2' (evalB_lit (B := W + 1) (n := 1) (σ := τ) (by omega))
        (by simp only [Bop.apply_add]; omega)
      simp only [Bop.apply_add] at e3'
      rw [hsucc, show skipFr Xa f j + 1 + xg Xa (skipFr Xa f j) =
        skipFr Xa f j + xg Xa (skipFr Xa f j) + 1 by omega]
      exact e3')
  refine ⟨σ', r.mono (by simp [Expr.size]; omega), hy', O⟩

private theorem skipL_run' {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : (σ.arrs "x").drop p = toWord ws ++ r) (hy : σ.vars "y" = p) (hp : p + (toWord ws).length ≤ M) :
    ∃ σ', Run (W + 1) skipL σ σ' (20 * ws.length + 30) ∧ σ'.vars "y" = p + (toWord ws).length ∧
      OFr σ σ' ["y", "sn", "sk"] := by
  set Xa := σ.arrs "x" with hX
  have hM := hC.room
  rw [toWord_words] at hx hp
  have hfr := length_frames_ge ws
  simp only [List.length_cons] at hp
  have hpl : p < Xa.length := by rw [hC.xl]; omega
  have hxp : xg Xa p = ws.length := xg_of_drop (by rw [hx]; rfl)
  have hx1 : Xa.drop (p + 1) = frames ws ++ r := by
    have := drop_add_of_drop (u := [ws.length]) (r := frames ws ++ r) (by rw [hx]; rfl)
    simpa using this
  have r1 : Run (W + 1) (asg "sn" (X (V "y"))) σ (σ.setVar "sn" ws.length) 3 :=
    (Run.assign (evalB_get (evalB_var (σ := σ) (x := "y") (by rw [hy]; omega))
      (by rw [hy, ← hxp]; exact xg_get hpl) (by omega))).mono (by simp)
  have r2 : Run (W + 1) (asg "y" (.add (V "y") (N 1))) (σ.setVar "sn" ws.length)
      ((σ.setVar "sn" ws.length).setVar "y" (p + 1)) 4 := by
    have h := evalB_bin (op := .add) (evalB_var (B := W + 1) (σ := σ.setVar "sn" ws.length) (x := "y")
      (by simp [hy]; omega)) (evalB_lit (B := W + 1) (n := 1) (σ := σ.setVar "sn" ws.length) (by omega))
      (by simp [hy]; omega)
    simp only [vars_setVar, Bop.apply_add, hy] at h
    exact (Run.assign (x := "y") h).mono (by simp)
  have hC2 : Ctx W M ((σ.setVar "sn" ws.length).setVar "y" (p + 1)) :=
    (hC.setVar (by decide) _).setVar (by decide) _
  obtain ⟨σ3, r3, hy3, O3⟩ := skipK_run' (k := "sn") (by decide) hC2 (f := p + 1) (ws := ws) (r := r)
    (by simpa using hx1) (by simp) (by simp) (by omega)
  obtain ⟨e1, -⟩ := skipFr_frames hx1 (j := ws.length) le_rfl
  refine ⟨σ3, (Run.seq r1 (Run.seq r2 r3)).mono ?_, ?_, ?_⟩
  · simp; omega
  · rw [hy3]; simp only [arrs_setVar, vars_setVar, if_true,
      show ("sn" = "y") = False by decide, if_false]
    rw [← hX, e1, List.take_length, toWord_words]; simp; omega
  · exact ((OFr.setVar σ "sn" _).trans (OFr.setVar _ "y" _)).trans O3 |>.mono (by simp)

/-! ### The query of a restriction -/

/-- Entry `k` of the positions of a restriction. -/
def jv (p1 p2 k : ℕ) : ℕ := if k < p1 then k else if k < p1 + p2 then k + 1 else p1

private theorem flatMap_single_eq_map (L : List ℕ) (f : ℕ → ℕ) : (L.flatMap fun k => [f k]) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem jList_eq (p1 p2 : ℕ) :
    jList p1 p2 = (List.range (p1 + p2 + 1)).flatMap fun k => [jv p1 p2 k] := by
  rw [flatMap_single_eq_map]
  apply List.ext_getElem
  · simp [jList]
  · intro i h1 h2
    have h3 : i < p1 + p2 + 1 := by simpa using h2
    simp only [jList, List.getElem_map, List.getElem_ofFn, List.getElem_range, moveLast, jv]
    split_ifs <;> omega

theorem jEnt_run {W M : ℕ} {τ : Env} {l : List ℕ} (hC : Ctx W M τ) (hF : Filled "OB" "po" l τ)
    (hp : τ.vars "p1" + τ.vars "p2" < M) (hk : τ.vars "fk" ≤ τ.vars "p1" + τ.vars "p2")
    (hl : l.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) jEnt τ τ' 20 ∧
      Filled "OB" "po" (l ++ [jv (τ.vars "p1") (τ.vars "p2") (τ.vars "fk")]) τ' ∧ OFr τ τ' ["po"] := by
  have hM := hC.room
  have ek : (V "fk").evalB (W + 1) τ = some (τ.vars "fk") := evalB_var (by omega)
  have e1 : (V "p1").evalB (W + 1) τ = some (τ.vars "p1") := evalB_var (by omega)
  have e2 : (V "p2").evalB (W + 1) τ = some (τ.vars "p2") := evalB_var (by omega)
  have e12 : (Expr.add (V "p1") (V "p2")).evalB (W + 1) τ = some (τ.vars "p1" + τ.vars "p2") :=
    evalB_bin e1 e2 (by simp only [Bop.apply_add]; omega)
  by_cases h1 : τ.vars "fk" < τ.vars "p1"
  · obtain ⟨τ', r, F, O⟩ := pv_run hC hF ek hl
    refine ⟨τ', (Run.ite_true (by rw [evalB_condLt ek e1]; simpa using h1) r).mono (by simp), ?_, O⟩
    simpa [jv, h1] using F
  by_cases h2 : τ.vars "fk" < τ.vars "p1" + τ.vars "p2"
  · obtain ⟨τ', r, F, O⟩ := pv_run hC hF (evalB_bin (op := .add) ek (evalB_lit (B := W + 1) (n := 1)
      (σ := τ) (by omega)) (by simp only [Bop.apply_add]; omega)) hl
    refine ⟨τ', (Run.ite_false (by rw [evalB_condLt ek e1]; simpa using h1)
      (Run.ite_true (by rw [evalB_condLt ek e12]; simpa using h2) r)).mono (by simp), ?_, O⟩
    simpa [jv, h1, h2] using F
  · obtain ⟨τ', r, F, O⟩ := pv_run hC hF e1 hl
    refine ⟨τ', (Run.ite_false (by rw [evalB_condLt ek e1]; simpa using h1)
      (Run.ite_false (by rw [evalB_condLt ek e12]; simpa using h2) r)).mono (by simp), ?_, O⟩
    simpa [jv, h1, h2] using F

private theorem set_append_cons (pre t : List ℕ) (a v : ℕ) : (pre ++ a :: t).set pre.length v = pre ++ v :: t := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [ih]

private theorem SegIs.of_ofr {M : ℕ} {σ τ : Env} {s l : String} {w : List ℕ} {xs : List String}
    (h : SegIs M σ s l w) (O : OFr σ τ xs) (hs : s ∉ xs) (hl : l ∉ xs) : SegIs M τ s l w := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [O.vars l hl, h1], by rw [O.vars s hs]; exact h2, ?_⟩
  rw [O.vars s hs, O.arrs "x" (by decide), h3]

theorem emRe_run {W M : ℕ} {σ : Env} {pre R1 R2 : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hk : σ.vars "pk" < M) (hd : σ.vars "pd" < M)
    (hl : σ.vars "p1" + σ.vars "p2" < M) (h1 : SegIs M σ "r1s" "r1l" R1)
    (h2 : SegIs M σ "r2s" "r2l" R2) (hpre : pre.length + 8 * M ≤ W) :
    ∃ σ', Run (W + 1) emRe σ σ'
        (40 * (R1.length + R2.length + σ.vars "p1" + σ.vars "p2") + 400) ∧
      Filled "OB" "po" (pre ++ [(reW (σ.vars "pk") (σ.vars "pd") (σ.vars "p1") (σ.vars "p2")
        (R1 ++ R2)).length, lDSq, 1] ++ reW (σ.vars "pk") (σ.vars "pd") (σ.vars "p1") (σ.vars "p2")
        (R1 ++ R2) ++ [0]) σ' ∧
      σ'.vars "qa" = pre.length + 3 ∧
      σ'.vars "ql" = (reW (σ.vars "pk") (σ.vars "pd") (σ.vars "p1") (σ.vars "p2") (R1 ++ R2)).length ∧
      σ'.vars "sp" = pre.length + 3 +
        (reW (σ.vars "pk") (σ.vars "pd") (σ.vars "p1") (σ.vars "p2") (R1 ++ R2)).length ∧
      σ'.vars "dq" = 1 ∧ σ'.vars "qk" = 0 ∧
      OFr σ σ' ["ci", "po", "fk", "qa", "ql", "sp", "dq", "qk"] := by
  have hM := hC.room
  have h16 := hC.m16
  obtain ⟨K, hK⟩ : ∃ K, σ.vars "pk" = K := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, σ.vars "pd" = D := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, σ.vars "p1" = P := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, σ.vars "p2" = P := ⟨_, rfl⟩
  rw [hK, hD, hP1, hP2]
  rw [hK] at hk; rw [hD] at hd; rw [hP1, hP2] at hl
  have hR1 := h1.2.1
  have hR2 := h2.2.1
  -- the head
  obtain ⟨τ1, r1, F1, O1⟩ := pushLits_run (W := W) (l := [0, lDSq, 1]) hF
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> first | omega | (simp [lDSq]; omega))
    (by rw [hC.ol]; simp; omega) (by simp; omega)
  have p1 := F1.pos
  simp only [List.length_append, List.length_cons, List.length_nil] at p1
  have r2 := Run.assign (x := "qa") (evalB_var (B := W + 1) (σ := τ1) (x := "po") (by omega))
  have F2 := F1.setVar (y := "qa") (by decide) (τ1.vars "po")
  have O2 := O1.trans (OFr.setVar τ1 "qa" (τ1.vars "po"))
  set τ2 := τ1.setVar "qa" (τ1.vars "po") with hτ2
  have C2 := hC.ofr O2 (by decide)
  -- the numbers
  have e3 : (Expr.add (V "pk") (N 1)).evalB (W + 1) τ2 = some (K + 1) := by
    have := O2.vars "pk" (by decide); simp [this, hK]; omega
  obtain ⟨τ3, r3, F3, O3'⟩ := pv_run C2 F2 e3 (by simp; omega)
  have O3 := O2.trans O3'
  have C3 := hC.ofr O3 (by decide)
  have e4 : (Expr.sub (V "pd") (N 1)).evalB (W + 1) τ3 = some (D - 1) := by
    have := O3.vars "pd" (by decide); simp [this, hD]; omega
  obtain ⟨τ4, r4, F4, O4'⟩ := pv_run C3 F3 e4 (by simp; omega)
  have O4 := O3.trans O4'
  have C4 := hC.ofr O4 (by decide)
  have e5 : (Expr.add (.add (V "p1") (N 1)) (V "p2")).evalB (W + 1) τ4 = some (P1 + 1 + P2) := by
    have := O4.vars "p1" (by decide); have := O4.vars "p2" (by decide); simp [*]; omega
  obtain ⟨τ5, r5, F5, O5'⟩ := pv_run C4 F4 e5 (by simp; omega)
  have O5 := O4.trans O5'
  have C5 := hC.ofr O5 (by decide)
  -- the result
  obtain ⟨τ6, r6, F6, O6'⟩ := emSeg_run (by decide) (by decide) C5 F5
    (h1.of_ofr O5 (by decide) (by decide)) (by simp; omega)
  have O6 := O5.trans O6'
  have C6 := hC.ofr O6 (by decide)
  obtain ⟨τ7, r7, F7, O7'⟩ := emSeg_run (by decide) (by decide) C6 F6
    (h2.of_ofr O6 (by decide) (by decide)) (by simp; omega)
  have O7 := O6.trans O7'
  have C7 := hC.ofr O7 (by decide)
  have e8 : (Expr.add (.add (V "p1") (V "p2")) (N 1)).evalB (W + 1) τ7 = some (P1 + P2 + 1) := by
    have := O7.vars "p1" (by decide); have := O7.vars "p2" (by decide); simp [*]; omega
  obtain ⟨τ8, r8, F8, O8'⟩ := pv_run C7 F7 e8 (by simp; omega)
  have O8 := O7.trans O8'
  have C8 := hC.ofr O8 (by decide)
  -- the positions
  set l8 := pre ++ [0, lDSq, 1] ++ [K + 1] ++ [D - 1] ++ [P1 + 1 + P2] ++ R1 ++ R2 ++ [P1 + P2 + 1]
    with hl8
  have hl8len : l8.length = pre.length + 7 + R1.length + R2.length := by simp [hl8]; omega
  obtain ⟨τ9, r9, P9, -, F9⟩ := forUp_append (B := W + 1) (i := "fk")
    (e := .add (.add (V "p1") (V "p2")) (N 1)) (body := jEnt) (N := P1 + P2 + 1) (K := 20)
    (a := "OB") (pv := "po") (by decide) (fun k => [jv P1 P2 k])
    (fun τ => OFr τ8 τ ["po", "fk"]) (fun τ v hP => (hP.trans (OFr.setVar τ "fk" v)).mono (by simp))
    (by omega) (OFr.refl τ8 |>.mono (by simp)) F8
    (fun τ hP => by
      have := (O8.trans hP).vars "p1" (by decide); have := (O8.trans hP).vars "p2" (by decide)
      simp [*]; omega)
    (fun k hk τ hP hik hF' => by
      have Cτ := hC.ofr (O8.trans hP) (by decide)
      have v1 := (O8.trans hP).vars "p1" (by decide)
      have v2 := (O8.trans hP).vars "p2" (by decide)
      have hlen : (l8 ++ (List.range k).flatMap fun k => [jv P1 P2 k]).length = l8.length + k := by
        rw [List.length_append, length_flatMap_single]
      obtain ⟨τ', r, F', O'⟩ := jEnt_run Cτ hF' (by omega) (by omega) (by rw [hlen]; omega)
      refine ⟨τ', r, by rw [O'.vars "fk" (by decide), hik], (hP.trans O').mono (by simp), ?_⟩
      rw [v1, v2, hik, hP1, hP2] at F'
      rw [List.range_succ, List.flatMap_append, ← List.append_assoc]
      simpa using F')
  have O9 := O8.trans P9
  have C9 := hC.ofr O9 (by decide)
  set w := reW K D P1 P2 (R1 ++ R2) with hw
  have hl9 : l8 ++ (List.range (P1 + P2 + 1)).flatMap (fun k => [jv P1 P2 k]) =
      pre ++ [0, lDSq, 1] ++ w := by
    rw [hl8, hw, reW, jList_eq]; simp
  rw [hl9] at F9
  have hwlen : w.length = 3 + R1.length + R2.length + 1 + (P1 + P2 + 1) := by
    simp [hw, reW, jList]; omega
  have p9 := F9.pos
  simp only [List.length_append, List.length_cons, List.length_nil] at p9
  have qa9 : τ9.vars "qa" = pre.length + 3 := by
    rw [show τ9.vars "qa" = τ2.vars "qa" from ((O3'.trans O4').trans ((O5'.trans O6').trans
      ((O7'.trans O8').trans P9))).vars "qa" (by decide)]
    simp [hτ2]; omega
  -- the length of the word
  have e10 : (Expr.sub (V "po") (V "qa")).evalB (W + 1) τ9 = some w.length := by
    simp [p9, qa9]; omega
  have r10 := Run.assign (x := "ql") e10
  have F10 := F9.setVar (y := "ql") (by decide) w.length
  set τ10 := τ9.setVar "ql" w.length with hτ10
  obtain ⟨τ11, r11, F11, O11⟩ := store_filled (W := W) (ie := .sub (V "qa") (N 3)) (e := V "ql")
    (k := pre.length) (v := w.length) F10 (by simp [hτ10, qa9]; omega) (by simp [hτ10]; omega)
    (by simp)
  have hset : (pre ++ [0, lDSq, 1] ++ w).set pre.length w.length = pre ++ [w.length, lDSq, 1] ++ w := by
    rw [show pre ++ [0, lDSq, 1] ++ w = pre ++ 0 :: (lDSq :: 1 :: w) by simp, set_append_cons]; simp
  rw [hset] at F11
  have p11 := F11.pos
  simp only [List.length_append, List.length_cons, List.length_nil] at p11
  have r12 := Run.assign (x := "sp") (evalB_var (B := W + 1) (σ := τ11) (x := "po") (by omega))
  have F12 := F11.setVar (y := "sp") (by decide) (τ11.vars "po")
  set τ12 := τ11.setVar "sp" (τ11.vars "po") with hτ12
  have C12 : Ctx W M τ12 := (C9.setVar (by decide) _).of_frame (O11.vars "W" (by decide))
    (O11.arrs "x" (by decide)) (O11.arrs "wp" (by decide)) O11.len |>.setVar (by decide) _
  obtain ⟨τ13, r13, F13, O13⟩ := pv_run C12 F12 (e := N 0) (evalB_lit (by omega)) (by simp; omega)
  have r14 := Run.assign (x := "dq") (evalB_lit (B := W + 1) (n := 1) (σ := τ13) (by omega))
  set τ14 := τ13.setVar "dq" 1 with hτ14
  have r15 := Run.assign (x := "qk") (evalB_lit (B := W + 1) (n := 0) (σ := τ14) (by omega))
  have Ofin : OFr σ (τ14.setVar "qk" 0) ["ci", "po", "fk", "qa", "ql", "sp", "dq", "qk"] :=
    ((((O9.trans (OFr.setVar τ9 "ql" _)).trans O11).trans (OFr.setVar τ11 "sp" _)).trans
      ((O13.trans (OFr.setVar τ13 "dq" 1)).trans (OFr.setVar τ14 "qk" 0))).mono (by simp)
  refine ⟨τ14.setVar "qk" 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Ofin⟩
  · simp only [emRe, seqs]
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 (Run.seq r10 (Run.seq r11 (Run.seq r12 (Run.seq r13
      (Run.seq r14 r15)))))))))))))).mono ?_
    simp [Expr.size, pushLits]
    omega
  · exact (F13.setVar (by decide) _).setVar (by decide) _
  · have O' := (((OFr.setVar τ9 "ql" w.length).trans O11).trans (OFr.setVar τ11 "sp" _)).trans
      ((O13.trans (OFr.setVar τ13 "dq" 1)).trans (OFr.setVar τ14 "qk" 0))
    rw [O'.vars "qa" (by decide), qa9]
  · have O' := (OFr.setVar τ11 "sp" (τ11.vars "po")).trans
      ((O13.trans (OFr.setVar τ13 "dq" 1)).trans (OFr.setVar τ14 "qk" 0))
    rw [O'.vars "ql" (by decide), O11.vars "ql" (by simp)]; simp [hτ10]
  · have O' := (O13.trans (OFr.setVar τ13 "dq" 1)).trans (OFr.setVar τ14 "qk" 0)
    rw [O'.vars "sp" (by decide)]; simp [hτ12, p11]
  · simp [hτ14]
  · simp

/-! ### The atoms of a new frame -/

theorem posCmd_spec (W : ℕ) :
    Spec (W + 1) (fun ρ => ρ.vars "ft" ≤ W ∧ ρ.vars "fk" ≤ W ∧ 5 ≤ W) posCmd
      (fun ρ ρ' => ρ'.vars "fb" = if posB (ρ.vars "ft") (ρ.vars "fk") then 1 else 0) 30 := by
  unfold posCmd
  run_vcg <;> simp_all [posB] <;> omega

theorem posCmd_run {W : ℕ} {τ : Env} (hft : τ.vars "ft" ≤ W) (hfk : τ.vars "fk" ≤ W) (h5 : 5 ≤ W) :
    ∃ τ', Run (W + 1) posCmd τ τ' 30 ∧
      τ'.vars "fb" = (if posB (τ.vars "ft") (τ.vars "fk") then 1 else 0) ∧ OFr τ τ' ["fb"] := by
  obtain ⟨τ', r, h⟩ := (posCmd_spec W).run ⟨hft, hfk, h5⟩
  exact ⟨τ', r, h, ofr_run r (by decide) (by decide) (by decide) (by decide)⟩

theorem renEnt_run {W M : ℕ} {τ : Env} {l : List ℕ} (hC : Ctx W M τ) (hF : Filled "OB" "po" l τ)
    (hp : τ.vars "y" + 1 + τ.vars "fk" < M) (hft : τ.vars "ft" < M) (hc1 : τ.vars "c1" < M)
    (hl : l.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) renEnt τ τ' 46 ∧
      Filled "OB" "po" (l ++ [xg (τ.arrs "x") (τ.vars "y" + 1 + τ.vars "fk") +
        (if posB (τ.vars "ft") (τ.vars "fk") then τ.vars "c1" else 0)]) τ' ∧ OFr τ τ' ["fb", "po"] := by
  have hM := hC.room
  have h16 := hC.m16
  obtain ⟨τ1, r1, hfb, O1⟩ := posCmd_run (τ := τ) (W := W) (by omega) (by omega) (by omega)
  have C1 := hC.ofr O1 (by decide)
  have vy := O1.vars "y" (by decide)
  have vk := O1.vars "fk" (by decide)
  have vc := O1.vars "c1" (by decide)
  have vx := O1.arrs "x" (by decide)
  set Xa := τ.arrs "x"
  have hlt : τ.vars "y" + 1 + τ.vars "fk" < Xa.length := by rw [hC.xl]; omega
  have hxv : xg Xa (τ.vars "y" + 1 + τ.vars "fk") < M := hC.xv _ (List.mem_of_getElem? (xg_get hlt))
  set fbv := (if posB (τ.vars "ft") (τ.vars "fk") then 1 else 0) with hfbv
  have hfb1 : fbv ≤ 1 := by rw [hfbv]; split <;> omega
  have hmul : fbv * τ.vars "c1" = if posB (τ.vars "ft") (τ.vars "fk") then τ.vars "c1" else 0 := by
    rw [hfbv]; split <;> simp
  have ey : (V "y").evalB (W + 1) τ1 = some (τ.vars "y") := by rw [← vy]; exact evalB_var (by omega)
  have ek : (V "fk").evalB (W + 1) τ1 = some (τ.vars "fk") := by rw [← vk]; exact evalB_var (by omega)
  have e1 : (Expr.add (V "y") (N 1)).evalB (W + 1) τ1 = some (τ.vars "y" + 1) :=
    evalB_bin ey (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
  have e2 : (Expr.add (.add (V "y") (N 1)) (V "fk")).evalB (W + 1) τ1 =
      some (τ.vars "y" + 1 + τ.vars "fk") := evalB_bin e1 ek (by simp only [Bop.apply_add]; omega)
  have e3 : (X (.add (.add (V "y") (N 1)) (V "fk"))).evalB (W + 1) τ1 =
      some (xg Xa (τ.vars "y" + 1 + τ.vars "fk")) :=
    evalB_get e2 (by rw [vx]; exact xg_get hlt) (by omega)
  have efb : (V "fb").evalB (W + 1) τ1 = some fbv := by rw [← hfb]; exact evalB_var (by omega)
  have ec : (V "c1").evalB (W + 1) τ1 = some (τ.vars "c1") := by rw [← vc]; exact evalB_var (by omega)
  have e4 : (Expr.mul (V "fb") (V "c1")).evalB (W + 1) τ1 = some (fbv * τ.vars "c1") :=
    evalB_bin efb ec (by simp only [Bop.apply_mul]; rw [hmul]; split <;> omega)
  have e5 := evalB_bin (op := .add) e3 e4 (by simp only [Bop.apply_add]; rw [hmul]; split <;> omega)
  simp only [Bop.apply_add, hmul] at e5
  obtain ⟨τ2, r2, F2, O2⟩ := pv_run C1 (hF.congr (O1.vars "po" (by decide)) (r1.frame_arr "OB" (by decide)))
    e5 hl
  refine ⟨τ2, (Run.seq r1 r2).mono (by simp [Expr.size]), F2, (O1.trans O2).mono (by simp)⟩

theorem renAtom_eq (l : ℕ) (c : List ℕ) :
    renAtom l c = (List.range c.length).flatMap fun k =>
      [c.getD k 0 + if posB (c.headD 0) k then l else 0] := by
  rw [flatMap_single_eq_map]
  apply List.ext_getElem
  · simp [renAtom]
  · intro i h1 h2
    simp only [renAtom, List.getElem_mapIdx, List.getElem_map, List.getElem_range]
    have hi : i < c.length := by simpa [renAtom] using h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    split <;> simp

theorem renFr_run {W M : ℕ} {τ : Env} {l c rest : List ℕ} (hC : Ctx W M τ)
    (hF : Filled "OB" "po" l τ) (hx : (τ.arrs "x").drop (τ.vars "y") = (c.length :: c) ++ rest)
    (hy : τ.vars "y" + 1 + c.length ≤ M) (hc1 : τ.vars "c1" < M) (hl : l.length + 2 * M ≤ W) :
    ∃ τ', Run (W + 1) renFr τ τ' (60 * c.length + 30) ∧
      Filled "OB" "po" (l ++ (c.length :: renAtom (τ.vars "c1") c)) τ' ∧
      τ'.vars "y" = τ.vars "y" + 1 + c.length ∧
      OFr τ τ' ["fl", "po", "ft", "fk", "fb", "y"] := by
  have hM := hC.room
  have h16 := hC.m16
  set Xa := τ.arrs "x" with hXa
  obtain ⟨y, hyv⟩ : ∃ y, τ.vars "y" = y := ⟨_, rfl⟩
  rw [hyv] at hx hy
  have hlt : y < Xa.length := by rw [hC.xl]; omega
  have hx0 : xg Xa y = c.length := xg_of_drop (by rw [hx]; rfl)
  have hx1 : Xa.drop (y + 1) = c ++ rest := by
    have := drop_add_of_drop (u := [c.length]) (r := c ++ rest) (by rw [hx]; rfl)
    simpa using this
  have hxk : ∀ k < c.length, xg Xa (y + 1 + k) = c.getD k 0 := by
    intro k hk
    have := congrArg (fun L => L[k]?) hx1
    simp only [List.getElem?_drop, List.getElem?_append_left hk] at this
    simp [xg, List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem hk]
  -- fl := x[y]
  have ey : (V "y").evalB (W + 1) τ = some y := by rw [← hyv]; exact evalB_var (by omega)
  have r1 := Run.assign (x := "fl") (evalB_get (v := c.length) ey (by rw [← hx0]; exact xg_get hlt)
    (by omega))
  have C1 := hC.setVar (y := "fl") (by decide) c.length
  obtain ⟨τ2, r2, F2, O2⟩ := pv_run C1 (hF.setVar (by decide) _) (e := V "fl")
    (evalB_var (by simp; omega)) (by omega)
  simp only [vars_setVar, if_true] at F2
  have C2 := C1.ofr O2 (by decide)
  have vy2 : τ2.vars "y" = y := by rw [O2.vars "y" (by decide)]; simp [hyv]
  have hlt1 : y + 1 < Xa.length := by rw [hC.xl]; omega
  have hft : xg Xa (y + 1) < M := hC.xv _ (List.mem_of_getElem? (xg_get hlt1))
  have ey2 : (Expr.add (V "y") (N 1)).evalB (W + 1) τ2 = some (y + 1) :=
    evalB_bin (by rw [← vy2]; exact evalB_var (by omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply_add]; omega)
  have vx2 : τ2.arrs "x" = Xa := by rw [O2.arrs "x" (by decide)]; simp [hXa]
  have r3 := Run.assign (x := "ft") (evalB_get (v := xg Xa (y + 1)) ey2 (by rw [vx2]; exact xg_get hlt1)
    (by omega))
  set τ3 := τ2.setVar "ft" (xg Xa (y + 1)) with hτ3
  have C3 := C2.setVar (y := "ft") (by decide) (xg Xa (y + 1))
  have F3 := F2.setVar (y := "ft") (by decide) (xg Xa (y + 1))
  have O3 : OFr τ τ3 ["fl", "po", "ft"] :=
    ((OFr.setVar τ "fl" _).trans (O2.trans (OFr.setVar τ2 "ft" _))).mono (by simp)
  have vfl3 : τ3.vars "fl" = c.length := by
    rw [hτ3, vars_setVar, if_neg (by decide), O2.vars "fl" (by decide)]; simp
  -- the entries
  set c1 := τ.vars "c1"
  let f : ℕ → List ℕ := fun k => [xg Xa (y + 1 + k) + if posB (xg Xa (y + 1)) k then c1 else 0]
  obtain ⟨τ4, r4, P4, -, F4⟩ := forUp_append (B := W + 1) (i := "fk") (e := V "fl") (body := renEnt)
    (N := c.length) (K := 46) (a := "OB") (pv := "po") (by decide) f
    (fun τ' => OFr τ3 τ' ["po", "fb", "fk"]) (fun τ' v hP => (hP.trans (OFr.setVar τ' "fk" v)).mono (by simp))
    (by omega) (OFr.refl τ3 |>.mono (by simp)) F3
    (fun τ' hP => by
      rw [show c.length = τ'.vars "fl" by rw [hP.vars "fl" (by decide), vfl3]]
      exact evalB_var (by rw [hP.vars "fl" (by decide), vfl3]; omega))
    (fun k hk τ' hP hik hF' => by
      have O' := O3.trans hP
      have Cτ := hC.ofr O' (by decide)
      have hlen : (l ++ c.length :: [] ++ (List.range k).flatMap f).length = l.length + 1 + k := by
        rw [List.length_append, length_flatMap_const (m := 1) (fun _ => rfl)]; simp
      have vy' : τ'.vars "y" = y := by rw [O'.vars "y" (by decide), hyv]
      have vft : τ'.vars "ft" = xg Xa (y + 1) := by rw [hP.vars "ft" (by decide)]; simp [hτ3]
      have vc' : τ'.vars "c1" = c1 := O'.vars "c1" (by decide)
      have vx' : τ'.arrs "x" = Xa := O'.arrs "x" (by decide)
      obtain ⟨τ'', r, F', O''⟩ := renEnt_run Cτ hF' (by omega) (by omega) (by omega)
        (by rw [hlen]; omega)
      refine ⟨τ'', r, by rw [O''.vars "fk" (by decide), hik], (hP.trans O'').mono (by simp), ?_⟩
      rw [vy', vft, vc', vx', hik] at F'
      rw [List.range_succ, List.flatMap_append, ← List.append_assoc]
      simpa [f] using F')
  have O4 := O3.trans P4
  have C4 := hC.ofr O4 (by decide)
  have hF4 : (List.range c.length).flatMap f = renAtom c1 c := by
    rw [renAtom_eq, flatMap_single_eq_map, flatMap_single_eq_map]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hc0 : xg Xa (y + 1) = c.headD 0 := by
      have := hxk 0 (by omega)
      rw [Nat.add_zero] at this; rw [this]
      cases c with
      | nil => simp at hk
      | cons a c => rfl
    rw [hxk k hk, hc0]
  rw [hF4] at F4
  -- y := y + x[y] + 1
  have vy4 : τ4.vars "y" = y := by rw [O4.vars "y" (by decide), hyv]
  have vx4 : τ4.arrs "x" = Xa := O4.arrs "x" (by decide)
  have e0 : (V "y").evalB (W + 1) τ4 = some y := by rw [← vy4]; exact evalB_var (by omega)
  have e1' : (X (V "y")).evalB (W + 1) τ4 = some c.length :=
    evalB_get e0 (by rw [vx4, ← hx0]; exact xg_get hlt) (by omega)
  have e2' := evalB_bin (op := .add) e0 e1' (by simp only [Bop.apply_add]; omega)
  have e3' := evalB_bin (op := .add) e2' (evalB_lit (B := W + 1) (n := 1) (σ := τ4) (by omega))
    (by simp only [Bop.apply_add]; omega)
  simp only [Bop.apply_add] at e3'
  have r5 := Run.assign (x := "y") e3'
  refine ⟨τ4.setVar "y" (y + c.length + 1), ?_, ?_, by simp; omega,
    (O4.trans (OFr.setVar τ4 "y" _)).mono (by simp)⟩
  · simp only [renFr, seqs]
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    simp [Expr.size]; omega
  · have := F4.setVar (y := "y") (by decide) (y + c.length + 1)
    simpa using this

private theorem drop_of_seg {Xa w : List ℕ} {a : ℕ} (h : seg Xa a w.length = w) (hl : a + w.length ≤ Xa.length) :
    Xa.drop a = w ++ Xa.drop (a + w.length) := by
  conv_lhs => rw [← List.take_append_drop w.length (Xa.drop a)]
  rw [List.drop_drop]
  simp only [seg] at h
  rw [h]

theorem flat_ren (l : ℕ) (L : List (List ℕ)) :
    L.flatMap (fun c => c.length :: renAtom l c) = frames (L.map (renAtom l)) := by
  induction L with
  | nil => rfl
  | cons c L ih => simp [frames, length_renAtom] at ih ⊢; exact ih

theorem length_frames_ren (l : ℕ) (L : List (List ℕ)) :
    (frames (L.map (renAtom l))).length = (frames L).length := by
  induction L with
  | nil => rfl
  | cons c L ih => simp [frames, length_renAtom] at ih ⊢; omega

/-- The scalars written by `emAtoms`. -/
def emAtomsVars : List String :=
  ["y", "sn", "sk", "u1", "u2", "ci", "po", "nr", "rk", "fl", "ft", "fk", "fb"]

theorem emAtoms_run {W M : ℕ} {σ : Env} {pre A B rA rB : List ℕ} {d kk l1 l2 : ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" pre σ) (hf : FreshIs M σ d kk l1 l2 A B)
    (hA : A = toWord (atomsOf A) ++ rA) (hB : B = toWord (atomsOf B) ++ rB) (hl : l1 < M)
    (hpre : pre.length + 8 * M ≤ W) :
    ∃ σ', Run (W + 1) emAtoms σ σ' (60 * (A.length + B.length) + 100) ∧
      Filled "OB" "po" (pre ++ toWord (atomsOf A ++ (atomsOf B).map (renAtom l1))) σ' ∧
      (toWord (atomsOf A ++ (atomsOf B).map (renAtom l1))).length ≤ A.length + B.length ∧
      OFr σ σ' emAtomsVars := by
  have hM := hC.room
  have h16 := hC.m16
  set Xa := σ.arrs "x" with hXa
  set LA := atomsOf A
  set LB := atomsOf B
  obtain ⟨hcd, hck, hc1, hc2, -, ⟨hAl, hAp, hAs⟩, ⟨hBl, hBp, hBs⟩⟩ := hf
  obtain ⟨a, ha⟩ : ∃ a, σ.vars "cAs" = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, σ.vars "cBs" = b := ⟨_, rfl⟩
  rw [ha] at hAp hAs; rw [hb] at hBp hBs
  rw [← hXa] at hAs hBs
  have hXl : Xa.length = W + 1 := hC.xl
  have hdA : Xa.drop a = toWord LA ++ (rA ++ Xa.drop (a + A.length)) := by
    rw [drop_of_seg hAs (by omega)]; nth_rewrite 1 [hA]; simp [List.append_assoc]
  have hdB : Xa.drop b = toWord LB ++ (rB ++ Xa.drop (b + B.length)) := by
    rw [drop_of_seg hBs (by omega)]; nth_rewrite 1 [hB]; simp [List.append_assoc]
  have hLAl : (toWord LA).length ≤ A.length := by
    have := congrArg List.length hA; simp at this; omega
  have hLBl : (toWord LB).length ≤ B.length := by
    have := congrArg List.length hB; simp at this; omega
  obtain ⟨xA0, -, -, eA, dA⟩ := listAt hdA
  obtain ⟨xB0, fB, gB, eB, -⟩ := listAt hdB
  have hTA := toWord_words LA
  have hTB := toWord_words LB
  have hfA := length_frames_ge LA
  have hfB := length_frames_ge LB
  have hlTA : (toWord LA).length = (frames LA).length + 1 := by rw [hTA]; simp
  have hlTB : (toWord LB).length = (frames LB).length + 1 := by rw [hTB]; simp
  -- y := cAs, skip the atoms of A
  have r1 := Run.assign (x := "y") (evalB_var (B := W + 1) (σ := σ) (x := "cAs") (by omega))
  rw [ha] at r1
  obtain ⟨τ2, r2, hy2, O2⟩ := skipL_run' (hC.setVar (y := "y") (by decide) a) (p := a)
    (by simpa using hdA) (by simp) (by omega)
  have O2' := (OFr.setVar σ "y" a).trans O2
  have C2 := hC.ofr O2' (by decide)
  have vx2 : τ2.arrs "x" = Xa := O2'.arrs "x" (by decide)
  have va2 : τ2.vars "cAs" = a := by rw [O2'.vars "cAs" (by decide), ha]
  have vb2 : τ2.vars "cBs" = b := by rw [O2'.vars "cBs" (by decide), hb]
  -- u1, u2
  have r3 := Run.assign (x := "u1") (evalB_bin (op := .add) (evalB_var (B := W + 1) (σ := τ2) (x := "cAs")
    (by omega)) (evalB_lit (B := W + 1) (σ := τ2) (n := 1) (by omega)) (by simp only [Bop.apply_add]; omega))
  simp only [Bop.apply_add, va2] at r3
  set τ3 := τ2.setVar "u1" (a + 1) with hτ3
  have e4 : (Expr.sub (.sub (V "y") (V "cAs")) (N 1)).evalB (W + 1) τ3 = some (frames LA).length := by
    simp [hτ3, hy2, va2]; omega
  have r4 := Run.assign (x := "u2") e4
  set τ4 := τ3.setVar "u2" (frames LA).length with hτ4
  have O4 : OFr σ τ4 ["y", "sn", "sk", "u1", "u2"] :=
    ((O2'.trans (OFr.setVar τ2 "u1" _)).trans (OFr.setVar τ3 "u2" _)).mono (by simp)
  have C4 := hC.ofr O4 (by decide)
  have F4 : Filled "OB" "po" pre τ4 := hF.congr (O4.vars "po" (by decide)) (by
    rw [show τ4.arrs "OB" = τ2.arrs "OB" by simp [hτ4, hτ3]]
    exact r2.frame_arr "OB" (by decide) |>.trans (by simp))
  -- the count
  have hla : a < Xa.length := by omega
  have hlb : b < Xa.length := by omega
  have ex : ∀ i, i < Xa.length → (X (V i.repr)).evalB (W + 1) τ4 = (X (V i.repr)).evalB (W + 1) τ4 :=
    fun _ _ => rfl
  have eA4 : (X (V "cAs")).evalB (W + 1) τ4 = some LA.length :=
    evalB_get (evalB_var (by simp [hτ4, hτ3, va2]; omega)) (by
      simp only [hτ4, hτ3, vars_setVar, arrs_setVar]; simp only [va2, vx2]; rw [← xA0]; exact xg_get hla)
      (by have := length_frames_ge LA; omega)
  have eB4 : (X (V "cBs")).evalB (W + 1) τ4 = some LB.length :=
    evalB_get (evalB_var (by simp [hτ4, hτ3, vb2]; omega)) (by
      simp only [hτ4, hτ3, vars_setVar, arrs_setVar]; simp only [vb2, vx2]; rw [← xB0]; exact xg_get hlb)
      (by omega)
  obtain ⟨τ5, r5, F5, O5⟩ := pv_run C4 F4 (evalB_bin (op := .add) eA4 eB4
    (by simp only [Bop.apply_add]; omega)) (by omega)
  simp only [Bop.apply_add] at F5
  have C5 := C4.ofr O5 (by decide)
  -- the frames of the atoms of A
  have hsegA : SegIs M τ5 "u1" "u2" (frames LA) := by
    refine ⟨by rw [O5.vars "u2" (by decide)]; simp [hτ4], by
      rw [O5.vars "u1" (by decide)]; simp [hτ4, hτ3]; omega, ?_⟩
    rw [O5.vars "u1" (by decide), O5.arrs "x" (by decide)]
    simp only [hτ4, hτ3, vars_setVar, arrs_setVar, if_pos, if_neg]
    simp only [show ("u1" = "u2") = False by decide, if_false, if_true, vx2, seg]
    have hd1 : Xa.drop (a + 1) = frames LA ++ (rA ++ Xa.drop (a + A.length)) := by
      have := drop_add_of_drop (u := [LA.length]) (r := frames LA ++ (rA ++ Xa.drop (a + A.length)))
        (by rw [hdA, hTA]; rfl)
      simpa using this
    rw [hd1]; simp
  obtain ⟨τ6, r6, F6, O6⟩ := emSeg_run (by decide) (by decide) C5 F5 hsegA (by simp; omega)
  have O6' := (O4.trans O5).trans O6
  have C6 := hC.ofr O6' (by decide)
  -- nr := x[cBs], y := cBs + 1
  have eB6 : (X (V "cBs")).evalB (W + 1) τ6 = some LB.length :=
    evalB_get (evalB_var (by rw [O6'.vars "cBs" (by decide), hb]; omega)) (by
      rw [O6'.vars "cBs" (by decide), hb, O6'.arrs "x" (by decide), ← xB0]; exact xg_get hlb) (by omega)
  have r7 := Run.assign (x := "nr") eB6
  set τ7 := τ6.setVar "nr" LB.length with hτ7
  have r8 := Run.assign (x := "y") (evalB_bin (op := .add) (evalB_var (B := W + 1) (σ := τ7) (x := "cBs")
    (by simp [hτ7]; rw [O6'.vars "cBs" (by decide), hb]; omega))
    (evalB_lit (B := W + 1) (σ := τ7) (n := 1) (by omega))
    (by simp only [Bop.apply_add]; simp [hτ7]; rw [O6'.vars "cBs" (by decide), hb]; omega))
  have vb7 : τ7.vars "cBs" = b := by simp [hτ7]; rw [O6'.vars "cBs" (by decide), hb]
  simp only [Bop.apply_add, vb7] at r8
  set τ8 := τ7.setVar "y" (b + 1) with hτ8
  have O8 : OFr σ τ8 ["y", "sn", "sk", "u1", "u2", "po", "ci", "nr"] :=
    ((O6'.trans (OFr.setVar τ6 "nr" _)).trans (OFr.setVar τ7 "y" _)).mono (by simp)
  have C8 := hC.ofr O8 (by decide)
  set l8 := pre ++ [LA.length + LB.length] ++ frames LA with hl8
  have F8 : Filled "OB" "po" l8 τ8 := (F6.setVar (by decide) _).setVar (by decide) _
  have hl8len : l8.length = pre.length + 1 + (frames LA).length := by simp [hl8]; omega
  -- the loop over the atoms of B
  set E := b + (toWord LB).length with hE
  have hc1' : σ.vars "c1" = l1 := hc1
  let I : Env → Prop := fun τ => ∃ j ≤ LB.length, τ.vars "rk" = j ∧ τ.vars "y" = frPos Xa b j ∧
    Filled "OB" "po" (l8 ++ (LB.take j).flatMap fun c => c.length :: renAtom l1 c) τ ∧
    OFr τ8 τ ["rk", "fl", "po", "ft", "fk", "fb", "y"]
  have hfp : ∀ j ≤ LB.length, frPos Xa b j + (frames (LB.drop j)).length ≤ E := by
    intro j hj
    obtain ⟨h1, -⟩ := fB j hj
    have h2 := List.take_append_drop j LB
    have h3 : (frames (LB.take j)).length + (frames (LB.drop j)).length = (frames LB).length := by
      rw [← List.length_append, ← frames_append, h2]
    omega
  have hwhile := Run.while_potential (B := W + 1) (b := .lt (V "rk") (V "nr"))
    (c := .seq renFr (asg "rk" (.add (V "rk") (N 1)))) I (fun τ => 60 * (E - τ.vars "y"))
    (fun τ ⟨j, hj, hrk, _, _, O⟩ => evalB_condLt_vars (by rw [hrk]; omega)
      (by rw [O.vars "nr" (by decide)]; simp [hτ8, hτ7]; omega))
    (fun τ ⟨j, hj, hrk, hy, Fτ, O⟩ hc => by
      have vnr : τ.vars "nr" = LB.length := by rw [O.vars "nr" (by decide)]; simp [hτ8, hτ7]
      have hjl : j < LB.length := by
        rw [evalB_condLt (evalB_var (by rw [hrk]; omega)) (evalB_var (by rw [vnr]; omega)), hrk, vnr] at hc
        simpa using hc
      have Oτ := O8.trans O
      have Cτ := hC.ofr Oτ (by decide)
      obtain ⟨-, hdj⟩ := fB j hj
      rw [frames_drop hjl] at hdj
      have hfpj := hfp j hj
      have hfps := hfp (j + 1) hjl
      rw [frames_drop hjl] at hfpj
      simp only [List.length_cons, List.length_append] at hfpj
      have hlenj : (l8 ++ (LB.take j).flatMap fun c => c.length :: renAtom l1 c).length ≤
          pre.length + 1 + (frames LA).length + (frames LB).length := by
        rw [List.length_append, flat_ren, length_frames_ren, hl8len]
        have := length_frames_take_le LB j; omega
      obtain ⟨τ', r, F', hy', O'⟩ := renFr_run (c := LB[j]) (rest := frames (LB.drop (j + 1)) ++
        (rB ++ Xa.drop (b + B.length))) Cτ Fτ
        (by rw [Oτ.arrs "x" (by decide), hy]; simpa using hdj) (by rw [hy]; omega)
        (by rw [Oτ.vars "c1" (by decide)]; omega) (by omega)
      rw [Oτ.vars "c1" (by decide), hc1'] at F'
      have Cτ' := Cτ.ofr O' (by decide)
      have vrk' : τ'.vars "rk" = j := by rw [O'.vars "rk" (by decide), hrk]
      have r' := Run.assign (x := "rk") (evalB_bin (op := .add) (evalB_var (B := W + 1) (σ := τ')
        (x := "rk") (by omega)) (evalB_lit (B := W + 1) (σ := τ') (n := 1) (by omega))
        (by simp only [Bop.apply_add]; omega))
      simp only [Bop.apply_add, vrk'] at r'
      refine ⟨τ'.setVar "rk" (j + 1), _, Run.seq r r', ⟨j + 1, hjl, by simp, ?_, ?_, ?_⟩, ?_⟩
      · rw [vars_setVar, if_neg (by decide), hy', hy]
        obtain ⟨e1, -⟩ := fB j hj; obtain ⟨e2, -⟩ := fB (j + 1) hjl
        rw [e1, e2, length_frames_take_succ hjl]; omega
      · have e : (LB.take (j + 1)).flatMap (fun c => c.length :: renAtom l1 c) =
            (LB.take j).flatMap (fun c => c.length :: renAtom l1 c) ++
              (LB[j].length :: renAtom l1 LB[j]) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some,
            List.flatMap_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [e, ← List.append_assoc]
        exact F'.setVar (y := "rk") (by decide) (j + 1)
      · exact ((O.trans O').trans (OFr.setVar τ' "rk" _)).mono (by simp)
      · simp only [vars_setVar, if_neg (show ¬ ("y" = "rk") by decide), hy', hy, Cond.size,
          Expr.size]
        omega)
    (show I (τ8.setVar "rk" 0) from
      ⟨0, Nat.zero_le _, by simp, by
        simp [hτ8, frPos, skipFr], by simpa using F8.setVar (y := "rk") (by decide) 0,
        (OFr.setVar τ8 "rk" 0).mono (by simp)⟩)
  obtain ⟨τ9, K9, r9, ⟨j9, hj9, hrk9, -, F9, O9⟩, hfalse, hK9⟩ := hwhile
  have vnr9 : τ9.vars "nr" = LB.length := by rw [O9.vars "nr" (by decide)]; simp [hτ8, hτ7]
  have hj9' : j9 = LB.length := by
    rw [evalB_condLt (evalB_var (by rw [hrk9]; omega)) (evalB_var (by rw [vnr9]; omega)), hrk9, vnr9]
      at hfalse
    simp at hfalse; omega
  rw [hj9', List.take_length, flat_ren] at F9
  have hfinal : l8 ++ frames (LB.map (renAtom l1)) = pre ++ toWord (LA ++ LB.map (renAtom l1)) := by
    rw [hl8, toWord_words, frames_append]; simp
  rw [hfinal] at F9
  refine ⟨τ9, ?_, F9, ?_, (O8.trans O9).mono (by simp [emAtomsVars])⟩
  · simp only [emAtoms, seqs, forUp]
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq (Run.assign (x := "rk") (evalB_lit (B := W + 1) (σ := τ8) (n := 0)
        (by omega))) r9))))))))).mono ?_
    have hy0 : (τ8.setVar "rk" 0).vars "y" = b + 1 := by simp [hτ8]
    rw [hy0] at hK9
    simp [Expr.size, Cond.size] at hK9 ⊢
    omega
  · have := length_toWord_append LA (LB.map (renAtom l1))
    rw [length_toWord_map_renAtom] at this
    omega

end Lax185574Proofs.CompRam
