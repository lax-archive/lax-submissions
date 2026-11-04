import Lax185574Proofs.CompRam.GBase

/-!
Reading the input and moving through the array `x` in the glue command
of lem:compose.

`rdN_run`: reading `n` entries appends them to `x`. `skipK_run`,
`skipL_run`, `skipNode_run`: the scalar `y` moves past frames, a list of
words, a node word. `extsAt_run`: the list of extensions of a node word
and their number. `extFr_run`: a frame of a list of words. `locW_run`:
the positions of the frames of the first words of the stack.
`ldG_run`, `ldRest_run`: the scalars of a frame of the stack and the
segment of the rest of the stack.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Frames of commands that write scalars only -/

theorem ofr_of_run {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} {xs : List String} (h : Run B c σ σ' K)
    (hv : c.wvars ⊆ xs) (ha : c.warrs = []) (hw : c.NoWrite) (hr : ¬ c.reads) : OFr σ σ' xs :=
  ⟨fun y hy => h.frame_var_sub y hv hy, fun b _ => h.frame_arr b (by simp [ha]),
    run_length_arrs h "OB", h.out_eq hw, h.frame_inp hr⟩

theorem getElem?_xg {X : List ℕ} {i : ℕ} (h : i < X.length) : X[i]? = some (xg X i) := by
  rw [List.getElem?_eq_getElem h, xg_of_lt h]

theorem xg_lt_M {W M : ℕ} {σ : Env} (hC : Ctx W M σ) (i : ℕ) : xg (σ.arrs "x") i < M := by
  unfold xg
  rw [List.getD_eq_getElem?_getD]
  cases h : (σ.arrs "x")[i]? with
  | none => have := hC.m16; simp; omega
  | some v => exact hC.xv v (List.mem_of_getElem? h)

/-- An entry of `x` read at a scalar position. -/
theorem evalB_xvar {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {y : String} (hy : σ.vars y ≤ W) :
    (X (V y)).evalB (W + 1) σ = some (xg (σ.arrs "x") (σ.vars y)) := by
  have hl := hC.xl
  have := xg_lt_M hC (σ.vars y)
  have := hC.room
  exact evalB_get (evalB_var (by omega)) (getElem?_xg (by omega)) (by omega)

/-- An entry of `x` at a position given by an expression. -/
theorem evalB_xe {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {e : Expr} {p : ℕ}
    (he : e.evalB (W + 1) σ = some p) (hp : p ≤ W) :
    (X e).evalB (W + 1) σ = some (xg (σ.arrs "x") p) := by
  have hl := hC.xl
  have := xg_lt_M hC p
  have := hC.room
  exact evalB_get he (getElem?_xg (by omega)) (by omega)

/-! ### Reading -/

theorem rdN_run {W : ℕ} {σ : Env} {pre u rest : List ℕ} {n : String} (hn : n ∉ ["ri", "rv", "xp"])
    (hF : Filled "x" "xp" pre σ) (hl : (σ.arrs "x").length = W + 1) (hinp : σ.inp = u ++ rest)
    (hN : σ.vars n = u.length) (hB : pre.length + u.length ≤ W) (hv : ∀ v ∈ u, v ≤ W) :
    ∃ σ', Run (W + 1) (rdN n) σ σ' (20 * u.length + 10) ∧ Filled "x" "xp" (pre ++ u) σ' ∧
      σ'.inp = rest ∧ (∀ y, y ∉ ["ri", "rv", "xp"] → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a) ∧ (σ'.arrs "x").length = W + 1 ∧ σ'.out = σ.out := by
  have hn1 : n ≠ "ri" := fun h => hn (by simp [h])
  have hn2 : n ≠ "rv" := fun h => hn (by simp [h])
  have hn3 : n ≠ "xp" := fun h => hn (by simp [h])
  let P : Env → Prop := fun τ => τ.vars n = u.length ∧ (τ.arrs "x").length = W + 1 ∧
    (∀ y, y ∉ ["ri", "rv", "xp"] → τ.vars y = σ.vars y) ∧ (∀ a, a ≠ "x" → τ.arrs a = σ.arrs a) ∧
    τ.out = σ.out
  obtain ⟨σ', r, ⟨⟨g1, g2, g3, g4, g5⟩, hF', hinp'⟩, hi'⟩ := forUp_run (B := W + 1) (i := "ri") (e := V n) (body := rdBody)
    (N := u.length) (K := 10)
    (fun k τ => P τ ∧ Filled "x" "xp" (pre ++ u.take k) τ ∧ τ.inp = u.drop k ++ rest) (by omega)
    (fun k _ τ hI _ => by rw [← hI.1.1]; exact evalB_var (by rw [hI.1.1]; omega))
    ⟨⟨by simp [hn1, hN], by simp [hl], fun y hy => by
        simp only [vars_setVar]; rw [if_neg (fun h => hy (by simp [h]))], fun a _ => rfl, rfl⟩,
      by simpa using hF.setVar (by decide) 0, by simp [hinp]⟩
    (by
      intro k hk τ ⟨⟨h1, h2, h3, h4, h5⟩, hFk, hik⟩ hrk
      have hku : k < u.length := hk
      have hd : u.drop k = u[k] :: u.drop (k + 1) := List.drop_eq_getElem_cons hku
      set τ1 : Env := { τ.setVar "rv" u[k] with inp := u.drop (k + 1) ++ rest } with hτ1
      have r1 : Run (W + 1) (.read "rv") τ τ1 1 := Run.read (by rw [hik, hd]; rfl)
      have hF1 : Filled "x" "xp" (pre ++ u.take k) τ1 := hFk.congr (by simp [hτ1]) (by simp [hτ1])
      have hlen : (pre ++ u.take k).length = pre.length + k := by simp; omega
      obtain ⟨τ2, r2, F2, fv, fa, fl, fo, fi⟩ := push1_run (B := W + 1) (e := V "rv") (v := u[k]) hF1
        (evalB_var (by have := hv u[k] (List.getElem_mem hku); simp [hτ1]; omega))
        (by rw [hlen]; simp [hτ1, h2]; omega) (by rw [hlen]; omega)
      refine ⟨τ2, (Run.seq r1 r2).mono (by simp), ?_, ?_⟩
      · rw [fv "ri" (by decide)]; simp [hτ1, hrk]
      · refine ⟨⟨?_, ?_, fun y hy => ?_, fun a ha => ?_, ?_⟩, ?_, ?_⟩
        · simp [fv n hn3, hτ1, hn1, hn2, h1]
        · simp [fl, hτ1, h2]
        · have : y ≠ "ri" := fun h => hy (by simp [h])
          have : y ≠ "rv" := fun h => hy (by simp [h])
          have : y ≠ "xp" := fun h => hy (by simp [h])
          simp [fv y ‹y ≠ "xp"›, hτ1, *]
        · simp [fa a ha, hτ1, h4 a ha]
        · simp [fo, hτ1, h5]
        · have := F2.setVar (y := "ri") (by decide) (k + 1)
          rw [List.take_succ_eq_append_getElem hku, ← List.append_assoc]; exact this
        · simp [fi, hτ1])
  refine ⟨σ', r.mono ?_, by simpa using hF', by simpa using hinp', g3, g4, g2, g5⟩
  simp [Expr.size]; omega

/-! ### Moving past frames -/

theorem stepY_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {p : ℕ} (hy : σ.vars "y" = p)
    (hp : p + xg (σ.arrs "x") p + 1 ≤ W) :
    Run (W + 1) stepY σ (σ.setVar "y" (p + xg (σ.arrs "x") p + 1)) 8 := by
  have hx := evalB_xvar hC (y := "y") (by omega)
  have he : (Expr.add (.add (V "y") (X (V "y"))) (N 1)).evalB (W + 1) σ =
      some (p + xg (σ.arrs "x") p + 1) := by
    have := evalB_bin (op := .add) (evalB_bin (op := .add) (evalB_var (B := W + 1) (x := "y") (σ := σ)
      (by omega)) hx (by simp only [Bop.apply_add]; rw [hy]; omega)) (evalB_lit (B := W + 1) (n := 1)
      (σ := σ) (by omega)) (by simp only [Bop.apply_add]; rw [hy]; omega)
    rw [this]; simp [hy]
  exact (Run.assign he).mono (by simp [Expr.size])

theorem skipK_run {W M : ℕ} {σ : Env} {k : String} (hk : k ∉ ["y", "sk"]) (hC : Ctx W M σ) {f : ℕ}
    {ws : List (List ℕ)} {r : List ℕ} (hx : (σ.arrs "x").drop f = frames ws ++ r) (hy : σ.vars "y" = f)
    (hK : σ.vars k ≤ ws.length) (hf : f + (frames ws).length ≤ M) :
    ∃ σ', Run (W + 1) (skipK k) σ σ' (20 * σ.vars k + 10) ∧
      σ'.vars "y" = skipFr (σ.arrs "x") f (σ.vars k) ∧ OFr σ σ' ["y", "sk"] := by
  have hk1 : k ≠ "y" := fun h => hk (by simp [h])
  have hk2 : k ≠ "sk" := fun h => hk (by simp [h])
  obtain ⟨X, hX⟩ : ∃ X, σ.arrs "x" = X := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K, σ.vars k = K := ⟨_, rfl⟩
  rw [hX] at hx ⊢
  rw [hKd] at hK ⊢
  have hroom := hC.room
  have hm16 := hC.m16
  have hfl := length_frames ws
  obtain ⟨σ', r, ⟨-, -, -, hP3⟩, hi'⟩ := forUp_run (B := W + 1) (i := "sk") (e := V k) (body := stepY)
    (N := K) (K := 8)
    (fun j τ => τ.vars k = K ∧ Ctx W M τ ∧ τ.arrs "x" = X ∧ τ.vars "y" = skipFr X f j) (by omega)
    (fun j _ τ hI _ => by rw [← hI.1]; exact evalB_var (by rw [hI.1]; omega))
    ⟨by simp [hk2, hKd], hC.setVar (by decide) 0, by simp [hX], by simp [hy, skipFr]⟩
    (by
      intro j hj τ ⟨h1, h2, h3, h4⟩ hsk
      have hjw : j < ws.length := by omega
      obtain ⟨e1, e2⟩ := skipFr_frames hx (j := j) hjw.le
      rw [frames_drop hjw] at e2
      have hxg : xg X (skipFr X f j) = ws[j].length := xg_of_drop (by rw [e2]; rfl)
      have hs := length_frames_take_succ hjw
      have hle := length_frames_take_le ws (j + 1)
      have hst := skipFr_succ' X f j
      have r1 := stepY_run h2 h4 (by rw [h3, hxg, e1]; omega)
      refine ⟨_, r1, by simp [hsk], by simp [hk1, hk2, h1], (h2.setVar (by decide) _).setVar (by decide) _,
        by simp [h3], ?_⟩
      simp only [vars_setVar, if_neg (show ("y" : String) ≠ "sk" by decide), if_true]
      rw [h3, hst]; omega)
  refine ⟨σ', r.mono (by simp only [Expr.size]; omega), by rw [hP3], ofr_of_run r ?_ (by
    simp [skipK, forUp, stepY, Com.warrs]) (by simp [skipK, forUp, stepY, Com.NoWrite])
    (by simp [skipK, forUp, stepY, Com.reads])⟩
  intro z hz; simp [skipK, forUp, stepY, Com.wvars] at hz ⊢; tauto

theorem toWord_words_cons (ws : List (List ℕ)) : toWord ws = [ws.length] ++ frames ws := by
  rw [toWord_words]; rfl

theorem length_toWord_eq (ws : List (List ℕ)) : (toWord ws).length = (frames ws).length + 1 := by
  rw [toWord_words]; simp

theorem drop_succ_of_toWord {X : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : X.drop p = toWord ws ++ r) : X.drop (p + 1) = frames ws ++ r := by
  have := drop_add_of_drop (u := [ws.length]) (r := frames ws ++ r) (by rw [hx, toWord_words]; rfl)
  simpa using this

theorem skipL_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : (σ.arrs "x").drop p = toWord ws ++ r) (hy : σ.vars "y" = p) (hp : p + (toWord ws).length ≤ M) :
    ∃ σ', Run (W + 1) skipL σ σ' (20 * ws.length + 30) ∧ σ'.vars "y" = p + (toWord ws).length ∧
      OFr σ σ' ["y", "sn", "sk"] := by
  have hroom := hC.room
  have hm16 := hC.m16
  have hlt := length_toWord_eq ws
  have h0 : xg (σ.arrs "x") p = ws.length := xg_of_drop (by rw [hx, toWord_words]; rfl)
  have hfl := length_frames ws
  have r1 := Run.assign (x := "sn") (evalB_xvar hC (y := "y") (by omega))
  rw [hy, h0] at r1
  set σ1 := σ.setVar "sn" ws.length with hσ1
  have hC1 : Ctx W M σ1 := hC.setVar (by decide) _
  have hy1 : σ1.vars "y" = p := by simp [hσ1, hy]
  have r2 := Run.assign (σ := σ1) (x := "y") (e := .add (V "y") (N 1)) (v := p + 1)
    (by have := evalB_bin (op := .add) (evalB_var (B := W + 1) (x := "y") (σ := σ1) (by omega))
          (evalB_lit (B := W + 1) (n := 1) (σ := σ1) (by omega)) (by simp only [Bop.apply_add]; omega)
        rw [this]; simp [hy1])
  set σ2 := σ1.setVar "y" (p + 1) with hσ2
  have hC2 : Ctx W M σ2 := hC1.setVar (by decide) _
  have hx2 : (σ2.arrs "x").drop (p + 1) = frames ws ++ r := by
    simp only [hσ2, hσ1, arrs_setVar]; exact drop_succ_of_toWord hx
  obtain ⟨σ3, r3, hy3, hf3⟩ := skipK_run (k := "sn") (by decide) hC2 hx2 (by simp [hσ2, hσ1])
    (by simp [hσ2, hσ1]) (by omega)
  have hsn : σ2.vars "sn" = ws.length := by simp [hσ2, hσ1]
  rw [hsn] at r3 hy3
  obtain ⟨e1, -⟩ := skipFr_frames hx2 (j := ws.length) le_rfl
  refine ⟨σ3, ?_, ?_, ?_⟩
  · show Run (W + 1) (.seq _ (.seq _ _)) σ σ3 _
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp [Expr.size]; omega)
  · rw [hy3, e1, List.take_length]; omega
  · have := ((OFr.setVar σ "sn" ws.length).trans (OFr.setVar σ1 "y" (p + 1))).trans hf3
    exact this.mono (by intro z hz; simp at hz ⊢; tauto)

theorem skipNode_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {p h l : ℕ} (t : Node h l) {r : List ℕ}
    (hx : (σ.arrs "x").drop p = toWord t ++ r) (hy : σ.vars "y" = p) (hd : σ.vars "dd" = h)
    (hh : h < M) (hp : p + (toWord t).length ≤ M) :
    ∃ σ', Run (W + 1) skipNode σ σ' (40 * (toWord t).length + 80) ∧
      σ'.vars "y" = p + (toWord t).length ∧ OFr σ σ' ["y", "sn", "sk"] := by
  have hroom := hC.room
  have hm16 := hC.m16
  cases h with
  | zero =>
    rw [toWord_node_zero] at hx hp ⊢
    have hc := count_lt_toWord (Node.atoms t).words
    obtain ⟨σ1, r1, hy1, hf1⟩ := skipL_run hC hx hy hp
    have hd1 : σ1.vars "dd" = 0 := by rw [hf1.vars "dd" (by decide), hd]
    have hb : (Cond.eq (V "dd") (N 0)).evalB (W + 1) σ1 = some true := by
      rw [evalB_condEq (evalB_var (by rw [hd1]; omega)) (evalB_lit (by omega)), hd1]; rfl
    refine ⟨σ1, ?_, hy1, hf1⟩
    exact (Run.seq r1 (Run.ite_true hb Run.skip)).mono (by simp only [Cond.size, Expr.size]; omega)
  | succ h =>
    rw [toWord_node_succ] at hx hp ⊢
    rw [List.append_assoc] at hx
    have hc1 := count_lt_toWord (Node.atoms t).words
    have hc2 := count_lt_toWord (Node.exts t).words
    simp only [List.length_append] at hp ⊢
    obtain ⟨σ1, r1, hy1, hf1⟩ := skipL_run hC hx hy (by omega)
    have hC1 : Ctx W M σ1 := hC.ofr hf1 (by decide)
    have hd1 : σ1.vars "dd" = h + 1 := by rw [hf1.vars "dd" (by decide), hd]
    have hb : (Cond.eq (V "dd") (N 0)).evalB (W + 1) σ1 = some false := by
      rw [evalB_condEq (evalB_var (by rw [hd1]; omega)) (evalB_lit (by omega)), hd1]; rfl
    have hx1 : (σ1.arrs "x").drop (p + (toWord (Node.atoms t).words).length) =
        toWord (Node.exts t).words ++ r := by
      rw [hf1.arrs "x" (by decide)]; exact drop_add_of_drop hx
    obtain ⟨σ2, r2, hy2, hf2⟩ := skipL_run hC1 hx1 hy1 (by omega)
    refine ⟨σ2, ?_, by rw [hy2]; omega, (hf1.trans hf2).mono (by intro z hz; simp at hz ⊢; tauto)⟩
    exact (Run.seq r1 (Run.ite_false hb r2)).mono (by simp only [Cond.size, Expr.size]; omega)

theorem extsAt_run {W M : ℕ} {σ : Env} {s cnt : String} (hc : cnt ∉ ["y", "sn", "sk", "W"])
    (hC : Ctx W M σ) {h l : ℕ} (t : Node (h + 1) l) {r : List ℕ}
    (hx : (σ.arrs "x").drop (σ.vars s) = toWord t ++ r) (hp : σ.vars s + (toWord t).length ≤ M) :
    ∃ σ', Run (W + 1) (extsAt s cnt) σ σ' (40 * (toWord t).length + 80) ∧
      σ'.vars "y" = σ.vars s + (toWord (Node.atoms t).words).length ∧
      σ'.vars cnt = (Node.exts t).words.length ∧
      (σ.arrs "x").drop (σ'.vars "y") = toWord (Node.exts t).words ++ r ∧
      OFr σ σ' ["y", "sn", "sk", cnt] := by
  have hroom := hC.room
  have hm16 := hC.m16
  have htl : (toWord t).length = (toWord (Node.atoms t).words).length +
      (toWord (Node.exts t).words).length := by rw [toWord_node_succ, List.length_append]
  rw [toWord_node_succ, List.append_assoc] at hx
  rw [toWord_node_succ, List.length_append] at hp
  have hc1 := count_lt_toWord (Node.atoms t).words
  have hc2 := count_lt_toWord (Node.exts t).words
  have r1 := Run.assign (x := "y") (evalB_var (B := W + 1) (x := s) (σ := σ) (by omega))
  set σ1 := σ.setVar "y" (σ.vars s) with hσ1
  have hC1 : Ctx W M σ1 := hC.setVar (by decide) _
  obtain ⟨σ2, r2, hy2, hf2⟩ := skipL_run hC1 (p := σ.vars s) (by simp only [hσ1, arrs_setVar]; exact hx)
    (by simp only [hσ1, vars_setVar, if_true]) (by omega)
  have hC2 : Ctx W M σ2 := hC1.ofr hf2 (by decide)
  have hx2 : (σ2.arrs "x").drop (σ2.vars "y") = toWord (Node.exts t).words ++ r := by
    rw [hf2.arrs "x" (by decide), hy2]; simp only [hσ1, arrs_setVar]; exact drop_add_of_drop hx
  have h0 : xg (σ2.arrs "x") (σ2.vars "y") = (Node.exts t).words.length :=
    xg_of_drop (by rw [hx2, toWord_words]; rfl)
  have r3 := Run.assign (x := cnt) (evalB_xvar hC2 (y := "y") (by rw [hy2]; omega))
  rw [h0] at r3
  have hcy : cnt ≠ "y" := fun e => hc (by simp [e])
  refine ⟨σ2.setVar cnt (Node.exts t).words.length, ?_, by simp only [vars_setVar, if_neg (Ne.symm hcy)]; exact hy2, by simp, ?_, ?_⟩
  · show Run (W + 1) (.seq _ (.seq _ _)) σ _ _
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp only [Expr.size]; omega)
  · have := hx2; rw [hf2.arrs "x" (by decide)] at this; simp only [hσ1, arrs_setVar] at this
    simp only [vars_setVar, if_neg (Ne.symm hcy)]; exact this
  · have := ((OFr.setVar σ "y" (σ.vars s)).trans hf2).trans (OFr.setVar σ2 cnt (Node.exts t).words.length)
    exact this.mono (by intro z hz; simp at hz ⊢; tauto)

theorem extFr_run {W M : ℕ} {σ : Env} {k : String} (hk : k ∉ ["y", "sk"]) (hC : Ctx W M σ)
    {ws : List (List ℕ)} {r : List ℕ} (hx : (σ.arrs "x").drop (σ.vars "y") = toWord ws ++ r)
    (hK : σ.vars k < ws.length) (hp : σ.vars "y" + (toWord ws).length ≤ M) :
    ∃ σ', Run (W + 1) (extFr k) σ σ' (20 * ws.length + 20) ∧
      σ'.vars "y" = frPos (σ.arrs "x") (σ.vars "y") (σ.vars k) ∧
      xg (σ.arrs "x") (σ'.vars "y") = (ws[σ.vars k]'hK).length ∧
      (σ.arrs "x").drop (σ'.vars "y" + 1) = ws[σ.vars k]'hK ++ (frames (ws.drop (σ.vars k + 1)) ++ r) ∧
      σ'.vars "y" + 1 + (ws[σ.vars k]'hK).length ≤ σ.vars "y" + (toWord ws).length ∧
      OFr σ σ' ["y", "sk"] := by
  have hroom := hC.room
  have hm16 := hC.m16
  have hky : k ≠ "y" := fun e => hk (by simp [e])
  obtain ⟨X, hX⟩ : ∃ X, σ.arrs "x" = X := ⟨_, rfl⟩
  obtain ⟨p, hp0⟩ : ∃ p, σ.vars "y" = p := ⟨_, rfl⟩
  obtain ⟨K, hK0⟩ : ∃ K, σ.vars k = K := ⟨_, rfl⟩
  rw [hX, hp0] at hx
  rw [hp0] at hp
  subst hK0
  have hlt := length_toWord_eq ws
  have r1 := Run.assign (σ := σ) (x := "y") (e := .add (V "y") (N 1)) (v := p + 1)
    (by have := evalB_bin (op := .add) (evalB_var (B := W + 1) (x := "y") (σ := σ) (by omega))
          (evalB_lit (B := W + 1) (n := 1) (σ := σ) (by omega)) (by simp only [Bop.apply_add]; omega)
        rw [this]; simp [hp0])
  set σ1 := σ.setVar "y" (p + 1) with hσ1
  have hC1 : Ctx W M σ1 := hC.setVar (by decide) _
  have hx1 : (σ1.arrs "x").drop (p + 1) = frames ws ++ r := by
    simp only [hσ1, arrs_setVar, hX]; exact drop_succ_of_toWord hx
  obtain ⟨σ2, r2, hy2, hf2⟩ := skipK_run (k := k) hk hC1 hx1 (by simp [hσ1]) (by simp [hσ1, hky]; omega)
    (by omega)
  have hk1 : σ1.vars k = σ.vars k := by simp [hσ1, hky]
  rw [hk1] at r2 hy2
  have hx1' : σ1.arrs "x" = X := by simp [hσ1, hX]
  rw [hx1'] at hy2
  obtain ⟨-, hpos, hget, -, -⟩ := listAt hx
  obtain ⟨e1, -⟩ := hpos (σ.vars k + 1) hK
  obtain ⟨e0, -⟩ := hpos (σ.vars k) hK.le
  obtain ⟨g1, -, g3⟩ := hget (σ.vars k) hK
  have hs := length_frames_take_succ hK
  have hle := length_frames_take_le ws (σ.vars k + 1)
  have hyfr : σ2.vars "y" = frPos X p (σ.vars k) := hy2
  refine ⟨σ2, ?_, by rw [hX, hp0]; exact hyfr, by rw [hX, hyfr]; exact g1, by rw [hX, hyfr]; exact g3,
    ?_, (OFr.setVar σ "y" (p + 1)).trans hf2 |>.mono (by intro z hz; simp at hz ⊢; tauto)⟩
  · show Run (W + 1) (.seq _ _) σ _ _
    exact (Run.seq r1 r2).mono (by simp [Expr.size]; omega)
  · rw [hyfr, e0, hp0]; omega

/-! ### The words of the stack -/

/-- The facts about word `j` of the stack in `x`. -/
theorem wordAt {X : List ℕ} {ws : List (List ℕ)} {r : List ℕ} (hx : X.drop 2 = toWord ws ++ r) {j : ℕ}
    (hj : j < ws.length) :
    xg X (frPos X 2 j) = ws[j].length ∧ seg X (frPos X 2 j + 1) ws[j].length = ws[j] ∧
      frPos X 2 j + 1 + ws[j].length ≤ 2 + (toWord ws).length ∧
      (∀ m, m < ws[j].length → xg X (frPos X 2 j + 1 + m) = ws[j].getD m 0) := by
  obtain ⟨-, hpos, hget, -, -⟩ := listAt hx
  obtain ⟨g1, -, g3⟩ := hget j hj
  obtain ⟨e1, -⟩ := hpos (j + 1) hj
  obtain ⟨e0, -⟩ := hpos j hj.le
  have hs := length_frames_take_succ hj
  have hle := length_frames_take_le ws (j + 1)
  have hlt := length_toWord_eq ws
  refine ⟨g1, by simp [seg, g3], by omega, fun m hm => ?_⟩
  have : X.drop (frPos X 2 j + 1 + m) = ws[j].drop m ++ (frames (ws.drop (j + 1)) ++ r) := by
    rw [← List.drop_drop, g3, List.drop_append_of_le_length (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  exact xg_of_drop (by rw [this, List.drop_eq_getElem_cons hm]; rfl)

theorem locW_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {ws : List (List ℕ)} {r : List ℕ}
    (hx : (σ.arrs "x").drop 2 = toWord ws ++ r) (hnb : σ.vars "nb" ≤ ws.length) (h14 : σ.vars "nb" ≤ 14)
    (hp : 2 + (toWord ws).length ≤ M) :
    ∃ σ', Run (W + 1) locW σ σ' 600 ∧
      (∀ i < σ.vars "nb", (σ'.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i) ∧
      (∀ y, y ∉ ["y", "wi"] → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "wp" → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs "wp").length = (σ.arrs "wp").length ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hroom := hC.room
  have hm16 := hC.m16
  obtain ⟨X, hX⟩ : ∃ X, σ.arrs "x" = X := ⟨_, rfl⟩
  obtain ⟨nb, hnb0⟩ : ∃ nb, σ.vars "nb" = nb := ⟨_, rfl⟩
  rw [hX] at hx ⊢
  rw [hnb0] at hnb h14 ⊢
  have hx3 : X.drop 3 = frames ws ++ r := drop_succ_of_toWord hx
  have hlt := length_toWord_eq ws
  have r0 := Run.assign (σ := σ) (x := "y") (evalB_lit (B := W + 1) (n := 3) (σ := σ) (by omega))
  set σ0 := σ.setVar "y" 3 with hσ0
  let I : ℕ → Env → Prop := fun k τ => τ.vars "nb" = nb ∧ Ctx W M τ ∧ τ.arrs "x" = X ∧
    τ.vars "y" = frPos X 2 k ∧ (∀ i < k, (τ.arrs "wp").getD i 0 = frPos X 2 i) ∧
    (∀ y, y ∉ ["y", "wi"] → τ.vars y = σ.vars y) ∧ (∀ a, a ≠ "wp" → τ.arrs a = σ.arrs a) ∧
    τ.out = σ.out ∧ τ.inp = σ.inp
  obtain ⟨σ', r1, hI, -⟩ := forUp_run (B := W + 1) (i := "wi") (e := V "nb")
    (body := .seq (.store "wp" (V "wi") (V "y")) stepY) (N := nb) (K := 12) I (σ := σ0) (by omega)
    (fun k _ τ hI _ => by rw [← hI.1]; exact evalB_var (by rw [hI.1]; omega))
    ⟨by simp [hσ0, hnb0], (hC.setVar (by decide) _).setVar (by decide) _, by simp [hσ0, hX],
      by simp [hσ0, frPos, skipFr], fun i hi => absurd hi (Nat.not_lt_zero _),
      fun y hy => by simp only [hσ0, vars_setVar]; rw [if_neg (fun h => hy (by simp [h])),
        if_neg (fun h => hy (by simp [h]))], fun a _ => rfl, rfl, rfl⟩
    (by
      intro k hk τ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hwi
      have hkw : k < ws.length := by omega
      obtain ⟨e1, e2⟩ := skipFr_frames hx3 (j := k) hkw.le
      rw [frames_drop hkw] at e2
      have hxg : xg X (skipFr X 3 k) = ws[k].length := xg_of_drop (by rw [e2]; rfl)
      have hs := length_frames_take_succ hkw
      have hle := length_frames_take_le ws (k + 1)
      have hfr : frPos X 2 k = skipFr X 3 k := rfl
      have hwl := h2.wl
      have rs := Run.store (B := W + 1) (σ := τ) (a := "wp") (i := V "wi") (e := V "y") (idx := k)
        (v := frPos X 2 k) (by rw [← hwi]; exact evalB_var (by rw [hwi]; omega))
        (by rw [← h4]; exact evalB_var (by rw [h4, hfr, e1]; omega)) (by rw [hwl]; omega)
      set τ1 := τ.setArr "wp" k (frPos X 2 k) with hτ1
      have hC1 : Ctx W M τ1 := ⟨by simp [hτ1, h2.hW], by simp [hτ1, h2.xl], by simp [hτ1, h2.ol],
        by simp [hτ1, hwl], by simp only [hτ1, arrs_setArr]; exact h2.xv, h2.m16, h2.room⟩
      have hy1 : τ1.vars "y" = frPos X 2 k := by simp [hτ1, h4]
      have hx1 : τ1.arrs "x" = X := by simp [hτ1, h3]
      have r2 := stepY_run hC1 hy1 (by rw [hx1, hfr, hxg, e1]; omega)
      rw [hx1, hfr, hxg] at r2
      have hst := skipFr_succ' X 3 k
      refine ⟨_, (Run.seq rs r2).mono (by simp [Expr.size]), by simp [hτ1, hwi], ?_⟩
      refine ⟨by simp [hτ1, h1], (hC1.setVar (by decide) _).setVar (by decide) _, by simp [hτ1, h3],
        ?_, fun i hi => ?_, fun y hy => ?_, fun a ha => ?_, by simp [hτ1, h8], by simp [hτ1, h9]⟩
      · simp only [vars_setVar, if_neg (show ("y" : String) ≠ "wi" by decide), if_true, hx1]
        show _ = skipFr X 3 (k + 1)
        rw [hst, ← hfr, hfr, hxg]; omega
      · simp only [arrs_setVar, hτ1, arrs_setArr, if_true]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hik : k = i
        · subst hik; simp [hwl, show k < W + 1 by omega]
        · rw [if_neg hik, ← List.getD_eq_getElem?_getD]; exact h5 i (by omega)
      · simp only [vars_setVar, hτ1, vars_setArr]
        rw [if_neg (fun h => hy (by simp [h])), if_neg (fun h => hy (by simp [h]))]; exact h6 y hy
      · simp only [arrs_setVar, hτ1, arrs_setArr, if_neg ha]; exact h7 a ha)
  obtain ⟨-, hC', -, -, hwp', hv', ha', ho', hi'⟩ := hI
  refine ⟨σ', (Run.seq r0 r1).mono (by simp [Expr.size]; omega), hwp', hv', ha', ?_, ho', hi'⟩
  rw [hC'.wl, hC.wl]

/-! ### Loading a frame -/

/-- Expressions that do not read scalars. -/
def NoVar : Expr → Prop
  | .lit _ => True
  | .var _ => False
  | .get _ i => NoVar i
  | .bin _ e f => NoVar e ∧ NoVar f

theorem evalB_noVar {B : ℕ} {σ τ : Env} (h : τ.arrs = σ.arrs) :
    ∀ {e : Expr}, NoVar e → e.evalB B τ = e.evalB B σ
  | .lit _, _ => rfl
  | .var _, hv => hv.elim
  | .get a i, hv => by simp only [Expr.evalB, evalB_noVar h (e := i) hv, h]
  | .bin _ e f, hv => by simp only [Expr.evalB, evalB_noVar h hv.1, evalB_noVar h hv.2]

theorem evalB_wp {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {j P : ℕ} (hj : j < M)
    (hwp : (σ.arrs "wp").getD j 0 = P) (hP : P ≤ M) :
    (Expr.get "wp" (N j)).evalB (W + 1) σ = some P := by
  have hroom := hC.room
  have hm16 := hC.m16
  have hl := hC.wl
  refine evalB_get (evalB_lit (by omega)) ?_ (by omega)
  rw [← hwp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

theorem num_run {W M : ℕ} {σ τ : Env} (hC : Ctx W M σ) (hτ : τ.arrs = σ.arrs) {j P : ℕ} (c : ℕ)
    (hj : j < M) (hc : c ≤ 6) (hwp : (σ.arrs "wp").getD j 0 = P) (hP : P + c ≤ M) (g : String) :
    Run (W + 1) (asg g (X (.add (.get "wp" (N j)) (N c)))) τ
      (τ.setVar g (xg (σ.arrs "x") (P + c))) 6 := by
  have hroom := hC.room
  have hm16 := hC.m16
  have he : (X (.add (.get "wp" (N j)) (N c))).evalB (W + 1) σ = some (xg (σ.arrs "x") (P + c)) :=
    evalB_xe hC (evalB_bin (evalB_wp hC hj hwp (by omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply_add]; omega)) (by omega)
  rw [← evalB_noVar hτ (by simp [NoVar])] at he
  exact (Run.assign he).mono (by simp [Expr.size])

theorem ldW_run {W M : ℕ} {σ τ : Env} (hC : Ctx W M σ) (hτ : τ.arrs = σ.arrs) {j P : ℕ}
    (hj : j < M) (hwp : (σ.arrs "wp").getD j 0 = P) (hP : P + 1 ≤ M) (s l : String) :
    Run (W + 1) (ldW j s l) τ ((τ.setVar s (P + 1)).setVar l (xg (σ.arrs "x") P)) 10 := by
  have hroom := hC.room
  have hm16 := hC.m16
  have he1 : (Expr.add (.get "wp" (N j)) (N 1)).evalB (W + 1) σ = some (P + 1) :=
    evalB_bin (evalB_wp hC hj hwp (by omega)) (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
  have he2 : (X (.get "wp" (N j))).evalB (W + 1) σ = some (xg (σ.arrs "x") P) :=
    evalB_xe hC (evalB_wp hC hj hwp (by omega)) (by omega)
  rw [← evalB_noVar hτ (by simp [NoVar])] at he1
  rw [← evalB_noVar (τ := τ.setVar s (P + 1)) (by simp [hτ]) (by simp [NoVar])] at he2
  exact (Run.seq (Run.assign he1) (Run.assign he2)).mono (by simp [Expr.size])

theorem getElem_of_take_drop {ws : List (List ℕ)} {w : ℕ} {L : List (List ℕ)}
    (hf : (ws.drop w).take 7 = L) {m : ℕ} (hm : m < 7) (hj : w + m < ws.length) :
    ws[w + m] = L.getD m [] := by
  have : ((ws.drop w).take 7)[m]? = L[m]? := by rw [hf]
  rw [List.getElem?_take, if_pos hm, List.getElem?_drop, List.getElem?_eq_getElem hj] at this
  rw [List.getD_eq_getElem?_getD, ← this]; rfl

/-- The scalars written by `ldG`. -/
def ldGVars : List String :=
  ["gd", "gk", "g1", "g2", "gp", "gi", "gAs", "gAl", "gBs", "gBl", "gSs", "gSl", "gTs", "gTl", "gUs",
    "gUl", "gEs", "gEl", "gx"]

private theorem segIs_of {M : ℕ} {τ : Env} {s l : String} {u : List ℕ} {P : ℕ} (hs : τ.vars s = P + 1)
    (hl : τ.vars l = u.length) (hseg : seg (τ.arrs "x") (P + 1) u.length = u) (hP : P + 1 + u.length ≤ M) :
    SegIs M τ s l u := ⟨hl, by rw [hs]; exact hP, by rw [hs]; exact hseg⟩

set_option maxHeartbeats 1000000 in
theorem ldG_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {ws : List (List ℕ)} {r : List ℕ}
    (hx : (σ.arrs "x").drop 2 = toWord ws ++ r) (hp : 2 + (toWord ws).length ≤ M) (w : ℕ) (f : Fr)
    (hw : w + 7 ≤ ws.length) (hf : (ws.drop w).take 7 = frWords f)
    (hwp : ∀ i < w + 7, (σ.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i) :
    ∃ σ', Run (W + 1) (ldG w) σ σ' 300 ∧ SlotIs M σ' f ∧ σ'.vars "gx" = 0 ∧ OFr σ σ' ldGVars := by
  have hroom := hC.room
  have hm16 := hC.m16
  obtain ⟨X, hX⟩ : ∃ X, σ.arrs "x" = X := ⟨_, rfl⟩
  rw [hX] at hx hwp
  have hxM : ∀ i, xg X i < M := fun i => by rw [← hX]; exact xg_lt_M hC i
  have wA : ∀ m, m < 7 → w + m < ws.length := fun m hm => by omega
  have e0 := getElem_of_take_drop hf (m := 0) (by omega) (wA 0 (by omega))
  have e1 := getElem_of_take_drop hf (m := 1) (by omega) (wA 1 (by omega))
  have e2 := getElem_of_take_drop hf (m := 2) (by omega) (wA 2 (by omega))
  have e3 := getElem_of_take_drop hf (m := 3) (by omega) (wA 3 (by omega))
  have e4 := getElem_of_take_drop hf (m := 4) (by omega) (wA 4 (by omega))
  have e5 := getElem_of_take_drop hf (m := 5) (by omega) (wA 5 (by omega))
  have e6 := getElem_of_take_drop hf (m := 6) (by omega) (wA 6 (by omega))
  simp only [frWords, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6
  obtain ⟨a0, -, c0, n0⟩ := wordAt hx (wA 0 (by omega))
  obtain ⟨a1, b1, c1, -⟩ := wordAt hx (wA 1 (by omega))
  obtain ⟨a2, b2, c2, -⟩ := wordAt hx (wA 2 (by omega))
  obtain ⟨a3, b3, c3, -⟩ := wordAt hx (wA 3 (by omega))
  obtain ⟨a4, b4, c4, -⟩ := wordAt hx (wA 4 (by omega))
  obtain ⟨a5, b5, c5, -⟩ := wordAt hx (wA 5 (by omega))
  obtain ⟨a6, b6, c6, -⟩ := wordAt hx (wA 6 (by omega))
  simp only [Nat.add_zero] at a0 c0 n0
  rw [e0] at a0 c0 n0
  rw [e1] at a1 b1 c1
  rw [e2] at a2 b2 c2
  rw [e3] at a3 b3 c3
  rw [e4] at a4 b4 c4
  rw [e5] at a5 b5 c5
  rw [e6] at a6 b6 c6
  simp only [List.length_cons, List.length_nil] at a0 c0 n0
  have hn : ∀ m, m < 6 → xg X (frPos X 2 w + (m + 1)) =
      [f.d, f.kk, f.l1, f.l2, f.ph, f.i].getD m 0 := fun m hm => by
    rw [show frPos X 2 w + (m + 1) = frPos X 2 w + 1 + m by omega]; exact n0 m (by simp; omega)
  have q0 := hwp w (by omega)
  have q1 := hwp (w + 1) (by omega)
  have q2 := hwp (w + 2) (by omega)
  have q3 := hwp (w + 3) (by omega)
  have q4 := hwp (w + 4) (by omega)
  have q5 := hwp (w + 5) (by omega)
  have q6 := hwp (w + 6) (by omega)
  have hwM : w + 7 ≤ M := by have := count_lt_toWord ws; omega
  refine ⟨?w, ?r, ?s, ?g, ?o⟩
  case r =>
    simp only [ldG, seqs]
    refine Run.mono (K := 98) (K' := 300) ?_ (by norm_num)
    exact (Run.seq (num_run hC (by rfl) 1 (by omega) (by omega) q0 (by omega) "gd")
      (Run.seq (num_run hC (by rfl) 2 (by omega) (by omega) q0 (by omega) "gk")
      (Run.seq (num_run hC (by rfl) 3 (by omega) (by omega) q0 (by omega) "g1")
      (Run.seq (num_run hC (by rfl) 4 (by omega) (by omega) q0 (by omega) "g2")
      (Run.seq (num_run hC (by rfl) 5 (by omega) (by omega) q0 (by omega) "gp")
      (Run.seq (num_run hC (by rfl) 6 (by omega) (by omega) q0 (by omega) "gi")
      (Run.seq (ldW_run hC (by rfl) (by omega) q1 (by omega) "gAs" "gAl")
      (Run.seq (ldW_run hC (by rfl) (by omega) q2 (by omega) "gBs" "gBl")
      (Run.seq (ldW_run hC (by rfl) (by omega) q3 (by omega) "gSs" "gSl")
      (Run.seq (ldW_run hC (by rfl) (by omega) q4 (by omega) "gTs" "gTl")
      (Run.seq (ldW_run hC (by rfl) (by omega) q5 (by omega) "gUs" "gUl")
      (Run.seq (ldW_run hC (by rfl) (by omega) q6 (by omega) "gEs" "gEl")
        (Run.assign (x := "gx") (evalB_lit (n := 0) (by omega)))))))))))))))
  case s =>
    have g0 := hn 0 (by omega)
    have g1 := hn 1 (by omega)
    have g2 := hn 2 (by omega)
    have g3 := hn 3 (by omega)
    have g4 := hn 4 (by omega)
    have g5 := hn 5 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, zero_add] at g0 g1 g2 g3 g4 g5
    have m0 := hxM (frPos X 2 w + 1)
    have m1 := hxM (frPos X 2 w + 2)
    have m2 := hxM (frPos X 2 w + 3)
    have m3 := hxM (frPos X 2 w + 4)
    have m4 := hxM (frPos X 2 w + 5)
    have m5 := hxM (frPos X 2 w + 6)
    rw [g0] at m0; rw [g1] at m1; rw [g2] at m2; rw [g3] at m3; rw [g4] at m4; rw [g5] at m5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ?_, ?_, ?_, ?_, ?_, Or.inl ⟨by simp, ?_⟩⟩
    · simp [hX, g0]
    · simp [hX, g1]
    · simp [hX, g2]
    · simp [hX, g3]
    · simp [hX, g4]
    · simp [hX, g5]
    · exact segIs_of (P := frPos X 2 (w + 1)) (by simp) (by simp [hX, a1]) (by simp [hX, b1]) (by omega)
    · exact segIs_of (P := frPos X 2 (w + 2)) (by simp) (by simp [hX, a2]) (by simp [hX, b2]) (by omega)
    · exact segIs_of (P := frPos X 2 (w + 3)) (by simp) (by simp [hX, a3]) (by simp [hX, b3]) (by omega)
    · exact segIs_of (P := frPos X 2 (w + 4)) (by simp) (by simp [hX, a4]) (by simp [hX, b4]) (by omega)
    · exact segIs_of (P := frPos X 2 (w + 5)) (by simp) (by simp [hX, a5]) (by simp [hX, b5]) (by omega)
    · exact segIs_of (P := frPos X 2 (w + 6)) (by simp) (by simp [hX, a6]) (by simp [hX, b6]) (by omega)
  case g => simp
  case o =>
    refine ⟨fun y hy => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [ldGVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hy]


theorem length_frames_take_drop (ws : List (List ℕ)) (j : ℕ) :
    (frames ws).length = (frames (ws.take j)).length + (frames (ws.drop j)).length := by
  conv_lhs => rw [← List.take_append_drop j ws, frames_append, List.length_append]

theorem ldRest_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {ws : List (List ℕ)} {r : List ℕ}
    (hx : (σ.arrs "x").drop 2 = toWord ws ++ r) (hp : 2 + (toWord ws).length ≤ M) (c : ℕ) (hc : 1 ≤ c)
    (hcw : 7 * c ≤ ws.length) (hL : σ.vars "L" = 2 + (toWord ws).length) (hn : σ.vars "n" = ws.length)
    (hwp : (σ.arrs "wp").getD (7 * c - 1) 0 = frPos (σ.arrs "x") 2 (7 * c - 1)) :
    ∃ σ', Run (W + 1) (ldRest c) σ σ' 50 ∧ SegIs M σ' "rS" "rL" (frames (ws.drop (7 * c))) ∧
      σ'.vars "cnt" = ws.length - 7 * c ∧ OFr σ σ' ["rS", "rL", "cnt"] := by
  have hroom := hC.room
  have hm16 := hC.m16
  obtain ⟨X, hX⟩ : ∃ X, σ.arrs "x" = X := ⟨_, rfl⟩
  rw [hX] at hx hwp
  obtain ⟨j, hj⟩ : ∃ j, 7 * c - 1 = j := ⟨_, rfl⟩
  have hjc : 7 * c = j + 1 := by omega
  rw [hj] at hwp
  rw [hjc] at hcw ⊢
  have hjw : j < ws.length := by omega
  obtain ⟨-, hpos, -, -, -⟩ := listAt hx
  obtain ⟨a0, -, c0, -⟩ := wordAt hx hjw
  obtain ⟨f1, f2⟩ := hpos (j + 1) hcw
  obtain ⟨f0, -⟩ := hpos j hjw.le
  have hs := length_frames_take_succ hjw
  have htd := length_frames_take_drop ws (j + 1)
  have hlt := length_toWord_eq ws
  have hcl := count_lt_toWord ws
  have hP : frPos X 2 (j + 1) = frPos X 2 j + xg X (frPos X 2 j) + 1 := by rw [a0, f1, f0]; omega
  have hev : (Expr.add (.add (.get "wp" (N j)) (Expr.get "x" (.get "wp" (N j)))) (N 1)).evalB (W + 1) σ =
      some (frPos X 2 (j + 1)) := by
    rw [hP]
    have h1 := evalB_wp hC (j := j) (by omega) hwp (by omega)
    have h2 := evalB_xe hC h1 (by omega)
    rw [hX] at h2
    exact evalB_bin (evalB_bin h1 h2 (by simp only [Bop.apply_add]; rw [a0]; omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply_add]; rw [a0]; omega)
  have r1 := Run.assign (x := "rS") hev
  set σ1 := σ.setVar "rS" (frPos X 2 (j + 1)) with hσ1
  have r2 := Run.assign (σ := σ1) (x := "rL") (e := .sub (V "L") (V "rS"))
    (v := (frames (ws.drop (j + 1))).length)
    (by have := evalB_bin (op := .sub) (evalB_var (B := W + 1) (x := "L") (σ := σ1)
          (by simp [hσ1, hL]; omega)) (evalB_var (B := W + 1) (x := "rS") (σ := σ1) (by simp [hσ1]; omega))
          (by simp [hσ1, hL]; omega)
        rw [this]; simp [hσ1, hL]; omega)
  set σ2 := σ1.setVar "rL" (frames (ws.drop (j + 1))).length with hσ2
  have r3 := Run.assign (σ := σ2) (x := "cnt") (e := .sub (V "n") (N (j + 1))) (v := ws.length - (j + 1))
    (by have := evalB_bin (op := .sub) (evalB_var (B := W + 1) (x := "n") (σ := σ2)
          (by simp [hσ2, hσ1, hn]; omega)) (evalB_lit (B := W + 1) (n := j + 1) (σ := σ2) (by omega))
          (by simp [hσ2, hσ1, hn]; omega)
        rw [this]; simp [hσ2, hσ1, hn])
  refine ⟨σ2.setVar "cnt" (ws.length - (j + 1)), ?_, ⟨by simp [hσ2], ?_, ?_⟩, by simp, ?_⟩
  · simp only [ldRest, seqs, hj, hjc]
    exact (Run.seq r1 (Run.seq r2 r3)).mono (by simp [Expr.size])
  · simp [hσ2, hσ1]; omega
  · simp only [vars_setVar, arrs_setVar, hσ2, hσ1, hX]; simp [seg, f2]
  · exact ((OFr.setVar σ "rS" _).trans (OFr.setVar σ1 "rL" _)).trans (OFr.setVar σ2 "cnt" _)

end Lax185574Proofs.CompRam
