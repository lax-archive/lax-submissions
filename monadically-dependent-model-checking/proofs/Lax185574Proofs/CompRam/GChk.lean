import Lax185574Proofs.CompRam.GBuilt

/-!
The checks and the output of the glue command of lem:compose.

`guardQ` checks the guard of the query of the working callee, by the
kind `qk` of the query (`guardQ_run`). `roundTest` checks
`(2 jr + 2)^4` on the cell just behind the buffer (`roundTest_run`).
`wrOut` writes the buffer with `dSq` after `sp` cells if `dq = 1`, and
sets `ovf` if an entry of the buffer is not below `Ob = W / 2^20 + 1`
(`wrOut_run`). Every value that a bounded run stores is below the bound
(`Run.arrs_lt`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding

theorem BigStepB.arrs_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k)
    (hσ : ∀ a, ∀ v ∈ σ.arrs a, v < B) : ∀ a, ∀ v ∈ σ'.arrs a, v < B := by
  induction h with
  | skip => exact hσ
  | assign _ => exact hσ
  | @store σ a i e k v _ he _ =>
      intro b u hu
      simp only [Env.setArr] at hu
      split_ifs at hu with hb
      · rcases List.mem_or_eq_of_mem_set hu with h1 | h1
        · exact hσ a u h1
        · rw [h1]; exact (Expr.eval_and_lt_of_evalB he).2
      · exact hσ b u hu
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read _ => exact hσ
  | write _ => exact hσ

theorem Run.arrs_lt {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hσ : ∀ a, ∀ v ∈ σ.arrs a, v < B) : ∀ a, ∀ v ∈ σ'.arrs a, v < B := by
  obtain ⟨_, _, hbs⟩ := h; exact BigStepB.arrs_lt hbs hσ

/-- The guard of the query of an outcome, as `guardChk` tests it. -/
def GOK (eR eS eC d W : ℕ) : Res → Prop
  | .call _ q => min (((realQ q).length + maxEntry (realQ q) + 1) ^ (expQ eR eS eC q + 1)) W ≤
      W / min (2 ^ d) W
  | _ => True

theorem seg_arr_of_filled {l : List ℕ} {τ : Env} (h : Filled "OB" "po" l τ) {s N : ℕ}
    (hs : s + N ≤ l.length) : seg (τ.arrs "OB") s N = seg l s N := seg_filled_sub h hs

/-- **The guard of the query.** -/
theorem guardQ_run {W eR eS eC d : ℕ} {σ : Env} {r : Res} {ob : List ℕ} (hW : σ.vars "W" = W)
    (hW2 : 8 ≤ W) (hF : Filled "OB" "po" ob σ) (hq : QAt r ob σ) (hlen : ob.length ≤ W)
    (hv : ∀ v ∈ σ.arrs "OB", v ≤ W) :
    ∃ σ', Run (W + 1) (guardQ eR eS eC d) σ σ'
        (ob.length * 30 + 60 * (eR + eS + eC + 1) + 30 * 2 ^ d + 300) ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ GOK eR eS eC d W r) ∧
      (∀ y, y ∉ gVars → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.inp = σ.inp := by
  have hc : ∀ (e : ℕ) (q : Qry), σ.vars "qk" = qkind q → σ.vars "qa" + σ.vars "ql" ≤ ob.length →
      seg ob (σ.vars "qa") (σ.vars "ql") = realQ q → expQ eR eS eC q = e →
      ∃ σ', Run (W + 1) (guardChk e d) σ σ' (ob.length * 30 + 60 * (e + 1) + 30 * 2 ^ d + 200) ∧
        (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ GOK eR eS eC d W (.call [] q)) ∧
        (∀ y, y ∉ gVars → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp := by
    intro e q _ hle hseg he
    have hl := hF.length_le
    obtain ⟨σ', r, hov, fv, fa, fo, fi⟩ := guardChk_run (e := e) (d := d) (a := σ.vars "qa")
      (N := σ.vars "ql") hW (by omega) rfl rfl (by omega) (by omega)
      (fun v hv' => hv v (mem_seg hv'))
    have hs : seg (σ.arrs "OB") (σ.vars "qa") (σ.vars "ql") = realQ q := by
      rw [seg_arr_of_filled hF hle, hseg]
    have hN : σ.vars "ql" = (realQ q).length := by
      rw [← hseg, length_seg (by omega)]
    rw [hs, hN] at hov
    refine ⟨σ', r.mono (by
      have h := Nat.mul_le_mul_right 30 (show σ.vars "ql" ≤ ob.length by omega); omega), ?_, fv, fa, fo, fi⟩
    rw [hov]
    simp only [GOK, he, ← hN]
    split_ifs with hg
    · exact ⟨fun h => ⟨h, hg⟩, fun h => h.1⟩
    · simp [hg]
  cases r with
  | call S q =>
    obtain ⟨hk, hle, hseg⟩ := hq
    have hq0 : (Cond.eq (V "qk") (N 0)).evalB (W + 1) σ = some (qkind q == 0) := by
      rw [← hk]; exact evalB_condEq (evalB_var (by cases q <;> simp [qkind] at hk ⊢ <;> omega))
        (evalB_lit (by omega))
    have hq1 : (Cond.eq (V "qk") (N 1)).evalB (W + 1) σ = some (qkind q == 1) := by
      rw [← hk]; exact evalB_condEq (evalB_var (by cases q <;> simp [qkind] at hk ⊢ <;> omega))
        (evalB_lit (by omega))
    have hq2 : (Cond.eq (V "qk") (N 2)).evalB (W + 1) σ = some (qkind q == 2) := by
      rw [← hk]; exact evalB_condEq (evalB_var (by cases q <;> simp [qkind] at hk ⊢ <;> omega))
        (evalB_lit (by omega))
    cases q with
    | re w =>
      obtain ⟨σ', r, h1, h2⟩ := hc eR (.re w) hk hle hseg rfl
      exact ⟨σ', (Run.ite_true (by simpa [qkind] using hq0) r).mono (by simp [Cond.size]; nlinarith),
        by simpa [GOK] using h1, h2⟩
    | sh w =>
      obtain ⟨σ', r, h1, h2⟩ := hc eS (.sh w) hk hle hseg rfl
      exact ⟨σ', (Run.ite_false (by simpa [qkind] using hq0) (Run.ite_true (by simpa [qkind] using hq1)
        r)).mono (by simp [Cond.size]; nlinarith), by simpa [GOK] using h1, h2⟩
    | ca ws =>
      obtain ⟨σ', r, h1, h2⟩ := hc eC (.ca ws) hk hle hseg rfl
      exact ⟨σ', (Run.ite_false (by simpa [qkind] using hq0) (Run.ite_false (by simpa [qkind] using hq1)
        (Run.ite_true (by simpa [qkind] using hq2) r))).mono (by simp [Cond.size]; nlinarith),
        by simpa [GOK] using h1, h2⟩
  | done z =>
    have hk : σ.vars "qk" = 3 := hq
    have e : ∀ m : ℕ, m < 3 → (Cond.eq (V "qk") (N m)).evalB (W + 1) σ = some false := by
      intro m hm
      rw [show false = (σ.vars "qk" == m) by rw [hk]; simp; omega]
      exact evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))
    exact ⟨σ, (Run.ite_false (e 0 (by omega)) (Run.ite_false (e 1 (by omega))
      (Run.ite_false (e 2 (by omega)) Run.skip))).mono (by simp [Cond.size] <;> omega),
      by simp [GOK], fun _ _ => rfl, rfl, rfl, rfl⟩
  | err =>
    have hk : σ.vars "qk" = 3 := hq
    have e : ∀ m : ℕ, m < 3 → (Cond.eq (V "qk") (N m)).evalB (W + 1) σ = some false := by
      intro m hm
      rw [show false = (σ.vars "qk" == m) by rw [hk]; simp; omega]
      exact evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))
    exact ⟨σ, (Run.ite_false (e 0 (by omega)) (Run.ite_false (e 1 (by omega))
      (Run.ite_false (e 2 (by omega)) Run.skip))).mono (by simp [Cond.size] <;> omega),
      by simp [GOK], fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ### The round test -/

theorem maxEntry_single (v : ℕ) : maxEntry [v] = v := by
  have := maxEntry_append_single [] v
  simpa [maxEntry] using this

/-- **The round test.** -/
theorem roundTest_run {W d : ℕ} {σ : Env} {ob : List ℕ} (hW : σ.vars "W" = W) (hW8 : 8 ≤ W)
    (hF : Filled "OB" "po" ob σ) (hl : ob.length + 1 ≤ W) (hOB : (σ.arrs "OB").length = W + 1)
    (hj : 2 * σ.vars "jr" ≤ W) (hv : ∀ v ∈ σ.arrs "OB", v ≤ W) :
    ∃ σ', Run (W + 1) (roundTest d) σ σ' (30 * 2 ^ d + 600) ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧
        min ((1 + 2 * σ.vars "jr" + 1) ^ (3 + 1)) W ≤ W / min (2 ^ d) W) ∧
      Filled "OB" "po" ob σ' ∧ (∀ y, y ∉ gVars ++ ["qa", "ql"] → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "OB" → σ'.arrs a = σ.arrs a) ∧ (σ'.arrs "OB").length = W + 1 ∧
      (∀ v ∈ σ'.arrs "OB", v ≤ W) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hpo := hF.pos
  set p := ob.length
  set σ1 := σ.setArr "OB" p (2 * σ.vars "jr") with h1
  have r1 : Run (W + 1) (.store "OB" (V "po") (.mul (N 2) (V "jr"))) σ σ1 5 :=
    (Run.store (idx := p) (v := 2 * σ.vars "jr")
      (by rw [show p = σ.vars "po" from hpo.symm]; exact evalB_var (by omega))
      (by simp; omega) (by omega)).mono (by simp)
  set σ2 := σ1.setVar "qa" p with h2
  set σ3 := σ2.setVar "ql" 1 with h3
  have r2 : Run (W + 1) (asg "qa" (V "po")) σ1 σ2 2 :=
    (Run.assign (by simp [h1]; omega)).mono (by simp)
  have r3 : Run (W + 1) (asg "ql" (N 1)) σ2 σ3 2 := (Run.assign (by simp; omega)).mono (by simp)
  have hOB3 : σ3.arrs "OB" = (σ.arrs "OB").set p (2 * σ.vars "jr") := by simp [h3, h2, h1]
  have hseg : seg (σ3.arrs "OB") p 1 = [2 * σ.vars "jr"] := by
    rw [hOB3]; simp [seg, List.getElem?_set, show p < (σ.arrs "OB").length by omega]
    rw [List.take_one, List.drop_set]; simp [show p < (σ.arrs "OB").length by omega]
    obtain ⟨a, l, hal⟩ : ∃ a l, List.drop p (σ.arrs "OB") = a :: l :=
      List.exists_cons_of_ne_nil (by simp; omega)
    rw [hal]; rfl
  have hv3 : ∀ v ∈ σ3.arrs "OB", v ≤ W := by
    intro v hv'
    rw [hOB3] at hv'
    rcases List.mem_or_eq_of_mem_set hv' with h | h
    · exact hv v h
    · omega
  obtain ⟨σ4, r4, hov, fv, fa, fo, fi⟩ := guardChk_run (e := 3) (d := d) (a := p) (N := 1)
    (σ := σ3) (by simp [h3, h2, h1, hW]) (by omega) (by simp [h3, h2]) (by simp [h3])
    (by rw [hOB3]; simp; omega) (by omega) (fun v hv' => hv3 v (mem_seg hv'))
  rw [hseg, maxEntry_single] at hov
  have hov3 : σ3.vars "ovf" = σ.vars "ovf" := by simp [h3, h2, h1]
  have hjr3 : σ3.vars "jr" = σ.vars "jr" := by simp [h3, h2, h1]
  refine ⟨σ4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_one r4)))).mono (by omega)
  · rw [hov, hov3]
    split_ifs with hg
    · exact ⟨fun h => ⟨h, by simpa using hg⟩, fun h => h.1⟩
    · simp only [one_ne_zero, false_iff, not_and]; intro _ h; exact hg (by simpa using h)
  · refine ⟨by rw [fv "po" (by decide)]; simp [h3, h2, h1, hpo, p], fun i hi => ?_⟩
    rw [fa, hOB3, List.getElem?_set_ne (by omega)]; exact hF.get i hi
  · intro y hy
    rw [fv y (fun h => hy (List.mem_append_left _ h))]
    have : y ≠ "qa" ∧ y ≠ "ql" := ⟨fun h => hy (by simp [h]), fun h => hy (by simp [h])⟩
    simp [h3, h2, h1, this.1, this.2]
  · intro a ha; rw [fa]; simp [h3, h2, h1, ha]
  · rw [fa, hOB3]; simp [hOB]
  · rw [fa]; exact hv3
  · rw [fo]; simp [h3, h2, h1]
  · rw [fi]; simp [h3, h2, h1]

/-! ### Writing the buffer -/

/-- A loop writing `N` cells of the buffer from `s`, with the check against `Ob`. -/
theorem wSeg_run {W s Nn : ℕ} {σ : Env} {ob : List ℕ} {ie : Expr} {nv : String}
    (hF : Filled "OB" "po" ob σ) (hsN : s + Nn ≤ ob.length) (hl : ob.length ≤ W)
    (hn : σ.vars nv = Nn) (hnv : nv ∉ ["ci", "ovf"]) (hO : σ.vars "Ob" ≤ W)
    (hv : ∀ v ∈ ob, v ≤ W)
    (hie : ∀ τ : Env, (∀ y, y ∉ ["ci", "ovf"] → τ.vars y = σ.vars y) → τ.vars "ci" < Nn →
      ∀ o, ie.evalB (W + 1) { τ with out := o } = some (s + τ.vars "ci"))
    (hsz : ie.size ≤ 4) :
    ∃ σ', Run (W + 1) (forUp "ci" (V nv) (wChk (.get "OB" ie))) σ σ' (30 * Nn + 10) ∧
      σ'.out = σ.out ++ seg ob s Nn ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ v ∈ seg ob s Nn, v < σ.vars "Ob") ∧
      σ'.arrs = σ.arrs ∧ (∀ y, y ∉ ["ci", "ovf"] → σ'.vars y = σ.vars y) ∧ σ'.inp = σ.inp := by
  let I : ℕ → Env → Prop := fun k τ => τ.out = σ.out ++ seg ob s k ∧
    (τ.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ v ∈ seg ob s k, v < σ.vars "Ob") ∧ τ.arrs = σ.arrs ∧
    (∀ y, y ∉ ["ci", "ovf"] → τ.vars y = σ.vars y) ∧ τ.inp = σ.inp
  have hlen := hF.length_le
  obtain ⟨σ', r, hI, -⟩ := forUp_run (B := W + 1) (i := "ci") (e := V nv)
    (body := wChk (.get "OB" ie)) (N := Nn) (K := 2 * (ie.size + 1) + 6) I (σ := σ) (by omega)
    (fun k _ τ hI _ => by rw [show Nn = τ.vars nv by rw [hI.2.2.2.1 nv hnv, hn]]; exact evalB_var (by
      rw [hI.2.2.2.1 nv hnv, hn]; omega))
    ⟨by simp [seg], by simp [seg], by simp, fun y hy => by
      have : y ≠ "ci" := fun h => hy (by simp [h]); simp [this], by simp⟩
    (fun k hk τ hτ hik => by
      obtain ⟨hout, hovf, harr, hvars, hinp⟩ := hτ
      have hsk : s + k < ob.length := by omega
      have hget : (τ.arrs "OB")[s + k]? = some ob[s + k] := by rw [harr]; exact hF.get _ hsk
      have hval := hv ob[s + k] (List.getElem_mem hsk)
      have hevO : ∀ o, (Expr.get "OB" ie).evalB (W + 1) { τ with out := o } = some ob[s + k] := by
        intro o
        refine evalB_get (k := s + k) ?_ (by simpa using hget) (by omega)
        rw [← hik]; exact hie τ hvars (by omega) o
      obtain ⟨τ', r', ho', hi', ha', hv', hlt, hge⟩ := wChk_run (B := W + 1) (v := ob[s + k]) hevO
        (by rw [hvars "Ob" (by decide)]; omega) (by omega)
      refine ⟨τ', r'.mono (by simp [Expr.size]), by rw [hv' "ci" (by decide), hik], ?_⟩
      have hseg : seg ob s (k + 1) = seg ob s k ++ [ob[s + k]] := by
        rw [seg_succ hsk]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsk]
      refine ⟨by simp [ho', hout, hseg], ?_, by simp [ha', harr], fun y hy => ?_, by simp [hi', hinp]⟩
      · simp only [Env.setVar, if_neg (show ("ovf" : String) ≠ "ci" by decide)]
        rw [hseg]
        by_cases hc : ob[s + k] < τ.vars "Ob"
        · rw [hlt hc, hovf]
          rw [hvars "Ob" (by decide)] at hc
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => hv.elim (h2 v) (fun e => e ▸ hc)⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => h2 v (Or.inl hv)⟩
        · rw [hge hc]
          rw [hvars "Ob" (by decide)] at hc
          simp only [one_ne_zero, false_iff, not_and, List.mem_append, List.mem_singleton]
          intro _ h; exact hc (h _ (Or.inr rfl))
      · have : y ≠ "ci" := fun h => hy (by simp [h])
        simp only [Env.setVar, if_neg this]
        rw [hv' y (fun h => hy (by simp [h])), hvars y hy])
  exact ⟨σ', r.mono (by simp [Expr.size]; nlinarith), hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩

theorem wDSq_frame (y : String) (hy : y ∈ ["po", "sp", "ovf", "Ob", "W"]) {B : ℕ} {σ σ' : Env} {K : ℕ}
    (r : Run B wDSq σ σ' K) : σ'.vars y = σ.vars y := by
  refine r.frame_var y ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Writing the buffer.** -/
theorem wrOut_run {W : ℕ} {σ : Env} {ob : List ℕ} (hW : σ.vars "W" = W) (hW34 : 2 ^ 34 ≤ W + 1)
    (hF : Filled "OB" "po" ob σ) (hsp : σ.vars "sp" ≤ ob.length)
    (hdq : σ.vars "dq" = 0 ∨ σ.vars "dq" = 1) (hl : ob.length + 1 ≤ W) (hv : ∀ v ∈ ob, v ≤ W) :
    ∃ σ', Run (W + 1) wrOut σ σ' (30 * ob.length + 300100) ∧
      σ'.out = σ.out ++ (ob.take (σ.vars "sp") ++ (if σ.vars "dq" = 1 then dSq else []) ++
        ob.drop (σ.vars "sp")) ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ v ∈ ob, v < W / 2 ^ 20 + 1) ∧ σ'.inp = σ.inp := by
  have hpo := hF.pos
  set sp := σ.vars "sp" with hspd
  have hOb : W / 2 ^ 20 + 1 ≤ W := by
    have : 2 ^ 20 * (W / 2 ^ 20) ≤ W := Nat.mul_div_le W _
    have : 2 ^ 20 ≤ W := by omega
    omega
  set σ1 := σ.setVar "Ob" (W / 2 ^ 20 + 1) with h1
  have r1 : Run (W + 1) (asg "Ob" (.add (.shiftr (V "W") (N 20)) (N 1))) σ σ1 6 := by
    refine (Run.assign ?_).mono (by simp)
    rw [show W / 2 ^ 20 + 1 = Bop.add.apply (Bop.shiftr.apply W 20) 1 from rfl]
    exact evalB_bin (evalB_bin (by rw [← hW]; exact evalB_var (by omega)) (evalB_lit (by omega))
      (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
  have hF1 : Filled "OB" "po" ob σ1 := hF.setVar (by decide) _
  obtain ⟨σ2, r2, ho2, hov2, ha2, hv2, hi2⟩ := wSeg_run (W := W) (s := 0) (Nn := sp) (nv := "sp")
    (ie := V "ci") hF1 (by omega) (by omega) (by simp [h1, hspd]) (by decide) (by simp [h1]; omega) hv
    (fun τ hτ hlt o => by simp; omega) (by simp)
  have hsp2 : σ2.vars "sp" = sp := by rw [hv2 "sp" (by decide)]; simp [h1, hspd]
  have hdq2 : σ2.vars "dq" = σ.vars "dq" := by rw [hv2 "dq" (by decide)]; simp [h1]
  have hF2 : Filled "OB" "po" ob σ2 := hF1.congr (hv2 "po" (by decide)) (by rw [ha2])
  -- the fixed question
  obtain ⟨σ3, r3, ho3, hv3, hf3, hi3⟩ : ∃ σ3, Run (W + 1) (.ite (.eq (V "dq") (N 1)) wDSq .skip) σ2 σ3 300010 ∧
      σ3.out = σ2.out ++ (if σ.vars "dq" = 1 then dSq else []) ∧
      (∀ y ∈ ["po", "sp", "ovf", "Ob", "W"], σ3.vars y = σ2.vars y) ∧
      σ3.arrs = σ2.arrs ∧ σ3.inp = σ2.inp := by
    have hev : (Cond.eq (V "dq") (N 1)).evalB (W + 1) σ2 = some (σ.vars "dq" == 1) := by
      rw [← hdq2]; exact evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))
    by_cases hd1 : σ.vars "dq" = 1
    · obtain ⟨σ3, r3, o3, i3, a3⟩ := wDSq_run (B := W + 1) (by omega) σ2
      refine ⟨σ3, (Run.ite_true (by rw [hev, hd1]; rfl) r3).mono ?_, by rw [o3, if_pos hd1],
        fun y hy => wDSq_frame y hy r3, a3, i3⟩
      have := wDSqCost_le; simp [Cond.size]; omega
    · refine ⟨σ2, (Run.ite_false (by rw [hev]; simp [hd1]) Run.skip).mono (by simp [Cond.size]),
        by simp [hd1], fun _ _ => rfl, rfl, rfl⟩
  have hsp3 : σ3.vars "sp" = sp := by rw [hv3 "sp" (by simp), hsp2]
  have hpo3 : σ3.vars "po" = ob.length := by rw [hv3 "po" (by simp), hF2.pos]
  have hF3 : Filled "OB" "po" ob σ3 := hF2.congr (hv3 "po" (by simp)) (by rw [hf3])
  set σ4 := σ3.setVar "sq" (ob.length - sp) with h4
  have r4 : Run (W + 1) (asg "sq" (.sub (V "po") (V "sp"))) σ3 σ4 4 := by
    refine (Run.assign ?_).mono (by simp)
    rw [show ob.length - sp = Bop.sub.apply (σ3.vars "po") (σ3.vars "sp") by rw [hpo3, hsp3]; rfl]
    exact evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by simp; omega)
  have hF4 : Filled "OB" "po" ob σ4 := hF3.setVar (by decide) _
  obtain ⟨σ5, r5, ho5, hov5, ha5, hv5, hi5⟩ := wSeg_run (W := W) (s := sp) (Nn := ob.length - sp)
    (nv := "sq") (ie := .add (V "sp") (V "ci")) hF4 (by omega) (by omega) (by simp [h4]) (by decide)
    (by rw [show σ4.vars "Ob" = σ3.vars "Ob" by simp [h4], hv3 "Ob" (by simp),
      hv2 "Ob" (by decide)]; simp [h1]; omega) hv
    (fun τ hτ hlt o => by
      have : τ.vars "sp" = sp := by rw [hτ "sp" (by decide)]; simp [h4, hsp3]
      simp [this]; omega) (by simp)
  refine ⟨σ5, ?_, ?_, ?_, ?_⟩
  · exact (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_one r5))))).mono (by omega)
  · rw [ho5, show σ4.out = σ3.out by simp [h4], ho3, ho2, show σ1.out = σ.out by simp [h1]]
    have e1 : seg ob 0 sp = ob.take sp := by simp [seg]
    have e2 : seg ob sp (ob.length - sp) = ob.drop sp := by
      simp only [seg]; exact List.take_of_length_le (by simp)
    rw [e1, e2]; simp
  · have hO4 : σ4.vars "Ob" = W / 2 ^ 20 + 1 := by
      rw [show σ4.vars "Ob" = σ3.vars "Ob" by simp [h4], hv3 "Ob" (by simp), hv2 "Ob" (by decide)]
      simp [h1]
    have hO1 : σ1.vars "Ob" = W / 2 ^ 20 + 1 := by simp [h1]
    have hov4 : σ4.vars "ovf" = σ2.vars "ovf" := by
      rw [show σ4.vars "ovf" = σ3.vars "ovf" by simp [h4], hv3 "ovf" (by simp)]
    have hov1 : σ1.vars "ovf" = σ.vars "ovf" := by simp [h1]
    rw [hov5, hO4, hov4, hov2, hO1, hov1]
    have e1 : seg ob 0 sp = ob.take sp := by simp [seg]
    have e2 : seg ob sp (ob.length - sp) = ob.drop sp := by
      simp only [seg]; exact List.take_of_length_le (by simp)
    rw [e1, e2]
    constructor
    · rintro ⟨⟨h0, h1'⟩, h2'⟩
      refine ⟨h0, fun v hv' => ?_⟩
      rw [← List.take_append_drop sp ob] at hv'
      rcases List.mem_append.1 hv' with h | h
      · exact h1' v h
      · exact h2' v h
    · rintro ⟨h0, h1'⟩
      exact ⟨⟨h0, fun v hv' => h1' v (List.mem_of_mem_take hv')⟩,
        fun v hv' => h1' v (List.mem_of_mem_drop hv')⟩
  · rw [hi5, show σ4.inp = σ3.inp by simp [h4], hi3, hi2]
    simp [h1]

end Lax185574Proofs.CompRam
