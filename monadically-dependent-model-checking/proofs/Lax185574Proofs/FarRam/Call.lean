import Lax185574Proofs.FarRam.Final
import Lax185574Proofs.ShiftRam.Glue


/-!
A round of the far-tree program that asks for a restriction: it writes
the state (the words read so far, with one more expected) and the query,
the child of extension `jr` with the positions `[ℓ]`.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.ShiftRam

def sumLn : Com :=
  .seq (.assign "tw" (.lit 0))
    (forUp "zs" (.var "nw") (.assign "tw" (.add (.var "tw") (.get "ln" (.var "zs")))))

theorem total_take_succ {W : List (List ℕ)} {i : ℕ} (h : i < W.length) :
    total (W.take (i + 1)) = total (W.take i) + W[i].length := off_succ h

theorem sumLn_run {B : ℕ} {W : List (List ℕ)} {σ : Env} (hw : WordsAt W σ) (hb : WordsBound B W)
    (hnw : σ.vars "nw" = W.length) :
    ∃ σ', Run B sumLn σ σ' (W.length * 15 + 10) ∧ σ'.vars "tw" = total W ∧
      (∀ z, z ∉ ["tw", "zs"] → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  have hlen := hb.len
  obtain ⟨σ', hr, ⟨htw, hfv, ha, ho⟩, -⟩ := forUp_run (B := B) (i := "zs") (e := .var "nw")
    (body := .assign "tw" (.add (.var "tw") (.get "ln" (.var "zs")))) (N := W.length) (K := 7)
    (fun k τ => τ.vars "tw" = total (W.take k) ∧ (∀ z, z ∉ ["tw", "zs"] → τ.vars z = σ.vars z) ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out) (σ := σ.setVar "tw" 0) (by omega)
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; rw [hI.2.1 "nw" (by decide), hnw]; exact ⟨rfl, by omega⟩)
    ⟨by simp [total], fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz; simp [hz.1, hz.2], by simp,
      by simp⟩
    (fun k hk τ ⟨htw, hfv, ha, ho⟩ hzs => by
      have hkt : total (W.take (k + 1)) ≤ total W := off_le_total W (k + 1)
      have hkt0 : total (W.take k) ≤ total W := off_le_total W k
      have hkl : W[k].length ≤ total W := by have := off_add_le hk; omega
      refine ⟨τ.setVar "tw" (total (W.take (k + 1))), (Run.assign ?_).mono (by simp), by simp [hzs], ?_,
        fun z hz => ?_, by simp [ha], by simp [ho]⟩
      · simp only [evalB_bin_iff, evalB_var_iff, evalB_get_iff]
        refine ⟨_, W[k].length, ⟨htw.symm, by rw [htw]; omega⟩, ⟨k, ⟨hzs.symm, by omega⟩, by
          rw [ha]; exact hw.ln k hk, by omega⟩, by rw [total_take_succ hk]; rfl,
          by omega⟩
      · simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp [hz.1, hz.2, hfv z (by simp [hz.1, hz.2])])
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono (by simp; nlinarith), ?_, hfv, ha, ho⟩
  rw [htw, List.take_length]

def findFr : Com :=
  .seq (.assign "ef" (.add (.var "ye") (.lit 1)))
    (forUp "zi" (.var "jr") (.assign "ef" (.add (.add (.var "ef") (.get "x" (.var "ef"))) (.lit 1))))

theorem findFr_run {B : ℕ} {X : List ℕ} {q ℓ : ℕ} {t : Node (q + 1) ℓ} {rest : List ℕ} {σ : Env}
    (hx : X.drop 0 = toWord t ++ rest) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 2 < B) {j : ℕ}
    (hj : j < (Node.exts t).words.length) (hxa : σ.arrs "x" = X) (hye : σ.vars "ye" = listEnd X 0)
    (hjr : σ.vars "jr" = j) :
    ∃ σ', Run B findFr σ σ' (j * 16 + 20) ∧ σ'.vars "ef" = frPos X (listEnd X 0) j ∧
      (∀ z, z ∉ ["ef", "zi"] → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  obtain ⟨-, h2⟩ := nodeSplit hx
  have hLe := listFacts_of h2
  obtain ⟨h0, -, -⟩ := listAt h2
  have hel := hLe.end_le
  have hRX : xg X (listEnd X 0) ≤ X.length := by
    have := hLe.frPos_le _ le_rfl; omega
  have hjB : j < B := by omega
  have hfp : ∀ k ≤ j, frPos X (listEnd X 0) k + 1 ≤ X.length := fun k hk => by
    have hk1 : k + 1 ≤ xg X (listEnd X 0) := by rw [h0]; omega
    obtain ⟨-, h1⟩ := hLe.frPos_le (k + 1) hk1
    have := skipFr_succ' X (listEnd X 0 + 1) k
    unfold frPos at h1 ⊢; omega
  obtain ⟨σ', hr, ⟨hef, hfv, ha, ho⟩, -⟩ := forUp_run (B := B) (i := "zi") (e := .var "jr")
    (body := .assign "ef" (.add (.add (.var "ef") (.get "x" (.var "ef"))) (.lit 1))) (N := j) (K := 8)
    (fun k τ => τ.vars "ef" = frPos X (listEnd X 0) k ∧ (∀ z, z ∉ ["ef", "zi"] → τ.vars z = σ.vars z) ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out) (σ := σ.setVar "ef" (listEnd X 0 + 1)) (by omega)
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; rw [hI.2.1 "jr" (by decide), hjr]; exact ⟨rfl, by omega⟩)
    ⟨by simp [frPos, skipFr], fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz; simp [hz.1, hz.2], by simp,
      by simp⟩
    (fun k hk τ ⟨hef, hfv, ha, ho⟩ hzi => by
      set fp := frPos X (listEnd X 0) k
      have hfpl : fp < X.length := by have := hfp k hk.le; omega
      have hnext : frPos X (listEnd X 0) (k + 1) = fp + xg X fp + 1 := by
        simp only [fp, frPos]; rw [skipFr_succ']; omega
      have hn1 := hfp (k + 1) (by omega)
      refine ⟨τ.setVar "ef" (fp + xg X fp + 1), (Run.assign ?_).mono (by simp), by simp [hzi], ?_,
        fun z hz => ?_, by simp [ha], by simp [ho]⟩
      · simp only [evalB_bin_iff, evalB_var_iff, evalB_get_iff, evalB_lit_iff]
        refine ⟨fp + xg X fp, 1, ⟨fp, xg X fp, ⟨hef.symm, by rw [hef]; omega⟩, ⟨fp, ⟨hef.symm, by rw [hef]; omega⟩, ?_,
          xg_lt hX (by omega)⟩, rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
        rw [ha, hxa, List.getElem?_eq_getElem hfpl, xg_of_lt hfpl]
      · simp [hnext]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp [hz.1, hz.2, hfv z (by simp [hz.1, hz.2])])
  refine ⟨σ', (Run.seq (Run.assign ?_) hr).mono (by simp; nlinarith), hef, hfv, ha, ho⟩
  simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
  have : listEnd X 0 < X.length := by have := hLe.frPos_le 0 (Nat.zero_le _); omega
  exact ⟨listEnd X 0, 1, ⟨hye.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩

theorem evalB_out (B : ℕ) (e : Expr) (σ : Env) (o : List ℕ) :
    e.evalB B { σ with out := o } = e.evalB B σ := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | get a i ih => simp only [Expr.evalB, ih]
  | bin op e f ihe ihf => simp only [Expr.evalB, ihe, ihf]

/-- Write the values of a list of expressions. -/
def writes : List Expr → Com
  | [] => .skip
  | e :: es => .seq (.write e) (writes es)

theorem writes_run {B : ℕ} : ∀ (es : List Expr) (vs : List ℕ) (σ : Env),
    List.Forall₂ (fun e v => e.evalB B σ = some v) es vs →
    Run B (writes es) σ { σ with out := σ.out ++ vs } ((es.map fun e => 1 + e.size).sum + 1)
  | [], [], σ, _ => by simpa [writes] using (Run.skip (B := B) (σ := σ))
  | e :: es, v₀ :: vs, σ, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have h2' : List.Forall₂ (fun e w => e.evalB B { σ with out := σ.out ++ [v₀] } = some w) es vs :=
      h2.imp fun e w h => by rw [evalB_out]; exact h
    have := writes_run es vs _ h2'
    refine (Run.seq (Run.write h1) this).mono (by simp; omega) |>.congr (by simp)

theorem sum_wd_length (W : List (List ℕ)) :
    ∀ k ≤ W.length, ∑ i ∈ Finset.range k, (wd W i).length = total (W.take k) := by
  intro k
  induction k with
  | zero => intro _; simp [total]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega), total_take_succ (by omega), wd_eq (by omega)]

def wFrames : Com := forUp "zs" (.var "nw") (.seq (.assign "ow" (.var "zs")) writeWord)

theorem wFrames_run {B : ℕ} {W : List (List ℕ)} {σ : Env} (hw : WordsAt W σ) (hb : WordsBound B W)
    (hnw : σ.vars "nw" = W.length) :
    ∃ σ', Run B wFrames σ σ' (13 * total W + 30 * W.length + 10) ∧ σ'.out = σ.out ++ frames W ∧
      (∀ z, z ∉ ["zs", "ow", "pa", "la", "k"] → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs := by
  have hlen := hb.len
  obtain ⟨σ', hr, ⟨hout, hfv, ha⟩, -⟩ := forUp_run_sum (B := B) (i := "zs") (e := .var "nw")
    (body := .seq (.assign "ow" (.var "zs")) writeWord) (N := W.length) (fun k => 13 * (wd W k).length + 20)
    (fun k τ => τ.out = σ.out ++ frames (W.take k) ∧
      (∀ z, z ∉ ["zs", "ow", "pa", "la", "k"] → τ.vars z = σ.vars z) ∧ τ.arrs = σ.arrs)
    (σ := σ) (by omega)
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; rw [hI.2.1 "nw" (by decide), hnw]; exact ⟨rfl, by omega⟩)
    ⟨by simp [frames], fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz; simp [hz.1], by simp⟩
    (fun k hk τ ⟨hout, hfv, ha⟩ hzs => by
      have hw1 : WordsAt W (τ.setVar "ow" k) := hw.of_arrs (by simp [ha]) (by simp [ha]) (by simp [ha])
      obtain ⟨τ', hr', hout'⟩ := writeWord_run hw1 hb (by simp) hk
      have hfv' : ∀ z, z ∉ ["pa", "la", "k"] → τ'.vars z = (τ.setVar "ow" k).vars z := fun z hz =>
        hr'.frame_var z (by simp at hz; simp [writeWord, writeEntry, Com.wvars]; tauto)
      have hfa' : ∀ a, τ'.arrs a = (τ.setVar "ow" k).arrs a := fun a =>
        hr'.frame_arr a (by simp [writeWord, writeEntry, Com.warrs])
      have hwk : W[k].length ≤ total W := by have := off_add_le hk; omega
      refine ⟨τ', (Run.seq (Run.assign (v := k) (by simp only [evalB_var_iff]; exact ⟨hzs.symm, by omega⟩))
        hr').mono (by rw [wd_eq hk]; simp; omega), by rw [hfv' "zs" (by decide)]; simp [hzs], ?_, fun z hz => ?_, ?_⟩
      · simp only [out_setVar]; rw [hout']; simp only [out_setVar]; rw [hout]; simp [frames_take_succ' hk]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp only [vars_setVar, if_neg hz.1]
        rw [hfv' z (by simp [hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]), vars_setVar, if_neg hz.2.1]
        exact hfv z (by simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2])
      · funext a; simp [hfa', ha])
  refine ⟨σ', hr.mono ?_, by rw [hout, List.take_length], hfv, ha⟩
  have h1 : ∑ k ∈ Finset.range W.length, (13 * (wd W k).length + 20 + (Expr.var "nw").size + 7) =
      13 * ∑ k ∈ Finset.range W.length, (wd W k).length + 28 * W.length := by
    rw [Finset.mul_sum]
    have h28 : 28 * W.length = ∑ _k ∈ Finset.range W.length, 28 := by simp [mul_comm]
    rw [h28, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by simp [Expr.size]
  rw [h1, sum_wd_length W _ le_rfl, List.take_length]
  simp [Expr.size]; omega

def wChild2 : Com :=
  .seq (.assign "cl" (.sub (.get "x" (.var "ef")) (.lit 1)))
    (forUp "i" (.var "cl") (.write (.get "x" (.add (.add (.var "ef") (.lit 2)) (.var "i")))))

def emitCall : Com :=
  .seq sumLn (.seq findFr (.seq (writes [.lit 1, .add (.add (.lit 4) (.var "nw")) (.var "tw"), .var "n0",
    .lit 0, .add (.var "jr") (.lit 1), .var "ns", .add (.var "nw") (.lit 1)])
    (.seq wFrames (.seq (writes [.add (.var "hk") (.lit 1), .sub (.var "hq") (.lit 1),
      .add (.var "hl") (.lit 1)]) (.seq wChild2 (writes [.lit 1, .var "hl"]))))))

def callCost (W : List (List ℕ)) (X : List ℕ) (j : ℕ) : ℕ :=
  13 * total W + 60 * W.length + 40 * X.length + 16 * j + 300

/-- **A call round.** -/
theorem emitCall_run (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t ++ rest) (k : ℕ) (W : List (List ℕ)) (nS n0 j : ℕ) (σ : Env)
    (hw : WordsAt W σ) (hb : WordsBound B W) (hnw : σ.vars "nw" = W.length) (hxa : σ.arrs "x" = X)
    (hye : σ.vars "ye" = listEnd X 0) (hjr : σ.vars "jr" = j) (hj : j < (Node.exts t).words.length)
    (hn0 : σ.vars "n0" = n0) (hns : σ.vars "ns" = nS) (hk : σ.vars "hk" = k) (hq : σ.vars "hq" = q + 1)
    (hl : σ.vars "hl" = ℓ) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 2 < B)
    (hWB : W.length + total W + 4 < B) (hvB : n0 + nS + k + q + ℓ + 3 < B) :
    ∃ σ', Run B emitCall σ σ' (callCost W X j) ∧ ∃ a ∈ Node.exts t,
      toWord a = (Node.exts t).words[j] ∧
      σ'.out = σ.out ++ ([1, 4 + W.length + total W, n0, 0, j + 1, nS, W.length + 1] ++ frames W ++
        [k + 1, q, ℓ + 1] ++ toWord a.2 ++ [1, ℓ]) := by
  obtain ⟨σ1, r1, htw1, hfv1, ha1, ho1⟩ := sumLn_run hw hb hnw
  obtain ⟨σ2, r2, hef2, hfv2, ha2, ho2⟩ := findFr_run hx hX hXB hj (by rw [ha1, hxa])
    (by rw [hfv1 "ye" (by decide), hye]) (by rw [hfv1 "jr" (by decide), hjr])
  have hv2 : ∀ z, z ∉ ["tw", "zs", "ef", "zi"] → σ2.vars z = σ.vars z := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hfv2 z (by simp [hz.2.2.1, hz.2.2.2]), hfv1 z (by simp [hz.1, hz.2.1])]
  have htw2 : σ2.vars "tw" = total W := by rw [hfv2 "tw" (by decide), htw1]
  have hw2 : WordsAt W σ2 := hw.of_arrs (by rw [ha2, ha1]) (by rw [ha2, ha1]) (by rw [ha2, ha1])
  have hjB : j + 2 < B := by
    obtain ⟨-, h2⟩ := nodeSplit hx
    have hLe := listFacts_of h2
    have hR0 := (listAt h2).1
    have hfe := (hLe.frPos_le _ le_rfl).2
    have hfe' := (hLe.frPos_le _ le_rfl).1
    have hel := hLe.end_le
    omega
  set vs1 := [1, 4 + W.length + total W, n0, 0, j + 1, nS, W.length + 1]
  have r3 := writes_run (B := B) [.lit 1, .add (.add (.lit 4) (.var "nw")) (.var "tw"), .var "n0",
    .lit 0, .add (.var "jr") (.lit 1), .var "ns", .add (.var "nw") (.lit 1)] vs1 σ2 (by
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true, vs1]
    refine ⟨evalB_lit (by omega), ?_, ?_, evalB_lit (by omega), ?_, ?_, ?_⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨4 + W.length, total W, ⟨4, W.length, ⟨rfl, by omega⟩, ⟨by rw [hv2 "nw" (by decide), hnw],
        by rw [hv2 "nw" (by decide), hnw]; omega⟩, rfl, by omega⟩, ⟨htw2.symm, by omega⟩, rfl, by omega⟩
    · simp only [evalB_var_iff]; rw [hv2 "n0" (by decide), hn0]; exact ⟨rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨j, 1, ⟨by rw [hv2 "jr" (by decide), hjr], by rw [hv2 "jr" (by decide), hjr]; omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [evalB_var_iff]; rw [hv2 "ns" (by decide), hns]; exact ⟨rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨W.length, 1, ⟨by rw [hv2 "nw" (by decide), hnw], by rw [hv2 "nw" (by decide), hnw]; omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩)
  set σ3 : Env := { σ2 with out := σ2.out ++ vs1 }
  obtain ⟨σ4, r4, ho4, hfv4, ha4⟩ := wFrames_run (σ := σ3) (hw2.of_arrs rfl rfl rfl) hb
    (by simp [σ3, hv2 "nw" (by decide), hnw])
  have hv4 : ∀ z, z ∉ ["tw", "zs", "ef", "zi", "ow", "pa", "la", "k"] → σ4.vars z = σ.vars z := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hfv4 z (by simp [hz.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2])]
    exact hv2 z (by simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1])
  set vs2 := [k + 1, q, ℓ + 1]
  have r5 := writes_run (B := B) [.add (.var "hk") (.lit 1), .sub (.var "hq") (.lit 1),
    .add (.var "hl") (.lit 1)] vs2 σ4 (by
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true, vs2]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨k, 1, ⟨by rw [hv4 "hk" (by decide), hk], by rw [hv4 "hk" (by decide), hk]; omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨q + 1, 1, ⟨by rw [hv4 "hq" (by decide), hq], by rw [hv4 "hq" (by decide), hq]; omega⟩,
        ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨ℓ, 1, ⟨by rw [hv4 "hl" (by decide), hl], by rw [hv4 "hl" (by decide), hl]; omega⟩,
        ⟨rfl, by omega⟩, rfl, by omega⟩)
  set σ5 : Env := { σ4 with out := σ4.out ++ vs2 }
  -- the child
  obtain ⟨-, h2⟩ := nodeSplit hx
  obtain ⟨a, ha, haw⟩ := getElem_words hj
  obtain ⟨-, r', hr'⟩ := extFrame h2 hj haw
  obtain ⟨-, -, hfr, -⟩ := listAt h2
  have hlen : xg X (frPos X (listEnd X 0) j) = (toWord a.2).length + 1 := by
    rw [(hfr j hj).1, ← haw, toWord_ext]; simp
  set fp := frPos X (listEnd X 0) j
  set L := (toWord a.2).length
  have hfpX : fp + 2 + L ≤ X.length := by
    have h := congrArg List.length hr'
    have := List.length_pos_iff.mpr (toWord_node_ne_nil a.2)
    simp at h; omega
  have hx5 : σ5.arrs "x" = X := by simp [σ5, ha4, σ3, ha2, ha1, hxa]
  have hef5 : σ5.vars "ef" = fp := by
    simp only [σ5]; rw [hfv4 "ef" (by decide)]; simp [σ3, hef2]
  have hfpl : fp < X.length := by omega
  set σ6 := σ5.setVar "cl" L
  have r6a : Run B (.assign "cl" (.sub (.get "x" (.var "ef")) (.lit 1))) σ5 σ6 5 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff]
    refine ⟨L + 1, 1, ⟨fp, ⟨hef5.symm, by omega⟩, ?_, by omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩
    rw [hx5, List.getElem?_eq_getElem hfpl, ← xg_of_lt hfpl, hlen]
  obtain ⟨σ7, r7, -, hout7⟩ := writeLoop_run (B := B) (N := L) (m := "cl")
    (e := .get "x" (.add (.add (.var "ef") (.lit 2)) (.var "i"))) (fun i => xg X (fp + 2 + i))
    (fun τ => τ.arrs "x" = X ∧ τ.vars "ef" = fp ∧ τ.vars "cl" = L) (by omega) (by decide)
    (fun τ o h => h) (fun τ k' h => ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩)
    (fun τ h => h.2.2)
    (fun τ h hi => by
      simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨fp + 2 + τ.vars "i", ⟨fp + 2, τ.vars "i", ⟨fp, 2, ⟨h.2.1.symm, by omega⟩, ⟨rfl, by omega⟩,
        rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ?_, xg_lt hX (by omega)⟩
      rw [h.1, List.getElem?_eq_getElem (by omega), ← xg_of_lt (by omega)])
    σ6 ⟨by simp [σ6, hx5], by simp [σ6, hef5], by simp [σ6]⟩
  rw [map_xg_drop hr'] at hout7
  have hl7 : σ7.vars "hl" = ℓ := by
    rw [r7.frame_var "hl" (by decide)]; simp only [σ6, vars_setVar]; simp [σ5]
    rw [hv4 "hl" (by decide), hl]
  have r8 := writes_run (B := B) [.lit 1, .var "hl"] [1, ℓ] σ7 (by
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
    exact ⟨evalB_lit (by omega), by simp only [evalB_var_iff]; rw [hl7]; exact ⟨rfl, by omega⟩⟩)
  refine ⟨{ σ7 with out := σ7.out ++ [1, ℓ] }, ?_, a, ha, haw, ?_⟩
  · unfold emitCall wChild2
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq (Run.seq r6a r7) r8)))))).mono ?_
    simp only [callCost, writes, Expr.size, List.map, List.sum_cons, List.sum_nil]
    have : L ≤ X.length := by omega
    nlinarith
  · simp only [hout7, σ6, out_setVar, σ5, ho4, σ3, ho2, ho1, vs1, vs2]
    simp

end Lax185574Proofs.FarRam
