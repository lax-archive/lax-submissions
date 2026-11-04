import Lax185574Proofs.ResolveRam.Glue.PWl

/-!
The query of the children of an item of lem:resolve-lift (`KidSpec`).

`kidCmd` reads `q` and `ℓ` from the item word `ow`, and for every `j <
kn` the parent and guard of the item word `kl + j` and the entries `1`,
`2` of the output word `ol + j`. If they pass `kidSel`, it appends the
frame of the guard followed by the output word without its header. The
number of frames is written in front at the end (`kidCmd_spec`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.ResolveRam

/-- Four nested tests around a command. -/
def ite4 (c1 c2 c3 c4 : Cond) (body : Com) : Com :=
  .ite c1 (.ite c2 (.ite c3 (.ite c4 body .skip) .skip) .skip) .skip

theorem ite4_run {B : ℕ} {c1 c2 c3 c4 : Cond} {body : Com} {τ τ' : Env} {b1 b2 b3 b4 : Bool} {K : ℕ}
    (h1 : c1.evalB B τ = some b1) (h2 : b1 = true → c2.evalB B τ = some b2)
    (h3 : b1 = true → b2 = true → c3.evalB B τ = some b3)
    (h4 : b1 = true → b2 = true → b3 = true → c4.evalB B τ = some b4)
    (hb : (b1 && b2 && b3 && b4) = true → Run B body τ τ' K) :
    Run B (ite4 c1 c2 c3 c4 body) τ (if (b1 && b2 && b3 && b4) = true then τ' else τ)
      (K + c1.size + c2.size + c3.size + c4.size + 5) := by
  unfold ite4
  cases b1
  · exact (Run.ite_false h1 Run.skip).mono (by omega)
  cases b2
  · exact (Run.ite_true h1 (Run.ite_false (h2 rfl) Run.skip)).mono (by omega)
  cases b3
  · exact (Run.ite_true h1 (Run.ite_true (h2 rfl) (Run.ite_false (h3 rfl rfl) Run.skip))).mono
      (by omega)
  cases b4
  · exact (Run.ite_true h1 (Run.ite_true (h2 rfl) (Run.ite_true (h3 rfl rfl)
      (Run.ite_false (h4 rfl rfl rfl) Run.skip)))).mono (by omega)
  · exact (Run.ite_true h1 (Run.ite_true (h2 rfl) (Run.ite_true (h3 rfl rfl)
      (Run.ite_true (h4 rfl rfl rfl) (hb rfl))))).mono (by omega)

/-- Append the frame of the guard `tgg` followed by word `tw1` without
its first three entries. -/
def kEmit : Com :=
  .seq (.assign "tOl" (.get "ln" (.var "tw1"))) (.seq (push1 "OB" "po" (.sub (.var "tOl") (.lit 2)))
    (.seq (push1 "OB" "po" (.var "tgg")) (.seq (.assign "tsa" (.add (.get "st" (.var "tw1")) (.lit 3)))
      (.seq (.assign "tsl" (.sub (.var "tOl") (.lit 3))) (.seq (cpSeg "a" "tsa" "tsl")
        (.assign "fc" (.add (.var "fc") (.lit 1))))))))

/-- One child candidate. -/
def kidBody : Com :=
  .seq (.assign "tw0" (.add (.var "kl") (.var "tj"))) (.seq (sget "tpp" "tw0" 0) (.seq (sget "tgg" "tw0" 1)
    (.seq (.assign "tw1" (.add (.var "ol") (.var "tj"))) (.seq (sget "tO1" "tw1" 1) (.seq (sget "tO2" "tw1" 2)
      (ite4 (.eq (.var "tpp") (.var "ii")) (.lt (.var "tgg") (.var "tl")) (.eq (.var "tO1") (.var "tq"))
        (.eq (.var "tO2") (.var "tl1")) kEmit))))))

/-- **The children of an item.** -/
def kidCmd : Com :=
  .seq (.assign "tq" (.sub (.get "a" (.add (.get "st" (.var "ow")) (.lit 3))) (.lit 1)))
    (.seq (.assign "tl" (.get "a" (.add (.get "st" (.var "ow")) (.lit 4))))
      (.seq (.assign "tl1" (.add (.var "tl") (.lit 1))) (.seq (.assign "fp" (.var "po"))
        (.seq (push1 "OB" "po" (.lit 0)) (.seq (.assign "fc" (.lit 0))
          (.seq (forUp "tj" (.var "kn") kidBody) patch))))))

/-- The scalars that `kidCmd` writes. -/
def kidV : List String :=
  ["tq", "tl", "tl1", "fp", "po", "fc", "tj", "tw0", "tpp", "tgg", "tw1", "tO1", "tO2", "tOl", "tsa", "tsl",
    "ci"]

theorem kidCmd_wvars : ∀ y ∈ kidCmd.wvars, y ∈ kidV := by decide

theorem kidSel_take_succ (q ℓ i : ℕ) {PG : List (ℕ × ℕ)} {OW : List (List ℕ)} {j : ℕ}
    (h1 : j < PG.length) (h2 : j < OW.length) :
    kidW q ℓ i (PG.take (j + 1)) (OW.take (j + 1)) =
      kidW q ℓ i (PG.take j) (OW.take j) ++ (kidSel q ℓ i PG[j] OW[j]).toList := by
  unfold kidW
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.toList_some, Option.toList_some, List.zip_append (by simp; omega), List.filterMap_append]
  congr 1

theorem total_take_drop_succ {ws : List (List ℕ)} {ol j : ℕ} (h : ol + j < ws.length) :
    total ((ws.drop ol).take (j + 1)) = total ((ws.drop ol).take j) + ws[ol + j].length := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h, Option.toList_some]
  simp [total]

/-- A segment of the array `a` inside a library word. -/
theorem seg_word {ws : List (List ℕ)} {τ : Env} (hw : WordsAt ws τ) {n : ℕ} (hn : n < ws.length) {d : ℕ}
    (hd : d ≤ ws[n].length) :
    seg (τ.arrs "a") (off ws n + d) (ws[n].length - d) = ws[n].drop d := by
  have h := drop_off hw hn
  simp only [seg]
  rw [← List.drop_drop, h, List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp)]
  simp

/-- **Appending a child.** -/
theorem kEmit_run {W : ℕ} {ws : List (List ℕ)} {pre : List ℕ} {n g c : ℕ} {τ : Env}
    (hw : WordsAt ws τ) (hn : n < ws.length) (h3 : 3 ≤ ws[n].length) (htw : τ.vars "tw1" = n)
    (hg : τ.vars "tgg" = g) (hfc : τ.vars "fc" = c) (hF : Filled "OB" "po" pre τ)
    (hOB : (τ.arrs "OB").length = W + 1) (ha : (τ.arrs "a").length = W + 1)
    (hB : pre.length + ws[n].length + 1 ≤ W) (hT : total ws + ws.length + 4 ≤ W)
    (hv : ∀ u ∈ ws[n], u ≤ W) (hgW : g ≤ W) (hc : c + 1 ≤ W) :
    ∃ τ', Run (W + 1) kEmit τ τ' (20 * ws[n].length + 60) ∧
      Filled "OB" "po" (pre ++ frames [g :: ws[n].drop 3]) τ' ∧ τ'.vars "fc" = c + 1 ∧
      OFr τ τ' ["tOl", "po", "tsa", "tsl", "ci", "fc"] := by
  have hoff := off_add_le hn
  set m := ws[n].length
  set τ1 := τ.setVar "tOl" m
  have r1 : Run (W + 1) (.assign "tOl" (.get "ln" (.var "tw1"))) τ τ1 3 :=
    (Run.assign (evalB_get (ev_var htw (by omega)) (hw.ln n hn) (by omega))).mono (by simp [Expr.size])
  obtain ⟨τ2, r2, F2, o2⟩ := push1_ofr (W := W) (e := .sub (.var "tOl") (.lit 2)) (v := m - 2)
    (hF.setVar (y := "tOl") (by decide) m) (ev_sub (ev_var (v := m) (by simp [τ1]) (by omega))
      (evalB_lit (by omega)) (by omega))
    (by simp [τ1, hOB]; omega) (by omega)
  obtain ⟨τ3, r3, F3, o3⟩ := push1_ofr (W := W) (e := .var "tgg") (v := g) F2
    (ev_var (v := g) (by rw [o2.vars _ (by decide)]; simp [τ1, hg]) (by omega))
    (by rw [o2.len]; simp [τ1, hOB]; omega) (by simp; omega)
  have hst3 : τ3.arrs "st" = τ.arrs "st" := by rw [o3.arrs _ (by decide), o2.arrs _ (by decide)]; simp [τ1]
  have hln3 : τ3.arrs "ln" = τ.arrs "ln" := by rw [o3.arrs _ (by decide), o2.arrs _ (by decide)]; simp [τ1]
  have ha3 : τ3.arrs "a" = τ.arrs "a" := by rw [o3.arrs _ (by decide), o2.arrs _ (by decide)]; simp [τ1]
  have v3 : ∀ y, y ∉ ["po"] → τ3.vars y = τ1.vars y := fun y hy => by
    rw [o3.vars y hy, o2.vars y hy]
  set τ4 := τ3.setVar "tsa" (off ws n + 3)
  have htw3 : τ3.vars "tw1" = n := by rw [v3 _ (by decide)]; simp [τ1, htw]
  have est : (Expr.get "st" (.var "tw1")).evalB (W + 1) τ3 = some (off ws n) :=
    evalB_get (ev_var htw3 (by omega)) (by rw [hst3]; exact hw.st n hn) (by omega)
  have r4 : Run (W + 1) (.assign "tsa" (.add (.get "st" (.var "tw1")) (.lit 3))) τ3 τ4 5 :=
    (Run.assign (ev_add est (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  set τ5 := τ4.setVar "tsl" (m - 3)
  have r5 : Run (W + 1) (.assign "tsl" (.sub (.var "tOl") (.lit 3))) τ4 τ5 4 :=
    (Run.assign (ev_sub (ev_var (by simp [τ4]; rw [v3 _ (by decide)]; simp [τ1]) (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  have hseg : seg (τ5.arrs "a") (off ws n + 3) (m - 3) = ws[n].drop 3 := by
    simp only [τ5, τ4, arrs_setVar]; rw [ha3]; exact seg_word hw hn h3
  obtain ⟨τ6, r6, F6, o6⟩ := cpSeg_ofr (W := W) (src := "a") (s := "tsa") (l := "tsl")
    (a := off ws n + 3) (N := m - 3) (σ := τ5) (by decide) (by simp [τ5, τ4]) (by simp [τ5])
    (by decide) (by decide) (by decide) (by decide) ((F3.setVar (by decide) _).setVar (by decide) _)
    (by simp [τ5, τ4, ha3, ha]; omega) (by simp [τ5, τ4]; rw [o3.len, o2.len]; simp [τ1, hOB]; omega)
    (by omega) (by simp; omega) (by rw [hseg]; intro u hu; exact hv u (List.mem_of_mem_drop hu))
  rw [hseg] at F6
  have hfc6 : τ6.vars "fc" = c := by
    rw [o6.vars _ (by decide)]; simp [τ5, τ4]; rw [v3 _ (by decide)]; simp [τ1, hfc]
  set τ7 := τ6.setVar "fc" (c + 1)
  have r7 : Run (W + 1) (.assign "fc" (.add (.var "fc") (.lit 1))) τ6 τ7 4 :=
    (Run.assign (ev_add (ev_var hfc6 (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  refine ⟨τ7, ?_, ?_, by simp [τ7], ?_⟩
  · unfold kEmit
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    simp only [Expr.size]; omega
  · have : frames [g :: ws[n].drop 3] = [m - 2, g] ++ ws[n].drop 3 := by
      rw [frames_single]; simp; omega
    rw [this]
    simpa [List.append_assoc] using F6.setVar (y := "fc") (by decide) (c + 1)
  · exact ((((((OFr.setVar τ "tOl" m).trans o2).trans o3).trans (OFr.setVar τ3 "tsa" _)).trans
      (OFr.setVar τ4 "tsl" _)).trans o6 |>.trans (OFr.setVar τ6 "fc" _)).mono (by decide)

/-- The scalars that the loop body writes. -/
def kbV0 : List String := ["tw0", "tpp", "tgg", "tw1", "tO1", "tO2", "tOl", "tsa", "tsl", "ci", "po", "fc"]

/-- **One child candidate.** -/
theorem kidBody_run {W : ℕ} {ws : List (List ℕ)} {pre : List ℕ} {kl ol j i q ℓ c : ℕ} {τ : Env}
    (hw : WordsAt ws τ) (hkl : τ.vars "kl" = kl) (hol : τ.vars "ol" = ol) (hj : τ.vars "tj" = j)
    (hi : τ.vars "ii" = i) (hq : τ.vars "tq" = q) (hl : τ.vars "tl" = ℓ) (hl1 : τ.vars "tl1" = ℓ + 1)
    (hk1 : kl + j < ws.length) (hk2 : ol + j < ws.length) (hF : Filled "OB" "po" pre τ)
    (hfc : τ.vars "fc" = c) (hOB : (τ.arrs "OB").length = W + 1) (ha : (τ.arrs "a").length = W + 1)
    (hB : pre.length + ws[ol + j].length + 1 ≤ W) (hT : total ws + ws.length + 4 ≤ W)
    (hv : ∀ n (hn : n < ws.length), ∀ u ∈ ws[n], u ≤ W) (hiW : i ≤ W) (hqW : q ≤ W) (hlW : ℓ + 1 ≤ W)
    (hc : c + 1 ≤ W) :
    ∃ τ', Run (W + 1) kidBody τ τ' (20 * ws[ol + j].length + 200) ∧
      Filled "OB" "po" (pre ++ frames (kidSel q ℓ i (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0)
        ws[ol + j]).toList) τ' ∧
      τ'.vars "fc" = c + (kidSel q ℓ i (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0) ws[ol + j]).toList.length ∧
      OFr τ τ' kbV0 := by
  have hgB : ∀ (n : ℕ) (hn : n < ws.length) (d : ℕ), ws[n].getD d 0 ≤ W := fun n hn d => by
    rw [List.getD_eq_getElem?_getD]
    cases h : ws[n][d]? with
    | none => simp
    | some u => simpa using hv n hn u (List.mem_of_getElem? h)
  have hvB : ∀ (n : ℕ) (hn : n < ws.length), ∀ u ∈ ws[n], u < W + 1 := fun n hn u hu => by
    have := hv n hn u hu; omega
  set pw := ws[kl + j]
  set ow := ws[ol + j]
  have hp0 : pw.getD 0 0 ≤ W := hgB _ hk1 0
  have hp1 : pw.getD 1 0 ≤ W := hgB _ hk1 1
  have ho1 : ow.getD 1 0 ≤ W := hgB _ hk2 1
  have ho2 : ow.getD 2 0 ≤ W := hgB _ hk2 2
  set τ1 := τ.setVar "tw0" (kl + j)
  have r1 : Run (W + 1) (.assign "tw0" (.add (.var "kl") (.var "tj"))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hkl (by omega)) (ev_var hj (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have w1 : WordsAt ws τ1 := hw.of_arrs (by simp [τ1]) (by simp [τ1]) (by simp [τ1])
  have r2 := sget_run (B := W + 1) w1 (v := "tpp") (x := "tw0") (j := 0) (by simp [τ1]) hk1 (by omega) (hvB _ hk1)
  set τ2 := τ1.setVar "tpp" (pw.getD 0 0)
  have w2 : WordsAt ws τ2 := hw.of_arrs (by simp [τ2, τ1]) (by simp [τ2, τ1]) (by simp [τ2, τ1])
  have r3 := sget_run (B := W + 1) w2 (v := "tgg") (x := "tw0") (j := 1) (by simp [τ2, τ1]) hk1 (by omega) (hvB _ hk1)
  set τ3 := τ2.setVar "tgg" (pw.getD 1 0)
  set τ4 := τ3.setVar "tw1" (ol + j)
  have r4 : Run (W + 1) (.assign "tw1" (.add (.var "ol") (.var "tj"))) τ3 τ4 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ3, τ2, τ1, hol]) (by omega))
      (ev_var (by simp [τ3, τ2, τ1, hj]) (by omega)) (by omega))).mono (by simp [Expr.size])
  have w4 : WordsAt ws τ4 := hw.of_arrs (by simp [τ4, τ3, τ2, τ1]) (by simp [τ4, τ3, τ2, τ1])
    (by simp [τ4, τ3, τ2, τ1])
  have r5 := sget_run (B := W + 1) w4 (v := "tO1") (x := "tw1") (j := 1) (by simp [τ4]) hk2 (by omega) (hvB _ hk2)
  set τ5 := τ4.setVar "tO1" (ow.getD 1 0)
  have w5 : WordsAt ws τ5 := hw.of_arrs (by simp [τ5, τ4, τ3, τ2, τ1]) (by simp [τ5, τ4, τ3, τ2, τ1])
    (by simp [τ5, τ4, τ3, τ2, τ1])
  have r6 := sget_run (B := W + 1) w5 (v := "tO2") (x := "tw1") (j := 2) (by simp [τ5, τ4]) hk2 (by omega) (hvB _ hk2)
  set τ6 := τ5.setVar "tO2" (ow.getD 2 0)
  have w6 : WordsAt ws τ6 := hw.of_arrs (by simp [τ6, τ5, τ4, τ3, τ2, τ1])
    (by simp [τ6, τ5, τ4, τ3, τ2, τ1]) (by simp [τ6, τ5, τ4, τ3, τ2, τ1])
  have g : ∀ y, y ∉ ["tw0", "tpp", "tgg", "tw1", "tO1", "tO2"] → τ6.vars y = τ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [τ6, τ5, τ4, τ3, τ2, τ1, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
  have c1 := evalB_condEq (B := W + 1) (σ := τ6) (ev_var (x := "tpp") (v := pw.getD 0 0) (by simp [τ6, τ5, τ4, τ3, τ2])
    (by omega)) (ev_var (x := "ii") (v := i) (by rw [g "ii" (by decide), hi]) (by omega))
  have c2 := evalB_condLt (B := W + 1) (σ := τ6) (ev_var (x := "tgg") (v := pw.getD 1 0) (by simp [τ6, τ5, τ4, τ3])
    (by omega)) (ev_var (x := "tl") (v := ℓ) (by rw [g "tl" (by decide), hl]) (by omega))
  have c3 := evalB_condEq (B := W + 1) (σ := τ6) (ev_var (x := "tO1") (v := ow.getD 1 0) (by simp [τ6, τ5])
    (by omega)) (ev_var (x := "tq") (v := q) (by rw [g "tq" (by decide), hq]) (by omega))
  have c4 := evalB_condEq (B := W + 1) (σ := τ6) (ev_var (x := "tO2") (v := ow.getD 2 0) (by simp [τ6])
    (by omega)) (ev_var (x := "tl1") (v := ℓ + 1) (by rw [g "tl1" (by decide), hl1]) (by omega))
  set b := (pw.getD 0 0 == i) && decide (pw.getD 1 0 < ℓ) && (ow.getD 1 0 == q) && (ow.getD 2 0 == ℓ + 1)
  have hsel : kidSel q ℓ i (pw.getD 0 0, pw.getD 1 0) ow =
      if b = true then some (pw.getD 1 0 :: ow.drop 3) else none := by
    simp only [kidSel, b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  have F6 : Filled "OB" "po" pre τ6 := hF.congr (g "po" (by decide)) (by simp [τ6, τ5, τ4, τ3, τ2, τ1])
  by_cases hb : b = true
  · have h3 : 3 ≤ ow.length := by
      simp only [b, Bool.and_eq_true, beq_iff_eq] at hb
      by_contra h
      have h0 : ow.getD 2 0 = 0 := List.getD_eq_default _ _ (by omega)
      rw [h0] at hb
      omega
    obtain ⟨τ7, r7, F7, f7, o7⟩ := kEmit_run (W := W) w6 hk2 h3 (by simp [τ6, τ5, τ4]) (by simp [τ6, τ5, τ4, τ3])
      (by rw [g "fc" (by decide), hfc]) F6 (by simp [τ6, τ5, τ4, τ3, τ2, τ1, hOB])
      (by simp [τ6, τ5, τ4, τ3, τ2, τ1, ha]) hB hT (hv _ hk2) hp1 hc
    have r8 := ite4_run (B := W + 1) (body := kEmit) (K := 20 * ow.length + 60) c1 (fun _ => c2)
      (fun _ _ => c3) (fun _ _ _ => c4) (fun _ => r7)
    rw [if_pos hb] at r8
    refine ⟨τ7, ?_, by rw [hsel, if_pos hb]; exact F7, by rw [f7, hsel, if_pos hb]; rfl, ?_⟩
    · unfold kidBody
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r8)))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · exact ((((((((OFr.setVar τ "tw0" _).trans (OFr.setVar τ1 "tpp" _)).trans (OFr.setVar τ2 "tgg" _)).trans
        (OFr.setVar τ3 "tw1" _)).trans (OFr.setVar τ4 "tO1" _)).trans (OFr.setVar τ5 "tO2" _)).trans o7).mono
        (by decide))
  · have r8 := ite4_run (B := W + 1) (body := kEmit) (τ' := τ6) (K := 0) c1 (fun _ => c2)
      (fun _ _ => c3) (fun _ _ _ => c4) (fun h => absurd h hb)
    rw [if_neg hb] at r8
    refine ⟨τ6, ?_, by rw [hsel, if_neg hb]; simpa [frames] using F6, by
      rw [hsel, if_neg hb, g "fc" (by decide), hfc]; rfl, ?_⟩
    · unfold kidBody
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r8)))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · exact (((((((OFr.setVar τ "tw0" _).trans (OFr.setVar τ1 "tpp" _)).trans (OFr.setVar τ2 "tgg" _)).trans
        (OFr.setVar τ3 "tw1" _)).trans (OFr.setVar τ4 "tO1" _)).trans (OFr.setVar τ5 "tO2" _)).mono
        (by decide))

theorem sum_len_drop {ws : List (List ℕ)} {ol : ℕ} : ∀ n, ol + n ≤ ws.length →
    ∑ k ∈ Finset.range n, (ws.getD (ol + k) []).length = total ((ws.drop ol).take n)
  | 0, _ => by simp [total]
  | n + 1, h => by
    rw [Finset.sum_range_succ, sum_len_drop n (by omega), total_take_drop_succ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

theorem frames_kidSel_le (q ℓ i : ℕ) (pg : ℕ × ℕ) (ow : List ℕ) :
    (frames (kidSel q ℓ i pg ow).toList).length ≤ ow.length := by
  unfold kidSel
  split_ifs with h
  · have h3 : 3 ≤ ow.length := by
      by_contra hc
      have : ow.getD 2 0 = 0 := List.getD_eq_default _ _ (by omega)
      omega
    simp [frames]; omega
  · simp [frames]

theorem total_sub {l L : List (List ℕ)} (h : l.Sublist L) : total l ≤ total L := by
  induction h with
  | slnil => simp [total]
  | cons a _ ih => rw [total_cons]; omega
  | cons_cons a _ ih => rw [total_cons, total_cons]; omega

/-- The scalars that the loop body writes, with the counter. -/
def kbV : List String := ["tw0", "tpp", "tgg", "tw1", "tO1", "tO2", "tOl", "tsa", "tsl", "ci", "po", "fc", "tj"]

/-- **The specification of the children query.** -/
theorem kidCmd_spec : KidSpec kidCmd kidV := by
  refine ⟨300, 0, ?_⟩
  intro W τ ws pre ow kl kn ol i p g k q ℓ t how hW hA hw howv hiv hklv hknv holv hkl hol hit hF hRoom
  have hRS := room_ge hRoom
  set S := ySz (toWord ws) + i + pre.length
  have hws : (toWord ws).length = ws.length + total ws + 1 := by
    rw [toWord_words, List.length_cons, Words.length_frames]
  have hSW : 65536 * (S + 1) ≤ W := by simpa using hRS
  have hySw : (toWord ws).length + maxEntry (toWord ws) + 1 + i + pre.length ≤ S := by
    simp only [S, ySz]; omega
  have hent : ∀ n (hn : n < ws.length), ∀ u ∈ ws[n], u ≤ W := fun n hn u hu => by
    have := le_maxEntry (mem_toWord_of hn hu); omega
  have hT : total ws + ws.length + 4 ≤ W := by omega
  -- the header
  have hoff := off_add_le how
  have hitw : ws[ow] = p :: g :: k :: (q + 1) :: ℓ :: toWord t := by rw [hit]; rfl
  have hlw : 5 ≤ ws[ow].length := by rw [hitw]; simp
  have e3 : (τ.arrs "a")[off ws ow + 3]? = some (q + 1) := by rw [hw.a ow how 3 (by omega)]; simp [hitw]
  have e4 : (τ.arrs "a")[off ws ow + 4]? = some ℓ := by rw [hw.a ow how 4 (by omega)]; simp [hitw]
  have bq : q + 1 ≤ W := hent ow how _ (by rw [hitw]; simp)
  have bl : ℓ + 1 ≤ W := by
    have := le_maxEntry (mem_toWord_of how (show ℓ ∈ ws[ow] by rw [hitw]; simp)); omega
  have est : ∀ ρ : Env, ρ.vars "ow" = ow → ρ.arrs "st" = τ.arrs "st" →
      (Expr.get "st" (.var "ow")).evalB (W + 1) ρ = some (off ws ow) := fun ρ h1 h2 =>
    evalB_get (ev_var h1 (by omega)) (by rw [h2]; exact hw.st ow how) (by omega)
  set τ1 := τ.setVar "tq" q
  have r1 : Run (W + 1) (.assign "tq" (.sub (.get "a" (.add (.get "st" (.var "ow")) (.lit 3))) (.lit 1))) τ τ1 8 :=
    (Run.assign (ev_sub (evalB_get (ev_add (est τ howv rfl) (evalB_lit (by omega)) (by omega)) e3 (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  set τ2 := τ1.setVar "tl" ℓ
  have r2 : Run (W + 1) (.assign "tl" (.get "a" (.add (.get "st" (.var "ow")) (.lit 4)))) τ1 τ2 6 :=
    (Run.assign (evalB_get (ev_add (est τ1 (by simp [τ1, howv]) (by simp [τ1])) (evalB_lit (by omega))
      (by omega)) (by simpa [τ1] using e4) (by omega))).mono (by simp [Expr.size])
  set τ3 := τ2.setVar "tl1" (ℓ + 1)
  have r3 : Run (W + 1) (.assign "tl1" (.add (.var "tl") (.lit 1))) τ2 τ3 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ2]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  set τ4 := τ3.setVar "fp" pre.length
  have r4 : Run (W + 1) (.assign "fp" (.var "po")) τ3 τ4 2 :=
    Run.assign (ev_var (by simp [τ3, τ2, τ1, hF.pos]) (by omega))
  obtain ⟨τ5, r5, F5, o5⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0)
    ((((hF.setVar (y := "tq") (by decide) q).setVar (y := "tl") (by decide) ℓ).setVar (y := "tl1") (by decide)
      (ℓ + 1)).setVar (y := "fp") (by decide) pre.length) (evalB_lit (by omega))
    (by simp [τ4, τ3, τ2, τ1, hA "OB"]; omega) (by omega)
  set τ6 := τ5.setVar "fc" 0
  have r6 : Run (W + 1) (.assign "fc" (.lit 0)) τ5 τ6 2 := Run.assign (evalB_lit (by omega))
  have v6 : ∀ y, y ∉ ["tq", "tl", "tl1", "fp", "po", "fc"] → τ6.vars y = τ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [τ6, vars_setVar, hy.2.2.2.2.2, if_false]
    rw [o5.vars y (by simp [hy.2.2.2.2.1])]
    simp [τ4, τ3, τ2, τ1, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]
  have a6 : ∀ b, b ≠ "OB" → τ6.arrs b = τ.arrs b := fun b hb => by
    simp only [τ6, arrs_setVar]; rw [o5.arrs b hb]; simp [τ4, τ3, τ2, τ1]
  have l6 : (τ6.arrs "OB").length = W + 1 := by simp [τ6]; rw [o5.len]; simp [τ4, τ3, τ2, τ1, hA "OB"]
  have hq6 : τ6.vars "tq" = q := by simp [τ6]; rw [o5.vars "tq" (by decide)]; simp [τ4, τ3, τ2, τ1]
  have hl6 : τ6.vars "tl" = ℓ := by simp [τ6]; rw [o5.vars "tl" (by decide)]; simp [τ4, τ3, τ2]
  have hl16 : τ6.vars "tl1" = ℓ + 1 := by simp [τ6]; rw [o5.vars "tl1" (by decide)]; simp [τ4, τ3]
  have hfp6 : τ6.vars "fp" = pre.length := by simp [τ6]; rw [o5.vars "fp" (by decide)]; simp [τ4]
  -- the loop
  set PG := ((ws.drop kl).take kn).map fun w => (w.getD 0 0, w.getD 1 0)
  set OW := (ws.drop ol).take kn
  have hPGl : PG.length = kn := by simp [PG]; omega
  have hOWl : OW.length = kn := by simp [OW]; omega
  have hPGj : ∀ j (hj : j < kn), PG[j]'(by omega) = (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0) := by
    intro j hj; simp [PG]
  have hOWj : ∀ j (hj : j < kn), OW[j]'(by omega) = ws[ol + j] := by intro j hj; simp [OW]
  have hOWt : total OW ≤ total ws := by
    exact total_sub ((List.take_sublist kn _).trans (List.drop_sublist ol ws))
  let I : ℕ → Env → Prop := fun j ρ =>
    Filled "OB" "po" (pre ++ [0] ++ frames (kidW q ℓ i (PG.take j) (OW.take j))) ρ ∧
    ρ.vars "fc" = (kidW q ℓ i (PG.take j) (OW.take j)).length ∧
    (kidW q ℓ i (PG.take j) (OW.take j)).length ≤ j ∧
    (frames (kidW q ℓ i (PG.take j) (OW.take j))).length ≤ total (OW.take j) ∧
    OFr τ6 ρ kbV
  have hI0 : I 0 (τ6.setVar "tj" 0) := ⟨by simpa [kidW, frames] using
      (F5.setVar (y := "fc") (by decide) 0).setVar (y := "tj") (by decide) 0,
    by simp [τ6, kidW], by simp [kidW], by simp [kidW, frames, total], (OFr.setVar τ6 "tj" 0).mono (by decide)⟩
  obtain ⟨τ7, r7, ⟨F7, c7, -, fl7, o7⟩, -⟩ := forUp_run_sum (B := W + 1) (i := "tj") (e := .var "kn")
    (body := kidBody) (N := kn) (fun j => 20 * (ws.getD (ol + j) []).length + 200) I (σ := τ6) (by omega)
    (fun j _ ρ hI _ => ev_var (by rw [hI.2.2.2.2.vars _ (by decide), v6 _ (by decide), hknv]) (by omega))
    hI0
    (by
      rintro j hj ρ ⟨Fρ, cρ, nρ, fρ, oρ⟩ hjρ
      have kv : ∀ y ∈ ["kl", "ol", "ii", "tq", "tl", "tl1", "fp", "kn"], ρ.vars y = τ6.vars y :=
        fun y hy => oρ.vars y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have wρ : WordsAt ws ρ := hw.of_arrs (by rw [oρ.arrs _ (by decide), a6 _ (by decide)])
        (by rw [oρ.arrs _ (by decide), a6 _ (by decide)]) (by rw [oρ.arrs _ (by decide), a6 _ (by decide)])
      have hsT := total_take_drop_succ (ws := ws) (ol := ol) (j := j) (by omega)
      have htl : total (OW.take (j + 1)) ≤ total ws :=
        total_sub ((List.take_sublist (j + 1) OW).trans ((List.take_sublist kn _).trans
          (List.drop_sublist ol ws)))
      have hOWtk1' : OW.take (j + 1) = (ws.drop ol).take (j + 1) := by simp [OW, List.take_take]; omega
      rw [hOWtk1'] at htl
      have hOWtk : OW.take j = (ws.drop ol).take j := by simp [OW, List.take_take]; omega
      have hOWtk1 : OW.take (j + 1) = (ws.drop ol).take (j + 1) := by simp [OW, List.take_take]; omega
      obtain ⟨ρ', r', F', c', o'⟩ := kidBody_run (W := W) (q := q) (ℓ := ℓ) (c := (kidW q ℓ i (PG.take j)
          (OW.take j)).length) wρ
        (by rw [kv "kl" (by simp), v6 _ (by decide), hklv]) (by rw [kv "ol" (by simp), v6 _ (by decide), holv])
        hjρ (by rw [kv "ii" (by simp), v6 _ (by decide), hiv]) (by rw [kv "tq" (by simp), hq6])
        (by rw [kv "tl" (by simp), hl6])
        (by rw [kv "tl1" (by simp), hl16])
        (by omega) (by omega) Fρ cρ
        (by rw [oρ.len, l6]) (by rw [oρ.arrs _ (by decide), a6 _ (by decide), hA "a"])
        (by simp only [List.length_append, List.length_singleton]; have := le_trans fρ (le_of_eq (congrArg total hOWtk)); omega) hT hent
        (by omega) (by omega) bl (by omega)
      refine ⟨ρ', ?_, ?_, ?_⟩
      · rwa [List.getD_eq_getElem _ _ (by omega)]
      · rw [o'.vars _ (by decide), hjρ]
      · have hst := kidSel_take_succ q ℓ i (PG := PG) (OW := OW) (j := j) (by omega) (by omega)
        rw [hPGj j hj, hOWj j hj] at hst
        have hfk := frames_kidSel_le q ℓ i (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0) ws[ol + j]
        have hlk : (kidSel q ℓ i (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0) ws[ol + j]).toList.length ≤ 1 := by
          cases kidSel q ℓ i (ws[kl + j].getD 0 0, ws[kl + j].getD 1 0) ws[ol + j] <;> simp
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hst, frames_append, ← List.append_assoc]; exact F'.setVar (by decide) _
        · simp [hst, c']
        · rw [hst, List.length_append]; omega
        · rw [hst, frames_append, List.length_append, hOWtk1, hsT]
          have := le_trans fρ (le_of_eq (congrArg total hOWtk)); omega
        · exact (oρ.trans (o'.trans (OFr.setVar ρ' "tj" _))).mono (by decide))
  -- the count
  have hfin : (pre ++ [0] ++ frames (kidW q ℓ i (PG.take kn) (OW.take kn))).length ≤ W := by
    simp only [List.length_append, List.length_singleton]
    have : total (OW.take kn) ≤ total ws := by
      rw [List.take_of_length_le (by omega)]; exact hOWt
    omega
  obtain ⟨τ8, r8, F8, o8⟩ := patch_run (W := W) (pre := pre) F7
    (by rw [o7.vars "fp" (by decide), hfp6]) c7 hfin
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at F8
  have hsum := sum_len_drop (ws := ws) (ol := ol) kn hol
  refine ⟨τ8, ?_, F8, ?_⟩
  · unfold kidCmd
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Expr.size, pow_zero, Nat.mul_one]
    simp only [OW]
    generalize total (List.take kn (List.drop ol ws)) = T1
    generalize total (List.take kn (List.drop kl ws)) = T2
    clear * -
    omega
  · have oall := (((((((OFr.setVar τ "tq" q).trans (OFr.setVar τ1 "tl" ℓ)).trans (OFr.setVar τ2 "tl1" _)).trans
      (OFr.setVar τ3 "fp" _)).trans o5).trans (OFr.setVar τ5 "fc" 0)).trans o7).trans o8
    have hsub : ∀ y ∈ ["tq"] ++ ["tl"] ++ ["tl1"] ++ ["fp"] ++ ["po"] ++ ["fc"] ++ kbV ++ [], y ∈ kidV := by
      decide
    refine ⟨fun y hy => oall.vars y (fun h => hy (hsub y h)), fun b hb => oall.arrs b
      (by intro h; subst h; simp [keepA] at hb), fun b => ?_, oall.out, oall.inp⟩
    by_cases hb : b = "OB"
    · subst hb; exact oall.len
    · rw [oall.arrs b hb]

/-- A layout for the children query. -/
def kidLayout : Lax808846Proofs.Compile.Layout :=
  ⟨kidV ++ ["ow", "ii", "kl", "kn", "ol"], ["a", "st", "ln", "OB"], 6⟩

theorem kidCmd_ok : Lax808846Proofs.Compile.Com.Ok kidLayout kidCmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
