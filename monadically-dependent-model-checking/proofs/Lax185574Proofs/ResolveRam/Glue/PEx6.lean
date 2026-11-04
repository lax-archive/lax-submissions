import Lax185574Proofs.ResolveRam.Glue.PEx5

/-!
The third part of the expansion of lem:resolve-lift: the far extensions.

For every answer `cw` of a composition (the library words `cl + z`,
`z < cn`), `part3` checks that its tree has depth `q` and arity `ℓ + 1`
and then runs the guard loop `gLoop` on it (`part3_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- The guards of one composition answer. -/
def p3Emit : Com :=
  .seq (.assign "th0" (.get "a" (.get "st" (.var "tc")))) (.seq (.assign "tsS" (.add (.get "st" (.var "tc")) (.lit 3)))
    (.seq (.assign "tsN" (.sub (.get "ln" (.var "tc")) (.lit 3))) (.seq (.assign "tp1" (.var "tsS"))
      (.seq (.assign "tp2" (.var "tsS")) gLoop))))

/-- One composition answer. -/
def p3Body : Com :=
  .seq (.assign "tc" (.add (.var "cl") (.var "tz"))) (.seq (sget "tO1" "tc" 1) (.seq (sget "tO2" "tc" 2)
    (.ite (.eq (.var "tO1") (.var "tqq")) (.ite (.eq (.var "tO2") (.var "tl1")) p3Emit .skip) .skip)))

/-- The far extensions. -/
def part3 : Com := forUp "tz" (.var "cn") p3Body

/-- The scalars that `part3` writes. -/
def p3V : List String := ["tc", "tO1", "tO2", "th0", "tsS", "tsN", "tp1", "tp2", "tz"] ++ gLV

/-- The words of the guards of a composition answer. -/
def newG (Dw : DW) (R i q ℓ : ℕ) (cw : List ℕ) : List (List ℕ) :=
  if cw.getD 1 0 = q ∧ cw.getD 2 0 = ℓ + 1 then (guardW Dw R ℓ (listWords cw 3) cw).map (i :: ·) else []

theorem flatMap_take_succ' {C : List (List ℕ)} {z : ℕ} (hz : z < C.length) (f : List ℕ → List (List ℕ)) :
    (C.take (z + 1)).flatMap f = (C.take z).flatMap f ++ f C[z] := flatMap_take_succ hz f

/-- The scalars that `p3Emit` writes. -/
def p3eV : List String := ["th0", "tsS", "tsN", "tp1", "tp2"] ++ gLV

/-- **The guards of one composition answer.** -/
theorem p3Emit_run {W : ℕ} {ws : List (List ℕ)} {n : ℕ} {ν : TypeTree} {pre : List ℕ}
    {Dw : DW} {R i q ℓ c : ℕ} {τ : Env} (hw : WordsAt ws τ) (hn : n < ws.length) (htc : τ.vars "tc" = n)
    (hν : ws[n] = toWord ν) (hq : ν.q = q) (hl : ν.ℓ = ℓ + 1) (hi : τ.vars "ii" = i)
    (h1 : τ.vars "th1" = q) (h2 : τ.vars "th2" = ℓ + 1)
    (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q) (hcP : τ.vars "tcP" = bv Dw.cP)
    (hcQ : τ.vars "tcQ" = bv Dw.cQ) (hi2 : τ.vars "ti2" = ℓ) (hs : τ.vars "ts" = R) (hL : τ.vars "tL" = ℓ)
    (hF : Filled "OB" "po" pre τ) (hpc : τ.vars "pc" = c) (hOB : (τ.arrs "OB").length = W + 1)
    (hal : (τ.arrs "a").length = W + 1)
    (hT : total ws + ws.length + 10 ≤ W) (hv : ∀ u ∈ ws[n], u ≤ W)
    (hcap : pre.length + ℓ * (ws[n].length + 3) ≤ W) (hik : i ≤ W)
    (hc : c + ℓ + 1 ≤ W) (hPB : Dw.P < W + 1) (hQB : Dw.Q < W + 1) (hR : 2 * R + 4 < W + 1) :
    ∃ τ', Run (W + 1) p3Emit τ τ' (ℓ * (hopK (2 * ws[n].length) R + 20 * ws[n].length + 100) + 40) ∧
      Filled "OB" "po" (pre ++ frames ((guardW Dw R ℓ (listWords ws[n] 3) ws[n]).map (i :: ·))) τ' ∧
      τ'.vars "pc" = c + (guardW Dw R ℓ (listWords ws[n] 3) ws[n]).length ∧ OFr τ τ' p3eV := by
  have hoff := off_add_le hn
  have hd0 := drop_off hw hn
  rw [hν] at hd0
  obtain ⟨r₁, hd₁, hl₁, hm₁⟩ := tree_atoms hd0
  set A := (Node.atoms ν.root).words
  have hlw : (toWord ν).length = ws[n].length := by rw [hν]
  have hl3 : 3 ≤ ws[n].length := by rw [hν, toWord_typeTree]; simp
  have hAl : A.length < (toWord A).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  set b := off ws n
  have hst := hw.st n hn
  have hln := hw.ln n hn
  have e0 : (τ.arrs "a")[b]? = some ν.k := by
    have := hw.a n hn 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; simp [hν, toWord_typeTree]
  have bk : ν.k ≤ W := hv _ (by rw [hν, toWord_typeTree]; simp)
  have bq : q ≤ W := by rw [← hq]; exact hv _ (by rw [hν, toWord_typeTree]; simp)
  have bl : ℓ + 1 ≤ W := by rw [← hl]; exact hv _ (by rw [hν, toWord_typeTree]; simp)
  set τ1 := τ.setVar "th0" ν.k
  have r1 : Run (W + 1) (.assign "th0" (.get "a" (.get "st" (.var "tc")))) τ τ1 4 :=
    (Run.assign (evalB_get (evalB_get (ev_var htc (by omega)) hst (by omega)) e0 (by omega))).mono
      (by simp [Expr.size])
  set τ2 := τ1.setVar "tsS" (b + 3)
  have r2 : Run (W + 1) (.assign "tsS" (.add (.get "st" (.var "tc")) (.lit 3))) τ1 τ2 5 :=
    (Run.assign (ev_add (evalB_get (ev_var (v := n) (by simp [τ1, htc]) (by omega)) (by simpa [τ1] using hst) (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  set τ3 := τ2.setVar "tsN" (ws[n].length - 3)
  have r3 : Run (W + 1) (.assign "tsN" (.sub (.get "ln" (.var "tc")) (.lit 3))) τ2 τ3 5 :=
    (Run.assign (ev_sub (evalB_get (ev_var (v := n) (by simp [τ2, τ1, htc]) (by omega)) (by simpa [τ2, τ1] using hln)
      (by omega)) (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  set τ4 := τ3.setVar "tp1" (b + 3)
  have r4 : Run (W + 1) (.assign "tp1" (.var "tsS")) τ3 τ4 2 :=
    Run.assign (ev_var (by simp [τ3, τ2]) (by omega))
  set τ5 := τ4.setVar "tp2" (b + 3)
  have r5 : Run (W + 1) (.assign "tp2" (.var "tsS")) τ4 τ5 2 :=
    Run.assign (ev_var (by simp [τ4, τ3, τ2]) (by omega))
  have kv : ∀ y ∈ ["ii", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL", "pc", "po"],
      τ5.vars y = τ.vars y := fun y hy => by
    have : y ≠ "tp2" ∧ y ≠ "tp1" ∧ y ≠ "tsN" ∧ y ≠ "tsS" ∧ y ≠ "th0" := by
      simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [τ5, τ4, τ3, τ2, τ1, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]
  have a5 : τ5.arrs = τ.arrs := by simp [τ5, τ4, τ3, τ2, τ1]
  have H5 : HopAt "a" "a" (τ.arrs "a") (τ.arrs "a") A A (b + 3) (b + 3) Dw (τ5.vars "ti1") ℓ R τ5 :=
    ⟨by rw [a5], by rw [a5], by simp [τ5, τ4], by simp [τ5], by rw [kv "tP" (by simp), hP],
      by rw [kv "tQ" (by simp), hQ], by rw [kv "tcP" (by simp), hcP], by rw [kv "tcQ" (by simp), hcQ], rfl,
      by rw [kv "ti2" (by simp), hi2], by rw [kv "ts" (by simp), hs]⟩
  have hseg : seg (τ5.arrs "a") (b + 3) (ws[n].drop 3).length = ws[n].drop 3 := by
    rw [a5, List.length_drop]; exact seg_word hw hn hl3
  have E5 : EmAt i (τ5.vars "tG") ν.k q (ℓ + 1) (b + 3) (ws[n].drop 3) τ5 :=
    ⟨by rw [kv "ii" (by simp), hi], rfl, by simp [τ5, τ4, τ3, τ2, τ1], by rw [kv "th1" (by simp), h1],
      by rw [kv "th2" (by simp), h2], by simp [τ5, τ4, τ3, τ2], by simp [τ5, τ4, τ3, List.length_drop], hseg⟩
  have hcw : ws[n] = [ν.k, q, ℓ + 1] ++ ws[n].drop 3 := by
    rw [hν, toWord_typeTree, ← hq, ← hl]; rfl
  obtain ⟨τ6, r6, F6, c6, o6⟩ := gLoop_run (W := W) (c := c) H5 hd₁ E5 (by rw [kv "tL" (by simp), hL])
    (hF.congr (kv "po" (by simp)) (by rw [a5])) (by rw [kv "pc" (by simp), hpc]) (by rw [a5, hOB])
    (by rw [a5, hal, List.length_drop]; omega)
    (by rw [List.length_drop, show ws[n].length - 3 + 6 = ws[n].length + 3 by omega]; exact hcap)
    (by rw [List.length_drop]; omega)
    (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | hx
      · exact hik
      · exact bk
      · omega
      · omega
      · exact hv x (List.mem_of_mem_drop hx))
    hc (by omega) (fun v h => by have := hv v (by rw [hν]; exact hm₁ v h); omega) hPB hQB (by omega) hR
  rw [← hcw] at F6 c6
  have hA : listWords ws[n] 3 = A := by rw [hν, listWords_tree_root]
  refine ⟨τ6, ?_, by rw [hA]; exact F6, by rw [hA]; exact c6, ?_⟩
  · unfold p3Emit
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    have h1 := exHopK_mono (L := A.length + A.length) (L' := 2 * ws[n].length) (R := R) (by omega)
    have := Nat.mul_le_mul_left ℓ (show hopK (A.length + A.length) R + 20 * (ws[n].drop 3).length + 100 ≤
      hopK (2 * ws[n].length) R + 20 * ws[n].length + 100 by rw [List.length_drop]; omega)
    omega
  · exact ((((((OFr.setVar τ "th0" _).trans (OFr.setVar τ1 "tsS" _)).trans (OFr.setVar τ2 "tsN" _)).trans
      (OFr.setVar τ3 "tp1" _)).trans (OFr.setVar τ4 "tp2" _)).trans o6).mono (by decide)

set_option maxHeartbeats 1000000 in
/-- **The far extensions.** -/
theorem part3_run {W : ℕ} {ws : List (List ℕ)} {cl cn : ℕ} {pre : List ℕ}
    {Dw : DW} {R i q ℓ c₀ : ℕ} {τ : Env} (hw : WordsAt ws τ) (hcl : τ.vars "cl" = cl)
    (hcn : τ.vars "cn" = cn) (hcc : cl + cn ≤ ws.length)
    (hC : ∀ w ∈ (ws.drop cl).take cn, ∃ ν : TypeTree, w = toWord ν) (hi : τ.vars "ii" = i)
    (hqq : τ.vars "tqq" = q) (hl1 : τ.vars "tl1" = ℓ + 1)
    (h1 : τ.vars "th1" = q) (h2 : τ.vars "th2" = ℓ + 1)
    (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q) (hcP : τ.vars "tcP" = bv Dw.cP)
    (hcQ : τ.vars "tcQ" = bv Dw.cQ) (hi2 : τ.vars "ti2" = ℓ) (hs : τ.vars "ts" = R) (hL : τ.vars "tL" = ℓ)
    (hF : Filled "OB" "po" pre τ) (hpc : τ.vars "pc" = c₀) (hOB : (τ.arrs "OB").length = W + 1)
    (hal : (τ.arrs "a").length = W + 1)
    (hT : total ws + ws.length + 10 ≤ W) (hv : ∀ n (hn : n < ws.length), ∀ u ∈ ws[n], u ≤ W)
    (hcap : pre.length + ℓ * (4 * total ws + 4 * ws.length) ≤ W) (hik : i ≤ W ∧ q ≤ W ∧ ℓ + 1 ≤ W)
    (hc : c₀ + ℓ * (cn + 1) + 1 ≤ W) (hPB : Dw.P < W + 1) (hQB : Dw.Q < W + 1)
    (hR : 2 * R + 4 < W + 1) :
    ∃ τ', Run (W + 1) part3 τ τ' (cn * (ℓ * (hopK (2 * total ((ws.drop cl).take cn)) R +
        20 * total ((ws.drop cl).take cn) + 100) + 120) + 10) ∧
      Filled "OB" "po" (pre ++ frames (((ws.drop cl).take cn).flatMap (newG Dw R i q ℓ))) τ' ∧
      τ'.vars "pc" = c₀ + (((ws.drop cl).take cn).flatMap (newG Dw R i q ℓ)).length ∧ OFr τ τ' p3V := by
  set C := (ws.drop cl).take cn
  set T := total ws
  set N := newG Dw R i q ℓ
  have hCl : C.length = cn := by simp [C]; omega
  have hCz : ∀ z (hz : z < cn), C[z]'(by omega) = ws[cl + z] := fun z hz => by simp [C]
  have hlen_le : ∀ n (hn : n < ws.length), ws[n].length ≤ T := fun n hn => by
    have := off_add_le hn; simp only [T]; omega
  set TC := total C
  have hlenC : ∀ z (hz : z < cn), ws[cl + z].length ≤ TC := fun z hz => by
    rw [← hCz z hz]
    simp only [TC, total]
    rw [List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem _))
  let I : ℕ → Env → Prop := fun z ρ =>
    Filled "OB" "po" (pre ++ frames ((C.take z).flatMap N)) ρ ∧
    ρ.vars "pc" = c₀ + ((C.take z).flatMap N).length ∧ ((C.take z).flatMap N).length ≤ ℓ * z ∧
    (frames ((C.take z).flatMap N)).length ≤ ℓ * (total (C.take z) + 3 * z) ∧ OFr τ ρ p3V
  have kP : ∀ y ∈ ["cl", "cn", "ii", "tqq", "tl1", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL"],
      y ∉ p3V := by decide
  obtain ⟨τ', r', ⟨F', c', -, -, o'⟩, -⟩ := forUp_run (B := W + 1) (i := "tz") (e := .var "cn") (body := p3Body)
    (N := cn) (K := ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 100) I (σ := τ) (by omega)
    (fun z _ ρ hI _ => ev_var (by rw [hI.2.2.2.2.vars _ (by decide), hcn]) (by omega))
    ⟨by simpa [frames] using hF.setVar (y := "tz") (by decide) 0, by simp [hpc], by simp,
      by simp [frames, total], (OFr.setVar τ "tz" 0).mono (by decide)⟩
    (by
      rintro z hz ρ ⟨Fρ, cρ, nρ, fρ, oρ⟩ hzρ
      have kv : ∀ y ∈ ["cl", "cn", "ii", "tqq", "tl1", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL"],
          ρ.vars y = τ.vars y := fun y hy => oρ.vars y (kP y hy)
      have wρ : WordsAt ws ρ := hw.of_arrs (by rw [oρ.arrs _ (by decide)]) (by rw [oρ.arrs _ (by decide)])
        (by rw [oρ.arrs _ (by decide)])
      set n := cl + z
      have hn : n < ws.length := by omega
      obtain ⟨ν, hν⟩ := hC C[z] (List.getElem_mem (by omega))
      rw [hCz z hz] at hν
      have hoff := off_add_le hn
      have hvn : ∀ u ∈ ws[n], u < W + 1 := fun u h => by have := hv n hn u h; omega
      set ρ1 := ρ.setVar "tc" n
      have r1 : Run (W + 1) (.assign "tc" (.add (.var "cl") (.var "tz"))) ρ ρ1 4 :=
        (Run.assign (ev_add (ev_var (by rw [kv "cl" (by simp), hcl]) (by omega)) (ev_var hzρ (by omega))
          (by omega))).mono (by simp [Expr.size])
      have w1 : WordsAt ws ρ1 := wρ.of_arrs (by simp [ρ1]) (by simp [ρ1]) (by simp [ρ1])
      have r2 := sget_run (B := W + 1) w1 (v := "tO1") (x := "tc") (j := 1) (by simp [ρ1]) hn (by omega) hvn
      set ρ2 := ρ1.setVar "tO1" (ws[n].getD 1 0)
      have w2 : WordsAt ws ρ2 := wρ.of_arrs (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1])
      have r3 := sget_run (B := W + 1) w2 (v := "tO2") (x := "tc") (j := 2) (by simp [ρ2, ρ1]) hn (by omega) hvn
      set ρ3 := ρ2.setVar "tO2" (ws[n].getD 2 0)
      have hg1 : ws[n].getD 1 0 = ν.q := by rw [hν, toWord_typeTree]; rfl
      have hg2 : ws[n].getD 2 0 = ν.ℓ := by rw [hν, toWord_typeTree]; rfl
      have hνq : ν.q ≤ W := hv n hn _ (by rw [hν, toWord_typeTree]; simp)
      have hνl : ν.ℓ ≤ W := hv n hn _ (by rw [hν, toWord_typeTree]; simp)
      have c1 : (Cond.eq (.var "tO1") (.var "tqq")).evalB (W + 1) ρ3 = some (ν.q == q) :=
        evalB_condEq (ev_var (x := "tO1") (v := ν.q) (by rw [← hg1]; simp [ρ3, ρ2]) (by omega))
          (ev_var (by simp [ρ3, ρ2, ρ1]; rw [kv "tqq" (by simp), hqq]) (by omega))
      have c2 : (Cond.eq (.var "tO2") (.var "tl1")).evalB (W + 1) ρ3 = some (ν.ℓ == ℓ + 1) :=
        evalB_condEq (ev_var (x := "tO2") (v := ν.ℓ) (by rw [← hg2]; simp [ρ3]) (by omega))
          (ev_var (by simp [ρ3, ρ2, ρ1]; rw [kv "tl1" (by simp), hl1]) (by omega))
      have hfs := flatMap_take_succ' (C := C) (z := z) (by omega) N
      rw [hCz z hz] at hfs
      have hTs : total (C.take (z + 1)) = total (C.take z) + ws[n].length := by
        have h1 : C.take (z + 1) = (ws.drop cl).take (z + 1) := by simp [C, List.take_take]; omega
        have h2 : C.take z = (ws.drop cl).take z := by simp [C, List.take_take]; omega
        rw [h1, h2, total_take_drop_succ (by omega)]
      have hTC : total (C.take (z + 1)) ≤ T := total_sub ((List.take_sublist _ _).trans
        ((List.take_sublist _ _).trans (List.drop_sublist _ _)))
      have hwT : ws.length ≤ ws.length := le_refl _
      have k3 : ∀ y ∈ ["tz", "cn"], ρ3.vars y = ρ.vars y := fun y hy => by
        simp at hy; rcases hy with rfl | rfl <;> simp [ρ3, ρ2, ρ1]
      by_cases hb : ν.q = q ∧ ν.ℓ = ℓ + 1
      · obtain ⟨hbq, hbl⟩ := hb
        have w3 : WordsAt ws ρ3 := wρ.of_arrs (by simp [ρ3, ρ2, ρ1]) (by simp [ρ3, ρ2, ρ1]) (by simp [ρ3, ρ2, ρ1])
        have k3' : ∀ y ∈ ["ii", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL"], ρ3.vars y = τ.vars y :=
          fun y hy => by
            have : y ≠ "tO2" ∧ y ≠ "tO1" ∧ y ≠ "tc" := by
              simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
            simp only [ρ3, ρ2, ρ1, vars_setVar, this.1, this.2.1, this.2.2, if_false]
            exact kv y (by simp at hy ⊢; tauto)
        have hlenS : c₀ + ((C.take z).flatMap N).length + ℓ + 1 ≤ W := by
          have : ℓ * z + ℓ ≤ ℓ * (cn + 1) := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
          omega
        have hcapS : (pre ++ frames ((C.take z).flatMap N)).length + ℓ * (ws[n].length + 3) ≤ W := by
          rw [List.length_append]
          have h1 : ℓ * (total (C.take z) + 3 * z) + ℓ * (ws[n].length + 3) ≤ ℓ * (4 * T + 4 * ws.length) := by
            rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
          omega
        obtain ⟨ρ4, r4, F4, c4, o4⟩ := p3Emit_run (W := W) (q := q) (ℓ := ℓ) (Dw := Dw) (R := R) (i := i)
          (c := c₀ + ((C.take z).flatMap N).length) w3 hn (by simp [ρ3, ρ2, ρ1]) hν hbq hbl
          (by rw [k3' "ii" (by simp), hi]) (by rw [k3' "th1" (by simp), h1]) (by rw [k3' "th2" (by simp), h2])
          (by rw [k3' "tP" (by simp), hP]) (by rw [k3' "tQ" (by simp), hQ]) (by rw [k3' "tcP" (by simp), hcP])
          (by rw [k3' "tcQ" (by simp), hcQ]) (by rw [k3' "ti2" (by simp), hi2]) (by rw [k3' "ts" (by simp), hs])
          (by rw [k3' "tL" (by simp), hL])
          (Fρ.setVar (by decide) _ |>.setVar (by decide) _ |>.setVar (by decide) _)
          (by simp [ρ3, ρ2, ρ1, cρ]) (by simp only [ρ3, ρ2, ρ1, arrs_setVar]; rw [oρ.len, hOB])
          (by simp only [ρ3, ρ2, ρ1, arrs_setVar]; rw [oρ.arrs _ (by decide), hal]) hT (hv n hn) hcapS hik.1
          hlenS hPB hQB hR
        have hNn : N ws[n] = (guardW Dw R ℓ (listWords ws[n] 3) ws[n]).map (i :: ·) := by
          simp only [N, newG, hg1, hg2]; rw [if_pos ⟨hbq, hbl⟩]
        have hgl := length_guardW_le Dw R ℓ (listWords ws[n] 3) ws[n]
        refine ⟨ρ4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold p3Body
          refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_true (by rw [c1]; simp [hbq])
            (Run.ite_true (by rw [c2]; simp [hbl]) r4))))).mono ?_
          have hlz : ws[n].length ≤ TC := hlenC z hz
          have h1 := exHopK_mono (L := 2 * ws[n].length) (L' := 2 * TC) (R := R) (by omega)
          have := Nat.mul_le_mul_left ℓ (show hopK (2 * ws[n].length) R + 20 * ws[n].length + 100 ≤
            hopK (2 * TC) R + 20 * TC + 100 by omega)
          simp only [Cond.size, Expr.size]
          omega
        · rw [o4.vars _ (by decide)]; simp [ρ3, ρ2, ρ1, hzρ]
        · rw [hfs, hNn, frames_append, ← List.append_assoc]; exact F4.setVar (by decide) _
        · simp only [vars_setVar, show ("pc" : String) ≠ "tz" by decide, if_false]
          rw [c4, hfs, hNn, List.length_append, List.length_map]; omega
        · rw [hfs, hNn, List.length_append, List.length_map, Nat.mul_succ]; omega
        · rw [hfs, hNn, frames_append, List.length_append, length_frames_oldG, hTs]
          have h3 := Nat.mul_le_mul_right (ws[n].length + 3) hgl
          have h5 : ℓ * (total (C.take z) + 3 * z) + ℓ * (ws[n].length + 3) =
              ℓ * (total (C.take z) + ws[n].length + 3 * (z + 1)) := by ring
          omega
        · exact (oρ.trans ((((OFr.setVar ρ "tc" _).trans (OFr.setVar ρ1 "tO1" _)).trans
            (OFr.setVar ρ2 "tO2" _)).trans (o4.trans (OFr.setVar ρ4 "tz" _)))).mono (by decide)
      · have hN : N ws[n] = [] := by
          simp only [N, newG, hg1, hg2]; rw [if_neg (by tauto)]
        have hrun : Run (W + 1) p3Body ρ ρ3 (K := 50) := by
          unfold p3Body
          by_cases h1 : ν.q = q
          · have h2 : ¬ ν.ℓ = ℓ + 1 := fun h => hb ⟨h1, h⟩
            exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_true (by rw [c1]; simp [h1])
              (Run.ite_false (by rw [c2]; simp [h2]) Run.skip))))).mono (by simp [Cond.size, Expr.size])
          · exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_false (by rw [c1]; simp [h1]) Run.skip)))).mono
              (by simp [Cond.size, Expr.size])
        refine ⟨ρ3, hrun.mono (by omega), by rw [k3 "tz" (by simp), hzρ], ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfs, hN, List.append_nil]
          exact (Fρ.setVar (by decide) _ |>.setVar (by decide) _ |>.setVar (by decide) _).setVar (by decide) _
        · simp only [vars_setVar, show ("pc" : String) ≠ "tz" by decide, if_false, ρ3, ρ2, ρ1,
            show ("pc" : String) ≠ "tO2" by decide, show ("pc" : String) ≠ "tO1" by decide,
            show ("pc" : String) ≠ "tc" by decide]
          rw [cρ, hfs, hN, List.append_nil]
        · rw [hfs, hN, List.append_nil, Nat.mul_succ]; omega
        · rw [hfs, hN, List.append_nil, hTs]
          have : ℓ * (total (C.take z) + 3 * z) ≤ ℓ * (total (C.take z) + ws[n].length + 3 * (z + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        · exact (oρ.trans ((((OFr.setVar ρ "tc" _).trans (OFr.setVar ρ1 "tO1" _)).trans
            (OFr.setVar ρ2 "tO2" _)).trans (OFr.setVar ρ3 "tz" _))).mono (by decide))
  refine ⟨τ', r'.mono ?_, by rwa [List.take_of_length_le (by omega)] at F',
    by rwa [List.take_of_length_le (by omega)] at c', o'⟩
  simp only [Expr.size]
  rw [show ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 100 + 1 + 7 = ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 108 by
    omega]
  have := Nat.mul_le_mul_left cn (show ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 108 ≤
    ℓ * (hopK (2 * TC) R + 20 * TC + 100) + 120 by omega)
  omega


end Lax185574Proofs.ResolveRam.Glue
