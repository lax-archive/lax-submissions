import Mathlib.Tactic
import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax457868Proofs.SaturatedCutoff
import Lax457868Proofs.SaturatedCutoffSource
import Lax457868Proofs.DrawLogSetup

/-!
Fixed IMP+ source for the refined Welzl cutoff. The polynomial is evaluated
through the guarded multiplication and addition commands, with all
intermediates capped at the input size.
-/

namespace Lax457868Proofs.RefinedCutoffSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.SaturatedCutoffSource
open Lax457868Proofs.DrawLogSetup

/-- Saturating multiply source with named inputs and destination. -/
def satMulTo (x y dest : String) : Com :=
  seqs [
    .assign "cutA" (.var x),
    .assign "cutB" (.var y),
    satMulCommand,
    .assign dest (.var "cutResult")]

/-- Saturating add source with named inputs and destination. -/
def satAddTo (x y dest : String) : Com :=
  seqs [
    .assign "cutA" (.var x),
    .assign "cutB" (.var y),
    satAddCommand,
    .assign dest (.var "cutResult")]

/-- The fixed straight-line guarded arithmetic for the cutoff polynomial. -/
def cutoffArithmetic : Com :=
  seqs [
    .assign "cutOne" (.lit 1),
    .assign "cutTwo" (.lit 2),
    .assign "cut64" (.lit 64),
    .assign "cut768" (.lit 768),
    satMulTo "c" "c" "cutC2",
    satMulTo "cutC2" "c" "cutC3",
    satMulTo "cutC3" "c" "cutC4",
    satMulTo "cutC4" "c" "cutC5",
    satMulTo "cut64" "L" "cutS",
    satAddTo "cutS" "cutOne" "cutSPlusOne",
    satMulTo "cut768" "cutC5" "cutP",
    satMulTo "cutP" "cutSPlusOne" "cutQ",
    satMulTo "cutQ" "L" "cutR",
    satAddTo "cutR" "cutOne" "cutK",
    satMulTo "cutTwo" "cutK" "cutoffResult"]

/-- Fixed source for the conditional base-case cutoff. The log setup is
executed only when `c < n`; otherwise the result is immediately `n`. -/
def refinedCutoffSource : Com :=
  (Com.assign "drawModulus" (.var "c")).seq
    (Com.ite (.lt (.var "c") (.var "n"))
      (seqs [drawLogSetup, cutoffArithmetic])
      (.assign "cutoffResult" (.var "n")))

private lemma assignVar {B : ℕ} {σ : Env} (x y : String)
    (hy : σ.vars y < B) :
    Run B (.assign x (.var y)) σ (σ.setVar x (σ.vars y)) 2 := by
  simpa using Run.assign (x := x) (evalB_var (x := y) hy)

/-- A named multiplication call costs at most 20 IMP+ steps. -/
lemma satMulTo_run {B : ℕ} {σ : Env} (x y dest : String)
    (hn : σ.vars "n" < B) (hx : σ.vars x < B) (hy : σ.vars y < B)
    (hyA : y ≠ "cutA") :
    ∃ σ', Run B (satMulTo x y dest) σ σ' 20 ∧
      σ'.vars dest = satMul (σ.vars "n") (σ.vars x) (σ.vars y) ∧
      (∀ z, z ≠ "cutA" → z ≠ "cutB" → z ≠ "cutResult" → z ≠ dest →
        σ'.vars z = σ.vars z) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₁ := σ.setVar "cutA" (σ.vars x)
  let σ₂ := σ₁.setVar "cutB" (σ.vars y)
  have hA : Run B (.assign "cutA" (.var x)) σ σ₁ 2 := by
    simpa [σ₁] using assignVar "cutA" x hx
  have hy₂ : σ₂.vars "cutB" = σ.vars y := by simp [σ₂, σ₁]
  have hcutA₂ : σ₂.vars "cutA" = σ.vars x := by simp [σ₂, σ₁]
  have hB : Run B (.assign "cutB" (.var y)) σ₁ σ₂ 2 := by
    have he : (Expr.var y).evalB B σ₁ = some (σ.vars y) := by
      have hv : σ₁.vars y = σ.vars y := by simp [σ₁, hyA]
      simpa [hv] using (evalB_var (x := y) hy)
    simpa [σ₂] using Run.assign (x := "cutB") he
  obtain ⟨σ₃, hmul, hval, hframe, harr, hin, hout⟩ :=
    satMulCommand_run (σ := σ₂) (by simpa [σ₂, σ₁] using hn)
      (by rw [hcutA₂]; exact hx)
      (by simpa [hy₂] using hy)
  have hn₂ : σ₂.vars "n" = σ.vars "n" := by simp [σ₂, σ₁]
  have houtBound : σ₃.vars "cutResult" < B := by
    rw [hval]
    exact (satMul_result_le _ _ _).trans_lt hn
  let σ₄ := σ₃.setVar dest (σ₃.vars "cutResult")
  have hD : Run B (.assign dest (.var "cutResult")) σ₃ σ₄ 2 := by
    have he : (Expr.var "cutResult").evalB B σ₃ = some (σ₃.vars "cutResult") :=
      evalB_var houtBound
    simpa [σ₄] using Run.assign (x := dest) he
  have hwhole : Run B (satMulTo x y dest) σ σ₄ 20 := by
    have h := hA.seq (hB.seq (hmul.seq hD))
    simpa [satMulTo, seqs, Nat.add_assoc] using h
  refine ⟨σ₄, hwhole, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [σ₄, vars_setVar, if_pos]
    rw [hval, hn₂, hcutA₂, hy₂]
  · intro z hzA hzB hzR hzd
    have hframeZ := hwhole.frame_var z (by
      simp [satMulTo, seqs, satMulCommand, Com.wvars, hzA, hzB, hzR, hzd])
    simpa [σ₄, hzd] using hframeZ
  · funext a
    exact hwhole.frame_arr a (by simp [satMulTo, seqs, satMulCommand, Com.warrs])
  · exact hwhole.frame_inp (by simp [satMulTo, seqs, satMulCommand, Com.reads])
  · exact hwhole.out_eq (by simp [satMulTo, seqs, satMulCommand, Com.NoWrite])

/-- A named addition call costs at most 20 IMP+ steps. -/
lemma satAddTo_run {B : ℕ} {σ : Env} (x y dest : String)
    (hn : σ.vars "n" < B) (hx : σ.vars x < B) (hy : σ.vars y < B)
    (hyA : y ≠ "cutA") :
    ∃ σ', Run B (satAddTo x y dest) σ σ' 20 ∧
      σ'.vars dest = satAdd (σ.vars "n") (σ.vars x) (σ.vars y) ∧
      (∀ z, z ≠ "cutA" → z ≠ "cutB" → z ≠ "cutResult" → z ≠ dest →
        σ'.vars z = σ.vars z) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₁ := σ.setVar "cutA" (σ.vars x)
  let σ₂ := σ₁.setVar "cutB" (σ.vars y)
  have hA : Run B (.assign "cutA" (.var x)) σ σ₁ 2 := by
    simpa [σ₁] using assignVar "cutA" x hx
  have hB : Run B (.assign "cutB" (.var y)) σ₁ σ₂ 2 := by
    have hv : σ₁.vars y = σ.vars y := by simp [σ₁, hyA]
    have he : (Expr.var y).evalB B σ₁ = some (σ.vars y) := by
      simpa [hv] using (evalB_var (x := y) hy)
    simpa [σ₂] using Run.assign (x := "cutB") he
  have hcutA₂ : σ₂.vars "cutA" = σ.vars x := by simp [σ₂, σ₁]
  have hy₂ : σ₂.vars "cutB" = σ.vars y := by simp [σ₂, σ₁]
  obtain ⟨σ₃, hadd, hval, hframe, harr, hin, hout⟩ :=
    satAddCommand_run (σ := σ₂) (by simpa [σ₂, σ₁] using hn)
      (by rw [hcutA₂]; exact hx) (by rw [hy₂]; exact hy)
  have hn₂ : σ₂.vars "n" = σ.vars "n" := by simp [σ₂, σ₁]
  have houtBound : σ₃.vars "cutResult" < B := by
    rw [hval]
    exact (satAdd_result_le _ _ _).trans_lt hn
  let σ₄ := σ₃.setVar dest (σ₃.vars "cutResult")
  have hD : Run B (.assign dest (.var "cutResult")) σ₃ σ₄ 2 := by
    have he : (Expr.var "cutResult").evalB B σ₃ = some (σ₃.vars "cutResult") :=
      evalB_var houtBound
    simpa [σ₄] using Run.assign (x := dest) he
  have hwhole : Run B (satAddTo x y dest) σ σ₄ 20 := by
    have h := hA.seq (hB.seq (hadd.seq hD))
    simpa [satAddTo, seqs, Nat.add_assoc] using h
  refine ⟨σ₄, hwhole, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [σ₄, vars_setVar, if_pos]
    rw [hval, hn₂, hcutA₂, hy₂]
  · intro z hzA hzB hzR hzd
    have hframeZ := hwhole.frame_var z (by
      simp [satAddTo, seqs, satAddCommand, Com.wvars, hzA, hzB, hzR, hzd])
    simpa [σ₄, hzd] using hframeZ
  · funext a
    exact hwhole.frame_arr a (by simp [satAddTo, seqs, satAddCommand, Com.warrs])
  · exact hwhole.frame_inp (by simp [satAddTo, seqs, satAddCommand, Com.reads])
  · exact hwhole.out_eq (by simp [satAddTo, seqs, satAddCommand, Com.NoWrite])

/-- The guarded polynomial sequence realizes `saturatedWelzlCutoff` with
all arithmetic outputs below `n`. The logarithm word `L` is supplied by
the caller, allowing the surrounding source to run the old log routine. -/
lemma cutoffArithmetic_run {B n c L : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hc : σ.vars "c" = c) (hL : σ.vars "L" = L)
    (hLlog : L = Nat.clog 2 c)
    (hnB : n < B) (hcB : c < B) (hLB : L < B) (h768 : 768 < B) :
    ∃ σ', Run B cutoffArithmetic σ σ' 228 ∧
      σ'.vars "cutoffResult" = saturatedWelzlCutoff n c ∧
      (∀ z, z ≠ "cutOne" → z ≠ "cutTwo" → z ≠ "cut64" → z ≠ "cut768" →
        z ≠ "cutA" → z ≠ "cutB" → z ≠ "cutResult" →
        z ≠ "cutC2" → z ≠ "cutC3" → z ≠ "cutC4" → z ≠ "cutC5" →
        z ≠ "cutS" → z ≠ "cutSPlusOne" → z ≠ "cutP" → z ≠ "cutQ" →
        z ≠ "cutR" → z ≠ "cutK" → z ≠ "cutoffResult" →
        σ'.vars z = σ.vars z) ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₁ := σ.setVar "cutOne" 1
  let σ₂ := σ₁.setVar "cutTwo" 2
  let σ₃ := σ₂.setVar "cut64" 64
  let σ₄ := σ₃.setVar "cut768" 768
  have h1 : Run B (.assign "cutOne" (.lit 1)) σ σ₁ 2 := by
    simpa [σ₁] using Run.assign (evalB_lit (by omega : 1 < B))
  have h2 : Run B (.assign "cutTwo" (.lit 2)) σ₁ σ₂ 2 := by
    simpa [σ₂] using Run.assign (evalB_lit (by omega : 2 < B))
  have h3 : Run B (.assign "cut64" (.lit 64)) σ₂ σ₃ 2 := by
    simpa [σ₃] using Run.assign (evalB_lit (by omega : 64 < B))
  have h4 : Run B (.assign "cut768" (.lit 768)) σ₃ σ₄ 2 := by
    simpa [σ₄] using Run.assign (evalB_lit h768)
  have hsetup : Run B (seqs [
      .assign "cutOne" (.lit 1), .assign "cutTwo" (.lit 2),
      .assign "cut64" (.lit 64), .assign "cut768" (.lit 768)]) σ σ₄ 8 := by
    simpa [seqs] using h1.seq (h2.seq (h3.seq h4))
  have hn₄ : σ₄.vars "n" = n := by simp [σ₄, σ₃, σ₂, σ₁, hn]
  have hc₄ : σ₄.vars "c" = c := by simp [σ₄, σ₃, σ₂, σ₁, hc]
  have hL₄ : σ₄.vars "L" = L := by simp [σ₄, σ₃, σ₂, σ₁, hL]
  have hC2B : 2 < B := by omega
  have h64B : 64 < B := by omega
  have hn₄B : σ₄.vars "n" < B := by rw [hn₄]; exact hnB
  obtain ⟨τ1, r1, v1, f1, a1, i1, o1⟩ :=
    satMulTo_run (B := B) (σ := σ₄) "c" "c" "cutC2"
      (by rw [hn₄]; exact hnB) (by rw [hc₄]; exact hcB) (by rw [hc₄]; exact hcB) (by decide)
  have ne1 : τ1.vars "n" = n := by rw [f1 "n" (by decide) (by decide) (by decide) (by decide), hn₄]
  have ce1 : τ1.vars "c" = c := by rw [f1 "c" (by decide) (by decide) (by decide) (by decide), hc₄]
  have le1 : τ1.vars "L" = L := by rw [f1 "L" (by decide) (by decide) (by decide) (by decide), hL₄]
  have n1 : τ1.vars "n" < B := by
    rw [ne1]; exact hnB
  have c1 : τ1.vars "c" < B := by
    rw [ce1]; exact hcB
  have l1 : τ1.vars "L" < B := by
    rw [le1]; exact hLB
  have C2B : τ1.vars "cutC2" < B := by
    rw [v1]; exact (satMul_result_le _ _ _).trans_lt hn₄B
  have h64₁ : τ1.vars "cut64" = 64 := by
    have h₁ := f1 "cut64" (by decide) (by decide) (by decide) (by decide)
    calc τ1.vars "cut64" = σ₄.vars "cut64" := h₁
      _ = 64 := by simp [σ₄, σ₃, σ₂, σ₁]
  have hone₁ : τ1.vars "cutOne" = 1 := by
    have h₁ := f1 "cutOne" (by decide) (by decide) (by decide) (by decide)
    calc τ1.vars "cutOne" = σ₄.vars "cutOne" := h₁
      _ = 1 := by simp [σ₄, σ₃, σ₂, σ₁]
  have h768₁ : τ1.vars "cut768" = 768 := by
    have h₁ := f1 "cut768" (by decide) (by decide) (by decide) (by decide)
    calc τ1.vars "cut768" = σ₄.vars "cut768" := h₁
      _ = 768 := by simp [σ₄, σ₃, σ₂, σ₁]
  have htwo₁ : τ1.vars "cutTwo" = 2 := by
    have h₁ := f1 "cutTwo" (by decide) (by decide) (by decide) (by decide)
    calc τ1.vars "cutTwo" = σ₄.vars "cutTwo" := h₁
      _ = 2 := by simp [σ₄, σ₃, σ₂, σ₁]

  obtain ⟨τ2, r2, v2, f2, a2, i2, o2⟩ :=
    satMulTo_run (B := B) (σ := τ1) "cutC2" "c" "cutC3" n1 C2B c1 (by decide)
  have ne2 : τ2.vars "n" = n := by rw [f2 "n" (by decide) (by decide) (by decide) (by decide), ne1]
  have ce2 : τ2.vars "c" = c := by rw [f2 "c" (by decide) (by decide) (by decide) (by decide), ce1]
  have le2 : τ2.vars "L" = L := by rw [f2 "L" (by decide) (by decide) (by decide) (by decide), le1]
  have n2 : τ2.vars "n" < B := by rw [f2 "n" (by decide) (by decide) (by decide) (by decide)]; exact n1
  have c2b : τ2.vars "c" < B := by rw [f2 "c" (by decide) (by decide) (by decide) (by decide)]; exact c1
  have l2 : τ2.vars "L" < B := by rw [f2 "L" (by decide) (by decide) (by decide) (by decide)]; exact l1
  have C3B : τ2.vars "cutC3" < B := by rw [v2]; exact (satMul_result_le _ _ _).trans_lt n1

  obtain ⟨τ3, r3, v3, f3, a3, i3, o3⟩ :=
    satMulTo_run (B := B) (σ := τ2) "cutC3" "c" "cutC4" n2 C3B c2b (by decide)
  have ne3 : τ3.vars "n" = n := by rw [f3 "n" (by decide) (by decide) (by decide) (by decide), ne2]
  have ce3 : τ3.vars "c" = c := by rw [f3 "c" (by decide) (by decide) (by decide) (by decide), ce2]
  have le3 : τ3.vars "L" = L := by rw [f3 "L" (by decide) (by decide) (by decide) (by decide), le2]
  have n3 : τ3.vars "n" < B := by rw [f3 "n" (by decide) (by decide) (by decide) (by decide)]; exact n2
  have c3b : τ3.vars "c" < B := by rw [f3 "c" (by decide) (by decide) (by decide) (by decide)]; exact c2b
  have l3 : τ3.vars "L" < B := by rw [f3 "L" (by decide) (by decide) (by decide) (by decide)]; exact l2
  have C4B : τ3.vars "cutC4" < B := by rw [v3]; exact (satMul_result_le _ _ _).trans_lt n2

  obtain ⟨τ4, r4, v4, f4, a4, i4, o4⟩ :=
    satMulTo_run (B := B) (σ := τ3) "cutC4" "c" "cutC5" n3 C4B c3b (by decide)
  have ne4 : τ4.vars "n" = n := by rw [f4 "n" (by decide) (by decide) (by decide) (by decide), ne3]
  have ce4 : τ4.vars "c" = c := by rw [f4 "c" (by decide) (by decide) (by decide) (by decide), ce3]
  have le4 : τ4.vars "L" = L := by rw [f4 "L" (by decide) (by decide) (by decide) (by decide), le3]
  have n4 : τ4.vars "n" < B := by rw [f4 "n" (by decide) (by decide) (by decide) (by decide)]; exact n3
  have c4b : τ4.vars "c" < B := by rw [f4 "c" (by decide) (by decide) (by decide) (by decide)]; exact c3b
  have l4 : τ4.vars "L" < B := by rw [f4 "L" (by decide) (by decide) (by decide) (by decide)]; exact l3
  have C5B : τ4.vars "cutC5" < B := by rw [v4]; exact (satMul_result_le _ _ _).trans_lt n3
  have h64₄ : τ4.vars "cut64" = 64 := by
    calc τ4.vars "cut64" = τ3.vars "cut64" := f4 "cut64" (by decide) (by decide) (by decide) (by decide)
      _ = τ2.vars "cut64" := f3 "cut64" (by decide) (by decide) (by decide) (by decide)
      _ = τ1.vars "cut64" := f2 "cut64" (by decide) (by decide) (by decide) (by decide)
      _ = 64 := h64₁
  have hone₄ : τ4.vars "cutOne" = 1 := by
    calc τ4.vars "cutOne" = τ3.vars "cutOne" := f4 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = τ2.vars "cutOne" := f3 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = τ1.vars "cutOne" := f2 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = 1 := hone₁
  have h768₄ : τ4.vars "cut768" = 768 := by
    calc τ4.vars "cut768" = τ3.vars "cut768" := f4 "cut768" (by decide) (by decide) (by decide) (by decide)
      _ = τ2.vars "cut768" := f3 "cut768" (by decide) (by decide) (by decide) (by decide)
      _ = τ1.vars "cut768" := f2 "cut768" (by decide) (by decide) (by decide) (by decide)
      _ = 768 := h768₁
  have htwo₄ : τ4.vars "cutTwo" = 2 := by
    calc τ4.vars "cutTwo" = τ3.vars "cutTwo" := f4 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ2.vars "cutTwo" := f3 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ1.vars "cutTwo" := f2 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = 2 := htwo₁

  obtain ⟨τ5, r5, v5, f5, a5, i5, o5⟩ :=
    satMulTo_run (B := B) (σ := τ4) "cut64" "L" "cutS" n4
      (by rw [h64₄]; exact h64B)
      l4 (by decide)
  have ne5 : τ5.vars "n" = n := by rw [f5 "n" (by decide) (by decide) (by decide) (by decide), ne4]
  have le5 : τ5.vars "L" = L := by rw [f5 "L" (by decide) (by decide) (by decide) (by decide), le4]
  have n5 : τ5.vars "n" < B := by rw [f5 "n" (by decide) (by decide) (by decide) (by decide)]; exact n4
  have l5 : τ5.vars "L" < B := by rw [f5 "L" (by decide) (by decide) (by decide) (by decide)]; exact l4
  have S5B : τ5.vars "cutS" < B := by rw [v5]; exact (satMul_result_le _ _ _).trans_lt n4
  have one5 : τ5.vars "cutOne" < B := by
    rw [f5 "cutOne" (by decide) (by decide) (by decide) (by decide), hone₄]
    omega

  obtain ⟨τ6, r6, v6, f6, a6, i6, o6⟩ :=
    satAddTo_run (B := B) (σ := τ5) "cutS" "cutOne" "cutSPlusOne" n5 S5B one5 (by decide)
  have ne6 : τ6.vars "n" = n := by rw [f6 "n" (by decide) (by decide) (by decide) (by decide), ne5]
  have le6 : τ6.vars "L" = L := by rw [f6 "L" (by decide) (by decide) (by decide) (by decide), le5]
  have n6 : τ6.vars "n" < B := by rw [f6 "n" (by decide) (by decide) (by decide) (by decide)]; exact n5
  have l6 : τ6.vars "L" < B := by rw [f6 "L" (by decide) (by decide) (by decide) (by decide)]; exact l5
  have C56B : τ6.vars "cutC5" < B := by
    rw [f6 "cutC5" (by decide) (by decide) (by decide) (by decide), f5 "cutC5" (by decide) (by decide) (by decide) (by decide)]
    exact C5B
  have S16B : τ6.vars "cutSPlusOne" < B := by rw [v6]; exact (satAdd_result_le _ _ _).trans_lt n5
  have p768B : τ6.vars "cut768" < B := by
    rw [f6 "cut768" (by decide) (by decide) (by decide) (by decide), f5 "cut768" (by decide) (by decide) (by decide) (by decide), h768₄]
    omega

  obtain ⟨τ7, r7, v7, f7, a7, i7, o7⟩ :=
    satMulTo_run (B := B) (σ := τ6) "cut768" "cutC5" "cutP" n6 p768B C56B (by decide)
  have ne7 : τ7.vars "n" = n := by rw [f7 "n" (by decide) (by decide) (by decide) (by decide), ne6]
  have le7 : τ7.vars "L" = L := by rw [f7 "L" (by decide) (by decide) (by decide) (by decide), le6]
  have n7 : τ7.vars "n" < B := by rw [f7 "n" (by decide) (by decide) (by decide) (by decide)]; exact n6
  have l7 : τ7.vars "L" < B := by rw [f7 "L" (by decide) (by decide) (by decide) (by decide)]; exact l6
  have S17B : τ7.vars "cutSPlusOne" < B := by rw [f7 "cutSPlusOne" (by decide) (by decide) (by decide) (by decide)]; exact S16B
  have p7B : τ7.vars "cutP" < B := by rw [v7]; exact (satMul_result_le _ _ _).trans_lt n6

  obtain ⟨τ8, r8, v8, f8, a8, i8, o8⟩ :=
    satMulTo_run (B := B) (σ := τ7) "cutP" "cutSPlusOne" "cutQ" n7 p7B S17B (by decide)
  have ne8 : τ8.vars "n" = n := by rw [f8 "n" (by decide) (by decide) (by decide) (by decide), ne7]
  have le8 : τ8.vars "L" = L := by rw [f8 "L" (by decide) (by decide) (by decide) (by decide), le7]
  have n8 : τ8.vars "n" < B := by rw [f8 "n" (by decide) (by decide) (by decide) (by decide)]; exact n7
  have l8 : τ8.vars "L" < B := by rw [f8 "L" (by decide) (by decide) (by decide) (by decide)]; exact l7
  have q8B : τ8.vars "cutQ" < B := by rw [v8]; exact (satMul_result_le _ _ _).trans_lt n7
  have hone8 : τ8.vars "cutOne" = 1 := by
    calc τ8.vars "cutOne" = τ7.vars "cutOne" := f8 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = τ6.vars "cutOne" := f7 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = τ5.vars "cutOne" := f6 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = τ4.vars "cutOne" := f5 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = 1 := hone₄
  have one8 : τ8.vars "cutOne" < B := by rw [hone8]; omega

  obtain ⟨τ9, r9, v9, f9, a9, i9, o9⟩ :=
    satMulTo_run (B := B) (σ := τ8) "cutQ" "L" "cutR" n8 q8B l8 (by decide)
  have ne9 : τ9.vars "n" = n := by rw [f9 "n" (by decide) (by decide) (by decide) (by decide), ne8]
  have le9 : τ9.vars "L" = L := by rw [f9 "L" (by decide) (by decide) (by decide) (by decide), le8]
  have hone9 : τ9.vars "cutOne" = 1 := by
    calc τ9.vars "cutOne" = τ8.vars "cutOne" := f9 "cutOne" (by decide) (by decide) (by decide) (by decide)
      _ = 1 := hone8
  have one9 : τ9.vars "cutOne" < B := by rw [hone9]; omega
  have n9 : τ9.vars "n" < B := by rw [f9 "n" (by decide) (by decide) (by decide) (by decide)]; exact n8
  have r9B : τ9.vars "cutR" < B := by rw [v9]; exact (satMul_result_le _ _ _).trans_lt n8

  obtain ⟨τ10, r10, v10, f10, a10, i10, o10⟩ :=
    satAddTo_run (B := B) (σ := τ9) "cutR" "cutOne" "cutK" n9 r9B one9 (by decide)
  have ne10 : τ10.vars "n" = n := by rw [f10 "n" (by decide) (by decide) (by decide) (by decide), ne9]
  have n10 : τ10.vars "n" < B := by rw [f10 "n" (by decide) (by decide) (by decide) (by decide)]; exact n9
  have k10B : τ10.vars "cutK" < B := by rw [v10]; exact (satAdd_result_le _ _ _).trans_lt n9
  have htwo10 : τ10.vars "cutTwo" = 2 := by
    calc τ10.vars "cutTwo" = τ9.vars "cutTwo" := f10 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ8.vars "cutTwo" := f9 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ7.vars "cutTwo" := f8 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ6.vars "cutTwo" := f7 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ5.vars "cutTwo" := f6 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = τ4.vars "cutTwo" := f5 "cutTwo" (by decide) (by decide) (by decide) (by decide)
      _ = 2 := htwo₄
  have two10 : τ10.vars "cutTwo" < B := by rw [htwo10]; omega

  obtain ⟨τ11, r11, v11, f11, a11, i11, o11⟩ :=
    satMulTo_run (B := B) (σ := τ10) "cutTwo" "cutK" "cutoffResult" n10 two10 k10B (by decide)

  have hruns : Run B (seqs [
      .assign "cutOne" (.lit 1), .assign "cutTwo" (.lit 2),
      .assign "cut64" (.lit 64), .assign "cut768" (.lit 768),
      satMulTo "c" "c" "cutC2", satMulTo "cutC2" "c" "cutC3",
      satMulTo "cutC3" "c" "cutC4", satMulTo "cutC4" "c" "cutC5",
      satMulTo "cut64" "L" "cutS", satAddTo "cutS" "cutOne" "cutSPlusOne",
      satMulTo "cut768" "cutC5" "cutP", satMulTo "cutP" "cutSPlusOne" "cutQ",
      satMulTo "cutQ" "L" "cutR", satAddTo "cutR" "cutOne" "cutK",
      satMulTo "cutTwo" "cutK" "cutoffResult"])
      σ τ11 228 := by
    have htail := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq
      (r7.seq (r8.seq (r9.seq (r10.seq r11)))))))))
    have h := h1.seq (h2.seq (h3.seq (h4.seq htail)))
    simpa [seqs, Nat.add_assoc] using h
  have hc2val : τ1.vars "cutC2" = satMul n c c := by
    simpa [hn₄, hc₄] using v1
  have hc3val : τ2.vars "cutC3" = satMul n (satMul n c c) c := by
    rw [v2, ne1, ce1, hc2val]
  have hc4val : τ3.vars "cutC4" = satMul n (satMul n (satMul n c c) c) c := by
    rw [v3, ne2, ce2, hc3val]
  have hc5val : τ4.vars "cutC5" = satMul n (satMul n (satMul n (satMul n c c) c) c) c := by
    rw [v4, ne3, ce3, hc4val]
  have hc5end : τ11.vars "cutC5" = τ4.vars "cutC5" := by
    calc τ11.vars "cutC5" = τ10.vars "cutC5" := f11 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ9.vars "cutC5" := f10 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ8.vars "cutC5" := f9 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ7.vars "cutC5" := f8 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ6.vars "cutC5" := f7 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ5.vars "cutC5" := f6 "cutC5" (by decide) (by decide) (by decide) (by decide)
      _ = τ4.vars "cutC5" := f5 "cutC5" (by decide) (by decide) (by decide) (by decide)
  have hsatPow : τ11.vars "cutC5" = satPow5 n c := by
    rw [hc5end, hc5val]
    simp [satPow5]
  have hsval : τ5.vars "cutS" = satMul n 64 (Nat.clog 2 c) := by
    rw [v5, ne4, h64₄, le4, hLlog]
  have hs1val : τ6.vars "cutSPlusOne" = satAdd n (satMul n 64 (Nat.clog 2 c)) 1 := by
    rw [v6, ne5, hsval]
    have hone5 : τ5.vars "cutOne" = 1 := by rw [f5 "cutOne" (by decide) (by decide) (by decide) (by decide), hone₄]
    rw [hone5]
  have hpval : τ7.vars "cutP" = satMul n 768 (satPow5 n c) := by
    rw [v7, ne6]
    have h768₆ : τ6.vars "cut768" = 768 := by
      calc τ6.vars "cut768" = τ5.vars "cut768" := f6 "cut768" (by decide) (by decide) (by decide) (by decide)
        _ = τ4.vars "cut768" := f5 "cut768" (by decide) (by decide) (by decide) (by decide)
        _ = 768 := h768₄
    have hc5₆ : τ6.vars "cutC5" = satPow5 n c := by
      have hτ6τ4 : τ6.vars "cutC5" = τ4.vars "cutC5" := by
        calc τ6.vars "cutC5" = τ5.vars "cutC5" := f6 "cutC5" (by decide) (by decide) (by decide) (by decide)
          _ = τ4.vars "cutC5" := f5 "cutC5" (by decide) (by decide) (by decide) (by decide)
      rw [hτ6τ4, hc5val]
      simp [satPow5]
    rw [h768₆, hc5₆]
  have hqval : τ8.vars "cutQ" = satMul n (satMul n 768 (satPow5 n c))
      (satAdd n (satMul n 64 (Nat.clog 2 c)) 1) := by
    have hs1_7 : τ7.vars "cutSPlusOne" =
        satAdd n (satMul n 64 (Nat.clog 2 c)) 1 := by
      rw [f7 "cutSPlusOne" (by decide) (by decide) (by decide) (by decide), hs1val]
    rw [v8, ne7, hpval, hs1_7]
  have hrval : τ9.vars "cutR" = satMul n
      (satMul n (satMul n 768 (satPow5 n c))
        (satAdd n (satMul n 64 (Nat.clog 2 c)) 1)) (Nat.clog 2 c) := by
    rw [v9, ne8, le8, hqval, hLlog]
  have hkval : τ10.vars "cutK" = satAdd n
      (satMul n (satMul n (satMul n 768 (satPow5 n c))
        (satAdd n (satMul n 64 (Nat.clog 2 c)) 1)) (Nat.clog 2 c)) 1 := by
    rw [v10, ne9, hrval, hone9]
  have hresult : τ11.vars "cutoffResult" = saturatedWelzlCutoff n c := by
    rw [v11, ne10, htwo10, hkval]
    rfl
  refine ⟨τ11, ?_, hresult, ?_, ?_, ?_, ?_⟩
  · simpa [cutoffArithmetic, seqs, Nat.add_assoc] using hruns
  · intro z hz1 hz2 hz64 hz768 hzA hzB hzR hzC2 hzC3 hzC4 hzC5 hzS hzS1 hzP hzQ hzR2 hzK hzOut
    exact hruns.frame_var z (by
      simp [seqs, satMulTo, satAddTo, satMulCommand,
        satAddCommand, Com.wvars, hz1, hz2, hz64, hz768, hzA, hzB, hzR,
        hzC2, hzC3, hzC4, hzC5, hzS, hzS1, hzP, hzQ, hzR2, hzK, hzOut])
  · intro a
    exact hruns.frame_arr a (by
      simp [seqs, satMulTo, satAddTo, satMulCommand,
        satAddCommand, Com.warrs])
  · exact hruns.frame_inp (by
      simp [seqs, satMulTo, satAddTo, satMulCommand,
        satAddCommand, Com.reads])
  · exact hruns.out_eq (by
      simp [seqs, satMulTo, satAddTo, satMulCommand,
        satAddCommand, Com.NoWrite])

/-- The concrete source returns `min n (2 * K c)`. Its only additional
register-fit hypothesis concerns the logarithm in the `c < n` branch. -/
lemma refinedCutoffSource_run {B n c : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hc : σ.vars "c" = c)
    (hnB : n < B) (hcB : c < B) (hqB : σ.vars "qpow" < B)
    (hc2 : 2 ≤ c) (h768 : 768 < B)
    (hlogFit : c < n → 2 ^ Nat.clog 2 c < B) :
    ∃ σ', Run B refinedCutoffSource σ σ' (12 * Nat.clog 2 n + 252) ∧
      σ'.vars "cutoffResult" = min n (2 * refinedCutoffK c) ∧
      σ'.vars "n" = σ.vars "n" ∧ σ'.vars "c" = σ.vars "c" ∧
      σ'.vars "qpow" = σ.vars "qpow" ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₀ := σ.setVar "drawModulus" c
  have hmod : Run B (.assign "drawModulus" (.var "c")) σ σ₀ 2 := by
    have hcb : σ.vars "c" < B := by rw [hc]; exact hcB
    have he : (Expr.var "c").evalB B σ = some c := by
      have h := evalB_var (x := "c") hcb
      simpa only [hc] using h
    simpa [σ₀] using Run.assign he
  have hn₀ : σ₀.vars "n" = n := by simp [σ₀, hn]
  have hc₀ : σ₀.vars "c" = c := by simp [σ₀, hc]
  have hnB₀ : σ₀.vars "n" < B := by rw [hn₀]; exact hnB
  have hcB₀ : σ₀.vars "c" < B := by rw [hc₀]; exact hcB
  have hqB₀ : σ₀.vars "qpow" < B := by simp [σ₀]; exact hqB
  have hcondEval : (Cond.lt (.var "c") (.var "n")).evalB B σ₀ =
      some (decide (c < n)) := by
    simpa [hc₀, hn₀] using evalB_condLt (evalB_var hcB₀) (evalB_var hnB₀)
  by_cases hlate : c < n
  · obtain ⟨τ, hlog, hnτ, hqτ, hLτ, hmodτ, hcapτ, hoffτ, hvτ,
        harrτ, hinτ, houtτ⟩ :=
      drawLogSetup_run (B := B) (m := c) (σ := σ₀) hnB₀ hqB₀ (by simp [σ₀]) hcB
        (hlogFit hlate)
    have hLB : Nat.clog 2 c < B := by
      have hle : Nat.clog 2 c < 2 ^ Nat.clog 2 c := Nat.lt_two_pow_self
      exact hle.trans (hlogFit hlate)
    have hnτn : τ.vars "n" = n := by simpa [hn₀] using hnτ
    have hcτ : τ.vars "c" = c := by
      have hframe := hlog.frame_var "c" (by simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
      simpa [hc₀] using hframe
    obtain ⟨ρ, harith, hresρ, hframeρ, harrρ, hinρ, houtρ⟩ :=
      cutoffArithmetic_run (B := B) (n := n) (c := c) (L := Nat.clog 2 c)
        (σ := τ) hnτn hcτ
        hLτ rfl hnB hcB hLB h768
    have hbranch : Run B
        (.ite (.lt (.var "c") (.var "n"))
          (seqs [drawLogSetup, cutoffArithmetic])
          (.assign "cutoffResult" (.var "n"))) σ₀ ρ
        (12 * Nat.clog 2 c + 250) := by
      have htail := hlog.seq harith
      have hbody : Run B (seqs [drawLogSetup, cutoffArithmetic]) σ₀ ρ
          (12 * Nat.clog 2 c + 18 + 228) := by
        simpa [seqs, Nat.add_assoc, hc₀] using htail
      have htrue : (Cond.lt (.var "c") (.var "n")).evalB B σ₀ = some true := by
        rw [hcondEval]
        simp [hlate]
      have hraw := Run.ite_true (d := .assign "cutoffResult" (.var "n")) htrue hbody
      have hrun : Run B
          (.ite (.lt (.var "c") (.var "n"))
            (seqs [drawLogSetup, cutoffArithmetic])
            (.assign "cutoffResult" (.var "n"))) σ₀ ρ
          (12 * Nat.clog 2 c + 250) := by
        have hle : 1 + (Cond.lt (.var "c") (.var "n")).size +
            (12 * Nat.clog 2 c + 18 + 228) ≤ 12 * Nat.clog 2 c + 250 := by
          norm_num [Cond.size, Expr.size]
          omega
        exact hraw.mono hle
      exact hrun.mono (by omega)
    have hwhole : Run B refinedCutoffSource σ ρ (12 * Nat.clog 2 c + 252) := by
      have h := hmod.seq hbranch
      have hcost : 2 + (12 * Nat.clog 2 c + 250) = 12 * Nat.clog 2 c + 252 := by omega
      rw [hcost] at h
      change Run B refinedCutoffSource σ ρ (12 * Nat.clog 2 c + 252)
      exact h
    have hresult : ρ.vars "cutoffResult" = min n (2 * refinedCutoffK c) := by
      rw [hresρ, saturatedWelzlCutoff_eq]
    have hcostle : 12 * Nat.clog 2 c + 252 ≤ 12 * Nat.clog 2 n + 252 := by
      have hclog := earlyWelzlCutoff_log_le n c (Nat.not_le_of_gt hlate)
      omega
    have hnρ : ρ.vars "n" = σ.vars "n" := by
      rw [hframeρ "n" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      rw [hnτn, hn]
    have hcρ : ρ.vars "c" = σ.vars "c" := by
      rw [hframeρ "c" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      rw [hcτ, hc]
    have hqρ : ρ.vars "qpow" = σ.vars "qpow" := by
      rw [hframeρ "qpow" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hqτ]
      simp [σ₀]
    have harrρσ : ∀ a, ρ.arrs a = σ.arrs a := by
      intro a
      rw [harrρ a, harrτ a]
      exact hmod.frame_arr a (by simp [Com.warrs])
    have hinρσ : ρ.inp = σ.inp := by
      rw [hinρ, hinτ]
      exact hmod.frame_inp (by simp [Com.reads])
    have houtρσ : ρ.out = σ.out := by
      rw [houtρ, houtτ]
      exact hmod.out_eq (by simp [Com.NoWrite])
    refine ⟨ρ, hwhole.mono hcostle, hresult, hnρ, hcρ, hqρ, harrρσ, hinρσ, houtρσ⟩
  · let ρ := σ₀.setVar "cutoffResult" n
    have hnEval : (Expr.var "n").evalB B σ₀ = some n := by
      simpa [hn₀] using (evalB_var (x := "n") hnB₀)
    have hassign : Run B (.assign "cutoffResult" (.var "n")) σ₀ ρ 2 := by
      simpa [ρ] using Run.assign hnEval
    have hfalse : (Cond.lt (.var "c") (.var "n")).evalB B σ₀ = some false := by
      rw [hcondEval]
      simp [hlate]
    have hbranch : Run B
        (.ite (.lt (.var "c") (.var "n"))
          (seqs [drawLogSetup, cutoffArithmetic])
          (.assign "cutoffResult" (.var "n"))) σ₀ ρ 6 := by
      exact Run.ite_false (d := .assign "cutoffResult" (.var "n")) hfalse hassign
    have hwhole : Run B refinedCutoffSource σ ρ 8 := by
      have h := hmod.seq hbranch
      simpa [refinedCutoffSource] using h
    have hresult : ρ.vars "cutoffResult" = min n (2 * refinedCutoffK c) := by
      rw [← earlyWelzlCutoff_eq n c hc2]
      simp [ρ, earlyWelzlCutoff, Nat.not_lt_of_ge (Nat.le_of_not_gt hlate)]
    refine ⟨ρ, hwhole.mono (by
      have hclog : Nat.clog 2 n ≤ 12 * Nat.clog 2 n := by omega
      omega), hresult, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ρ, σ₀, hn]
    · simp [ρ, σ₀, hc]
    · simp [ρ, σ₀]
    · intro a
      have hb := hbranch.frame_arr a (by
        simp [Com.warrs, seqs, drawLogSetup, cutoffArithmetic, satMulTo,
          satAddTo, satMulCommand, satAddCommand, computeLog, inc])
      rw [hb]
      exact hmod.frame_arr a (by simp [Com.warrs])
    · have hb := hbranch.frame_inp (by
        simp [Com.reads, seqs, drawLogSetup, cutoffArithmetic, satMulTo,
          satAddTo, satMulCommand, satAddCommand, computeLog, inc])
      rw [hb]
      exact hmod.frame_inp (by simp [Com.reads])
    · have hb := hbranch.out_eq (by
        simp [Com.NoWrite, seqs, drawLogSetup, cutoffArithmetic, satMulTo,
          satAddTo, satMulCommand, satAddCommand, computeLog, inc])
      rw [hb]
      exact hmod.out_eq (by simp [Com.NoWrite])

end Lax457868Proofs.RefinedCutoffSource
