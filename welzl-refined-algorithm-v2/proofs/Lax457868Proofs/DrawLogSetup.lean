import Mathlib.Tactic
import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax457868Proofs.ReusedOriginal.Construction.WelzlLog

/-!
The fixed draw setup computes the ceiling binary logarithm of the draw
modulus while preserving the caller's input size and power word.
-/

namespace Lax457868Proofs.DrawLogSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlLog

/-- Save the caller's size and power, run the existing logarithm computation
at `drawModulus`, then restore those caller-owned words. -/
def drawLogSetup : Com :=
  seqs [
    .assign "drawSavedN" (.var "n"),
    .assign "drawSavedQ" (.var "qpow"),
    .assign "n" (.var "drawModulus"),
    computeLog,
    .assign "n" (.var "drawSavedN"),
    .assign "qpow" (.var "drawSavedQ")]

/-- The wrapper runs the source logarithm loop at the draw modulus. It writes
`L = ⌈log₂ drawModulus⌉` and preserves `n`, `qpow`, arrays, tape, output, and
the other draw parameters. Its cost is the source loop's cost plus five
word assignments. -/
lemma drawLogSetup_run {B m : ℕ} {σ : Env}
    (hn : σ.vars "n" < B)
    (hq : σ.vars "qpow" < B)
    (hmod : σ.vars "drawModulus" = m)
    (hmB : m < B)
    (hpowB : 2 ^ Nat.clog 2 m < B) :
    ∃ σ', Run B drawLogSetup σ σ' (12 * Nat.clog 2 m + 18) ∧
      σ'.vars "n" = σ.vars "n" ∧
      σ'.vars "qpow" = σ.vars "qpow" ∧
      σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧
      σ'.vars "drawCap" = σ.vars "drawCap" ∧
      σ'.vars "drawOffset" = σ.vars "drawOffset" ∧
      σ'.vars "v" = σ.vars "v" ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let n₀ := σ.vars "n"
  let q₀ := σ.vars "qpow"
  let σ₁ := σ.setVar "drawSavedN" n₀
  let σ₂ := σ₁.setVar "drawSavedQ" q₀
  let σ₃ := σ₂.setVar "n" m
  have hlogB : Nat.clog 2 m + 1 < B := by
    have hle : Nat.clog 2 m + 1 ≤ 2 ^ Nat.clog 2 m :=
      Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := Nat.clog 2 m))
    omega
  obtain ⟨τ, hlogRun, hnτ, hLτ, hqτ⟩ :=
    computeLog_run (B := B) (n := m) (σ := σ₃) (by simp [σ₃, σ₂, σ₁, n₀])
      hpowB hlogB
  let τ₁ := τ.setVar "n" n₀
  let τ₂ := τ₁.setVar "qpow" q₀
  have hsaveN₃ : σ₃.vars "drawSavedN" = n₀ := by simp [σ₃, σ₂, σ₁]
  have hsaveQ₃ : σ₃.vars "drawSavedQ" = q₀ := by simp [σ₃, σ₂, σ₁]
  have hsaveNτ : τ.vars "drawSavedN" = n₀ := by
    have hframe := hlogRun.frame_var "drawSavedN" (by
      simp [computeLog, seqs, inc, Com.wvars])
    simpa [hsaveN₃] using hframe.trans hsaveN₃
  have hsaveQτ : τ.vars "drawSavedQ" = q₀ := by
    have hframe := hlogRun.frame_var "drawSavedQ" (by
      simp [computeLog, seqs, inc, Com.wvars])
    simpa [hsaveQ₃] using hframe.trans hsaveQ₃
  have hrestoreN : Run B (.assign "n" (.var "drawSavedN")) τ τ₁ 2 := by
    have heval : (Expr.var "drawSavedN").evalB B τ = some n₀ := by
      have hb : τ.vars "drawSavedN" < B := by simpa [hsaveNτ] using hn
      simpa [hsaveNτ] using (evalB_var (x := "drawSavedN") hb)
    simpa [τ₁] using (Run.assign heval)
  have hrestoreQ : Run B (.assign "qpow" (.var "drawSavedQ")) τ₁ τ₂ 2 := by
    have hsaveQτ₁ : τ₁.vars "drawSavedQ" = q₀ := by simp [τ₁, hsaveQτ]
    have heval : (Expr.var "drawSavedQ").evalB B τ₁ = some q₀ := by
      have hb : τ₁.vars "drawSavedQ" < B := by simpa [hsaveQτ₁] using hq
      simpa [hsaveQτ₁] using (evalB_var (x := "drawSavedQ") hb)
    simpa [τ₂] using (Run.assign heval)
  have hsaveQ₁ : Run B (.assign "drawSavedQ" (.var "qpow")) σ₁ σ₂ 2 := by
    have heval : (Expr.var "qpow").evalB B σ₁ = some q₀ := by
      have hb : σ₁.vars "qpow" < B := by simpa [σ₁, q₀] using hq
      simpa [σ₁, q₀] using (evalB_var (x := "qpow") hb)
    simpa [σ₂] using (Run.assign heval)
  have hsaveN : Run B (.assign "drawSavedN" (.var "n")) σ σ₁ 2 := by
    have heval : (Expr.var "n").evalB B σ = some n₀ := by
      have hb : σ.vars "n" < B := by simpa [n₀] using hn
      simpa [n₀] using (evalB_var (x := "n") hb)
    simpa [σ₁] using (Run.assign heval)
  have hsetN : Run B (.assign "n" (.var "drawModulus")) σ₂ σ₃ 2 := by
    have hmod₂ : σ₂.vars "drawModulus" = m := by simp [σ₂, σ₁, hmod]
    have heval : (Expr.var "drawModulus").evalB B σ₂ = some m := by
      have hb : σ₂.vars "drawModulus" < B := by simpa [hmod₂] using hmB
      simpa [hmod₂] using (evalB_var (x := "drawModulus") hb)
    simpa [σ₃] using (Run.assign heval)
  have hwhole : Run B drawLogSetup σ τ₂ (12 * Nat.clog 2 m + 18) := by
    have hlast := hrestoreN.seq hrestoreQ
    have hcompute := hlogRun.seq hlast
    have hset := hsetN.seq hcompute
    have hsave := hsaveQ₁.seq hset
    have hr := hsaveN.seq hsave
    have hraw : Run B drawLogSetup σ τ₂
        (2 + (2 + (2 + (12 * Nat.clog 2 m + 8 + (2 + 2))))) := by
      simpa [drawLogSetup, seqs] using hr
    have hcost : Run B drawLogSetup σ τ₂ (12 * Nat.clog 2 m + 18) :=
      hraw.mono (by omega)
    exact hcost
  refine ⟨τ₂, hwhole, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [τ₂, τ₁, n₀]
  · simp [τ₂, τ₁, q₀]
  · have hLrestoreN := hrestoreN.frame_var "L" (by simp [Com.wvars])
    have hLrestoreQ := hrestoreQ.frame_var "L" (by simp [Com.wvars])
    exact hLrestoreQ.trans (hLrestoreN.trans hLτ)
  · have hmodframe := hwhole.frame_var "drawModulus" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact hmodframe.trans hmod
  · have hcapFrame := hwhole.frame_var "drawCap" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact hcapFrame
  · have hoffFrame := hwhole.frame_var "drawOffset" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact hoffFrame
  · have hvFrame := hwhole.frame_var "v" (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.wvars])
    exact hvFrame
  · intro a
    exact hwhole.frame_arr a (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.warrs])
  · exact hwhole.frame_inp (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.reads])
  · exact hwhole.out_eq (by
      simp [drawLogSetup, seqs, computeLog, inc, Com.NoWrite])

end Lax457868Proofs.DrawLogSetup
