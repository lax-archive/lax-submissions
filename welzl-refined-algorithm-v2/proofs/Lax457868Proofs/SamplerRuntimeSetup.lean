import Lax457868Proofs.SaturatedCutoff
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
import Lax808846Proofs.Reasoning

/-! Runtime sampler parameters for the nontrivial branch. Arithmetic fits
because that branch has already established `2 * refinedCutoffK c < n`.
The retry caps are the input size; they are not input-dependent syntax. -/

namespace Lax457868Proofs.SamplerRuntimeSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- All parameter intermediates are below the existing refined cutoff. -/
lemma parameter_bounds {c n : ℕ} (hc : 2 ≤ c)
    (hlarge : 2 * refinedCutoffK c < n) :
    c ^ 2 < n ∧ 4 * c ^ 2 < n ∧ 64 * Nat.clog 2 c < n ∧
      64 * Nat.clog 2 c + 1 < n ∧
      4 * c ^ 2 * (64 * Nat.clog 2 c + 1) < n ∧ 64 < n := by
  have hL : 1 ≤ Nat.clog 2 c := Nat.clog_pos (by decide) (by omega)
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hpow : c ^ 2 ≤ c ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hfactor : 1 ≤ 64 * Nat.clog 2 c + 1 := by omega
  have hden : 4 * c ^ 2 * (64 * Nat.clog 2 c + 1) ≤ refinedCutoffK c := by
    have hp := Nat.mul_le_mul_right (64 * Nat.clog 2 c + 1)
      (Nat.mul_le_mul_left 4 hpow)
    have hl := Nat.mul_le_mul_left
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1)) hL
    dsimp [refinedCutoffK]
    nlinarith
  have hs : 64 * Nat.clog 2 c + 1 ≤
      4 * c ^ 2 * (64 * Nat.clog 2 c + 1) := by nlinarith
  have hd : 4 * c ^ 2 ≤ 4 * c ^ 2 * (64 * Nat.clog 2 c + 1) := by
    nlinarith
  omega

/-- Fixed straight-line parameter setup following active-domain packing. -/
def samplerParameterSource : Com := seqs [
  .assign "samplerDenom" (.mul (.lit 4) (.mul (.var "c") (.var "c"))),
  .assign "repairSampleSize" (.mul (.lit 64) (.var "refinedLogC")),
  .assign "samplerCapDenom" (.mul (.var "samplerDenom")
    (.add (.var "repairSampleSize") (.lit 1))),
  .assign "batchTarget" (.div (.var "drawModulus") (.var "samplerDenom")),
  .assign "exceptionCap" (.div (.var "drawModulus") (.var "samplerCapDenom")),
  .assign "nearBound" (.div (.var "cutoffResult") (.lit 6)),
  .assign "repairFarBound" (.div (.var "cutoffResult") (.lit 3)),
  .assign "initialRetryCap" (.var "n"),
  .assign "repairRetryCap" (.var "n"),
  .assign "drawCap" (.var "n")]

/-- Compute every sampler register from runtime values. The cost 38 is the
sum of the ten assignment/expression costs in the displayed source. -/
lemma samplerParameterSource_run {B n c m : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hc : σ.vars "c" = c)
    (hL : σ.vars "refinedLogC" = Nat.clog 2 c)
    (hm : σ.vars "drawModulus" = m)
    (hcut : σ.vars "cutoffResult" = 2 * refinedCutoffK c)
    (hc2 : 2 ≤ c) (hmn : m ≤ n)
    (hlarge : 2 * refinedCutoffK c < n) (hnB : n < B) :
    ∃ τ, Run B samplerParameterSource σ τ 38 ∧
      τ.vars "batchTarget" = m / (4 * c ^ 2) ∧
      τ.vars "repairSampleSize" = 64 * Nat.clog 2 c ∧
      τ.vars "exceptionCap" = m / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)) ∧
      τ.vars "nearBound" = refinedCutoffK c / 3 ∧
      τ.vars "repairFarBound" = (2 * refinedCutoffK c) / 3 ∧
      τ.vars "initialRetryCap" = n ∧ τ.vars "repairRetryCap" = n ∧
      τ.vars "drawCap" = n ∧
      (∀ v, v ∉ samplerParameterSource.wvars → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  obtain ⟨hcSq, hden, hs, hs1, hcapden, h64⟩ := parameter_bounds hc2 hlarge
  have hcSqB : c * c < B := by nlinarith
  have hcB : c < B := by nlinarith
  have hdenB : 4 * (c * c) < B := by nlinarith
  have hsB : 64 * Nat.clog 2 c < B := hs.trans hnB
  have hs1B : 64 * Nat.clog 2 c + 1 < B := hs1.trans hnB
  have hcapdenB : 4 * (c * c) * (64 * Nat.clog 2 c + 1) < B := by
    simpa only [pow_two] using hcapden.trans hnB
  have hLB : Nat.clog 2 c < B := by omega
  have h64B : 64 < B := h64.trans hnB
  have h4B : 4 < B := by omega
  have h1B : 1 < B := by omega
  have h6B : 6 < B := by omega
  have h3B : 3 < B := by omega
  have hmB : m < B := hmn.trans_lt hnB
  have hcutB : 2 * refinedCutoffK c < B := hlarge.trans hnB
  have hrB : m / (4 * (c * c)) < B := (Nat.div_le_self _ _).trans_lt hmB
  have hcapB : m / (4 * (c * c) * (64 * Nat.clog 2 c + 1)) < B :=
    (Nat.div_le_self _ _).trans_lt hmB
  have hnearB : (2 * refinedCutoffK c) / 6 < B :=
    (Nat.div_le_self _ _).trans_lt hcutB
  have hfarB : (2 * refinedCutoffK c) / 3 < B :=
    (Nat.div_le_self _ _).trans_lt hcutB
  let σ1 := σ.setVar "samplerDenom" (4 * c ^ 2)
  have r1 : Run B (.assign "samplerDenom" (.mul (.lit 4) (.mul (.var "c") (.var "c")))) σ σ1 6 := by
    apply Run.assign
    simp only [Expr.evalB, fit, h4B, ↓reduceIte, hc, hcB, Bop.apply, Option.bind_some, hcSqB, hdenB, pow_two]
  let σ2 := σ1.setVar "repairSampleSize" (64 * Nat.clog 2 c)
  have r2 : Run B (.assign "repairSampleSize" (.mul (.lit 64) (.var "refinedLogC"))) σ1 σ2 4 := by
    apply Run.assign
    simp only [Expr.evalB, fit, h64B, ↓reduceIte, Env.setVar, pow_two, String.reduceEq, hL, hLB, Bop.apply,
    Option.bind_some, hsB, σ1]
  let σ3 := σ2.setVar "samplerCapDenom" (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))
  have r3 : Run B (.assign "samplerCapDenom" (.mul (.var "samplerDenom") (.add (.var "repairSampleSize") (.lit 1)))) σ2 σ3 6 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hdenB, hsB, h1B, Bop.apply,
    Option.bind_some, hs1B, hcapdenB, σ2, σ1]
  let σ4 := σ3.setVar "batchTarget" (m / (4 * c ^ 2))
  have r4 : Run B (.assign "batchTarget" (.div (.var "drawModulus") (.var "samplerDenom"))) σ3 σ4 4 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hm, hmB, hdenB, Bop.apply,
    Option.bind_some, hrB, σ3, σ2, σ1]
  let σ5 := σ4.setVar "exceptionCap" (m / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)))
  have r5 : Run B (.assign "exceptionCap" (.div (.var "drawModulus") (.var "samplerCapDenom"))) σ4 σ5 4 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hm, hmB, hcapdenB, Bop.apply,
    Option.bind_some, hcapB, σ4, σ3, σ2, σ1]
  let σ6 := σ5.setVar "nearBound" ((2 * refinedCutoffK c) / 6)
  have r6 : Run B (.assign "nearBound" (.div (.var "cutoffResult") (.lit 6))) σ5 σ6 4 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hcut, hcutB, h6B, Bop.apply,
    Option.bind_some, hnearB, σ5, σ4, σ3, σ2, σ1]
  let σ7 := σ6.setVar "repairFarBound" ((2 * refinedCutoffK c) / 3)
  have r7 : Run B (.assign "repairFarBound" (.div (.var "cutoffResult") (.lit 3))) σ6 σ7 4 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hcut, hcutB, h3B, Bop.apply,
    Option.bind_some, hfarB, σ6, σ5, σ4, σ3, σ2, σ1]
  let σ8 := σ7.setVar "initialRetryCap" (n)
  have r8 : Run B (.assign "initialRetryCap" (.var "n")) σ7 σ8 2 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hn, hnB, σ7, σ6, σ5, σ4, σ3, σ2,
    σ1]
  let σ9 := σ8.setVar "repairRetryCap" (n)
  have r9 : Run B (.assign "repairRetryCap" (.var "n")) σ8 σ9 2 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hn, hnB, σ8, σ7, σ6, σ5, σ4, σ3,
    σ2, σ1]
  let σ10 := σ9.setVar "drawCap" (n)
  have r10 : Run B (.assign "drawCap" (.var "n")) σ9 σ10 2 := by
    apply Run.assign
    simp only [Expr.evalB, fit, Env.setVar, pow_two, String.reduceEq, ↓reduceIte, hn, hnB, σ9, σ8, σ7, σ6, σ5, σ4,
    σ3, σ2, σ1]
  have hr : Run B samplerParameterSource σ σ10 38 := by
    simpa [samplerParameterSource, seqs] using r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10)))))))))
  have hnear : (2 * refinedCutoffK c) / 6 = refinedCutoffK c / 3 := by omega
  refine ⟨σ10, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals first | (intro v hv; exact hr.frame_var v hv) | simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Env.setVar, hnear]

end Lax457868Proofs.SamplerRuntimeSetup
