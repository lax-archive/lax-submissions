import Lax457868Proofs.ReusedOriginal.Construction.DriverSetup
import Lax457868Proofs.ReusedOriginal.Construction.SourceBounds
import Lax457868Proofs.RefinedCutoffSource
import Lax457868Proofs.SamplerRuntimeSetup

/-! The original CSR setup is reused unchanged. The refined source then
computes its cutoff and saves the parameter logarithm before sampler calls
reuse the logarithm register. All scratch arrays begin as zero arrays. -/

namespace Lax457868Proofs.RefinedSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.DriverSetup
open Lax457868Proofs.ReusedOriginal.Construction.SourceBounds
open Lax457868Proofs.RefinedCutoffSource
open Lax457868Proofs.SamplerRuntimeSetup

/-- Fixed input setup; `L` is saved before later draw calls overwrite it. -/
def refinedSetupSource : Com := seqs [setup, refinedCutoffSource,
  .assign "refinedLogC" (.var "L"), .assign "activeBCount" (.var "n")]

/-- Concrete initial driver facts, with the scratch arrays still zero. -/
structure Ready (c n : ℕ) (x bits : List ℕ) (σ : Env) : Prop where
  parameter : σ.vars "c" = c
  vertices : σ.vars "n" = n
  radixSize : σ.vars "qpow" = 2 ^ Nat.clog 2 n
  cutoff : σ.vars "cutoffResult" = min n (2 * refinedCutoffK c)
  logParameter : 2 * refinedCutoffK c < n → σ.vars "refinedLogC" = Nat.clog 2 c
  activeCount : σ.vars "acount" = n
  activeBCount : σ.vars "activeBCount" = n
  success : σ.vars "good" = 1
  round : σ.vars "round" = 0
  removedCount : σ.vars "removedCount" = 0
  offsets : σ.arrs "off" = arrOf (n + 1) (offset x)
  targets : σ.arrs "tgt" = arrOf (2 * edgeCount x) (target x)
  activeA : σ.arrs "activeA" = arrOf n (fun _ => 1)
  activeB : σ.arrs "activeB" = arrOf n (fun _ => 1)
  lengths : ∀ a, (σ.arrs a).length = welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a
  scratch : ∀ a, a ≠ "off" → a ≠ "tgt" → a ≠ "activeA" → a ≠ "activeB" →
    σ.arrs a = List.replicate (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a) 0
  input : σ.inp = bits
  output : σ.out = []
  edges : σ.vars "m" = edgeCount x

/-- Real setup execution from the encoded input. Word bounds concern input
words and linear workspace extents, and never require a running-time value
to fit in one word. The cost adds the reused setup and cutoff costs. -/
lemma refinedSetupSource_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} (hx : EncodesGraph x n G) (hc2 : 2 ≤ c)
    (hB : 4 * (x.length + 1) ≤ B) (h768 : 768 < B)
    (hinput : ∀ v ∈ (c :: x) ++ bits, v < B) :
    ∃ σ, Run B refinedSetupSource
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      σ (40 * (x.length + Nat.clog 2 n + 1) + 12 * Nat.clog 2 n + 256) ∧
      Ready c n x bits σ ∧ ValuesBounded B σ := by
  obtain ⟨σ₀, hsetup, hr⟩ := setup_run hx hB
  have hbound₀ := run_preserves hsetup
    (init_valuesBounded _ (by omega) hinput)
  have hnB : n < B := by rw [← hr.vertices]; exact hbound₀.vars _
  have hcB : c < B := hinput c (by simp)
  have hpow : c < n → 2 ^ Nat.clog 2 c < B := by
    intro hcn
    have hpowle : 2 ^ Nat.clog 2 c ≤ 2 ^ Nat.clog 2 n :=
      Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 (Nat.le_of_lt hcn))
    have hqb : 2 ^ Nat.clog 2 n < B := by rw [← hr.radixSize]; exact hbound₀.vars _
    exact hpowle.trans_lt hqb
  obtain ⟨σ₁, hcutrun, hcut, hn₁, hc₁, hq₁, harr₁, hin₁, hout₁, hlog₁⟩ :=
    refinedCutoffSource_run hr.vertices hr.parameter hnB hcB (hbound₀.vars "qpow")
      hc2 h768 hpow
  have hbound₁ := run_preserves hcutrun hbound₀
  let σ₂ := σ₁.setVar "refinedLogC" (σ₁.vars "L")
  have hsave : Run B (.assign "refinedLogC" (.var "L")) σ₁ σ₂ 2 := by
    exact Run.assign (evalB_var (hbound₁.vars "L"))
  let σ₃ := σ₂.setVar "activeBCount" n
  have hbcount : Run B (.assign "activeBCount" (.var "n")) σ₂ σ₃ 2 := by
    apply Run.assign
    have hn₂ : σ₂.vars "n" = n := by simp [σ₂, hn₁, hr.vertices]
    rw [evalB_var (by rw [hn₂]; exact hnB), hn₂]
  have hrun : Run B refinedSetupSource
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      σ₃ (40 * (x.length + Nat.clog 2 n + 1) + 12 * Nat.clog 2 n + 256) := by
    simpa [refinedSetupSource, seqs, Nat.add_assoc] using
      hsetup.seq (hcutrun.seq (hsave.seq hbcount))
  have htail : Run B (seqs [refinedCutoffSource,
      .assign "refinedLogC" (.var "L"), .assign "activeBCount" (.var "n")])
      σ₀ σ₃ (12 * Nat.clog 2 n + 256) := by
    simpa [seqs, Nat.add_assoc] using hcutrun.seq (hsave.seq hbcount)
  have harr : σ₃.arrs = σ₀.arrs := by funext a; exact harr₁ a
  refine ⟨σ₃, hrun, ?_, run_preserves hbcount (run_preserves hsave hbound₁)⟩
  constructor
  · simpa [σ₃, σ₂, hc₁] using hr.parameter
  · simpa [σ₃, σ₂, hn₁] using hr.vertices
  · simpa [σ₃, σ₂, hq₁] using hr.radixSize
  · simpa [σ₃, σ₂] using hcut
  · intro hlarge
    have hcn : c < n := by
      have hh := (parameter_bounds hc2 hlarge).1
      nlinarith
    simpa [σ₃, σ₂] using hlog₁ hcn
  · exact (htail.frame_var "acount" (by decide)).trans hr.activeCount
  · simp [σ₃]
  · exact (htail.frame_var "good" (by decide)).trans hr.success
  · exact (htail.frame_var "round" (by decide)).trans hr.round
  · exact (htail.frame_var "removedCount" (by decide)).trans hr.removedCount
  · rw [harr]; exact hr.offsets
  · rw [harr]; exact hr.targets
  · rw [harr]; exact hr.activeA
  · rw [harr]; exact hr.activeB
  · intro a; rw [harr]; exact hr.lengths a
  · intro a ha₁ ha₂ ha₃ ha₄
    rw [harr, hsetup.frame_arr a (by
      simp [setup, readGraph, readArray, initializeWelzl, computeLog, initActive,
        seqs, inc, Com.warrs, ha₁, ha₂, ha₃, ha₄])]
    rfl
  · exact hin₁.trans hr.input
  · exact hout₁.trans hr.output
  · exact (htail.frame_var "m" (by decide)).trans hr.edges

end Lax457868Proofs.RefinedSetup
