import Lax457868Proofs.ClockedSource
import Lax457868Proofs.RefinedSetup

/-! Initialize the two-word source clock from the actual graph sizes. Its
capacity has the near-linear target shape; the product with log n is never
computed in a machine word. -/
namespace Lax457868Proofs.RefinedClockSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ClockedSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlLog

/-- The coefficient is fixed with the program, while both counters are
computed from the input. `n + 2m + 4` is the CSR input length plus one. -/
def clockSetup (D : ℕ) : Com := seqs [computeLog,
  .assign blockSizeName (.mul (.lit D)
    (.add (.add (.var "n") (.mul (.lit 2) (.var "m"))) (.lit 4))),
  .assign blocksName (.add (.var "L") (.lit 1)),
  .assign slotsName (.lit 0), .assign timedOutName (.lit 0),
  .assign continueName (.lit 0)]

lemma clockSetup_run {B D n m : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hq : σ.vars "qpow" = 2 ^ Nat.clog 2 n)
    (hn2 : 2 ≤ n) (hD : 1 ≤ D)
    (hsize : D * (n + 2 * m + 4) < B)
    (hpow : 2 ^ Nat.clog 2 n < B)
    (hlog : Nat.clog 2 n + 1 < B) :
    ∃ τ, Run B (clockSetup D) σ τ (12 * Nat.clog 2 n + 28) ∧
      Ready B (D * (n + 2 * m + 4)) τ ∧
      capacity (D * (n + 2 * m + 4)) τ =
        D * (n + 2 * m + 4) * (Nat.clog 2 n + 1) ∧
      (∀ v, v ≠ "L" → ¬ protectedName v → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hbase : n + 2 * m + 4 ≤ D * (n + 2 * m + 4) := by nlinarith
  have hDB : D < B := by nlinarith
  have hnB : n < B := by omega
  have hmB : m < B := by omega
  have hm2B : 2 * m < B := by omega
  have hsumB : n + 2 * m < B := by omega
  have hbaseB : n + 2 * m + 4 < B := hbase.trans_lt hsize
  have h4B : 4 < B := by omega
  have h2B : 2 < B := by omega
  have h1B : 1 < B := by omega
  have h0B : 0 < B := by omega
  have hLB : Nat.clog 2 n < B := by omega
  obtain ⟨σ₀, r₀, hn₀, hL₀, hq₀⟩ := computeLog_run hn hpow hlog
  have hm₀ : σ₀.vars "m" = m := (r₀.frame_var _ (by decide)).trans hm
  let σ₁ := σ₀.setVar blockSizeName (D * (n + 2 * m + 4))
  have r₁ : Run B (.assign blockSizeName (.mul (.lit D)
      (.add (.add (.var "n") (.mul (.lit 2) (.var "m"))) (.lit 4)))) σ₀ σ₁ 10 := by
    apply Run.assign
    simp only [Expr.evalB, fit, hDB, h2B, h4B, hn₀, hm₀, hnB, hmB,
      hm2B, hsumB, hbaseB, hsize, Bop.apply, Option.bind_some, ↓reduceIte]
  let σ₂ := σ₁.setVar blocksName (Nat.clog 2 n + 1)
  have r₂ : Run B (.assign blocksName (.add (.var "L") (.lit 1))) σ₁ σ₂ 4 := by
    apply Run.assign
    simp [σ₁, Env.setVar, blockSizeName, Expr.evalB, fit, hL₀, hLB, h1B, hlog, Bop.apply]
  let σ₃ := σ₂.setVar slotsName 0
  have r₃ : Run B (.assign slotsName (.lit 0)) σ₂ σ₃ 2 :=
    Run.assign (evalB_lit h0B)
  let σ₄ := σ₃.setVar timedOutName 0
  have r₄ : Run B (.assign timedOutName (.lit 0)) σ₃ σ₄ 2 :=
    Run.assign (evalB_lit h0B)
  let τ := σ₄.setVar continueName 0
  have r₅ : Run B (.assign continueName (.lit 0)) σ₄ τ 2 :=
    Run.assign (evalB_lit h0B)
  have hr : Run B (clockSetup D) σ τ (12 * Nat.clog 2 n + 28) := by
    simpa [clockSetup, seqs, Nat.add_assoc] using
      r₀.seq (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅))))
  have hp : 0 < D * (n + 2 * m + 4) := by positivity
  refine ⟨τ, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hp, hsize, ?_, ?_, ?_, ?_⟩ <;>
      simp [τ, σ₄, σ₃, σ₂, σ₁, Env.setVar, blockSizeName, blocksName,
        slotsName, timedOutName, continueName, hlog, hp]
  · simp [capacity, τ, σ₄, σ₃, σ₂, σ₁, Env.setVar, blockSizeName,
      blocksName, slotsName, timedOutName, continueName]
  · intro v hv hprotected
    have hc : v ≠ blockSizeName ∧ v ≠ blocksName ∧ v ≠ slotsName ∧
        v ≠ timedOutName ∧ v ≠ continueName := by
      simpa [protectedName, not_or] using hprotected
    simp only [τ, σ₄, σ₃, σ₂, σ₁, Env.setVar, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2, ↓reduceIte]
    by_cases hvq : v = "qpow"
    · subst v; exact hq₀.trans hq.symm
    · exact r₀.frame_var v (by simp [computeLog, seqs, inc, Com.wvars, hv, hvq])
  · funext a
    exact hr.frame_arr a (by simp [clockSetup, computeLog, seqs, inc, Com.warrs])
  · exact hr.frame_inp (by simp [clockSetup, computeLog, seqs, inc, Com.reads])
  · exact hr.out_eq (by simp [clockSetup, computeLog, seqs, inc, Com.NoWrite])

end Lax457868Proofs.RefinedClockSetup
