import Lax185574Proofs.LoopScript
import Lax185574Proofs.Words.Computes

/-!
Glue programs written in IMP+, at the word lengths of the loop driver.

`glue_runsTo`: an IMP+ run whose values stay below `B` gives a halting
run of the compiled program at every word length `v` with room for `B`,
and every halting run there has the same output. `lp_room`: region `i`
of the driver has room for a number `N` if `(i + 1)² · N` fits into a
buffer.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Machine Lax808846Proofs.Simulation Lax185574Proofs.RamSim

/-- **Compiled glue.** -/
theorem glue_runsTo {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) {B v K : ℕ} {ext : String → ℕ}
    {u : List ℕ} {σ' : Env} (hB : 1 < B)
    (hBv : (L.temps + 2 + L.scalars.length + L.arrays.length + 1) * B ≤ 2 ^ v)
    (hu : ∀ y ∈ u, y < B) (hrun : Run B cmd (initEnv ext u) σ' K) :
    (∃ t ≤ L.const * K + 1, RunsTo v (compileProgram L cmd) u σ'.out t) ∧
      (∀ o t, RunsTo v (compileProgram L cmd) u o t → o = σ'.out) := by
  have hfit : L.FitsWords B v := by
    refine ⟨hB, ?_, ?_⟩
    · nlinarith
    · simp only [Layout.span]; nlinarith
  obtain ⟨k, hk, hbs⟩ := hrun
  obtain ⟨t, ht, hr⟩ := compileProgram_runsTo hfit hok hu hbs
  exact ⟨⟨t, le_trans ht (by gcongr), hr⟩, fun o t' h => (runsTo_unique h hr).1⟩

/-- **Room in a region.** -/
theorem lp_room {w i N : ℕ} (hN : 1 ≤ N) (h : (i + 1) ^ 2 * N ≤ lpCap w) :
    lpSize w i ≠ 0 ∧ N ≤ 2 ^ lpV w i := by
  have h1 : N ≤ lpCap w / (i + 1) ^ 2 := (Nat.le_div_iff_mul_le (by positivity)).2 (by linarith)
  have h2 := lpSize_ge w i
  have hs : lpSize w i ≠ 0 := by omega
  exact ⟨hs, by rw [← lpSize_eq hs]; omega⟩

theorem lpCap_eq {w : ℕ} (hw : 3 ≤ w) : 8 * lpCap w = 2 ^ w := by
  simp only [lpCap]
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega

end Lax185574Proofs.Simulate
