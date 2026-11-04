import Lax185574Proofs.RamSimBack
import Lax185574Proofs.RamSimulate

/-!
Backward soundness of `simulate`: if the simulator halts, the simulated
program halted on the rewritten input with the same output, and in no
more steps.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

theorem simulate_back (p₀ : Program) (ρ : Rewrite 1) (w : ℕ) (x y : List ℕ) (T : ℕ)
    (hK : simBase ρ ≤ 2 ^ (w - 1)) (hfit : ρ.Fits w (fun _ => x))
    (hrun : RunsTo w (simProg p₀ ρ) x y T) :
    ∃ t ≤ T, RunsTo (w - 1) p₀ (ρ.apply fun _ => x) y t := by
  obtain ⟨N, S_end, hr, hs, hy, hT⟩ := hrun
  obtain ⟨n₀, -, S7, e7, hpc7, R7⟩ := sim_start p₀ ρ w x hK hfit
  have hH : Halts w (simProg p₀ ρ) (initState x) N S_end := ⟨hr, hs⟩
  have hn₀ := e7.le_of_halts hH
  obtain ⟨j, s_j, h1, h2, hj, -⟩ := sim_back (simCode p₀ ρ) (p := simProg p₀ ρ)
    (pre := simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6) (post := [.halt])
    (simProg_eq p₀ ρ) (simPre_length ρ) le_rfl (simCode_tgt p₀ ρ) le_rfl
    (fun _ h => by cases h) R7 hpc7 (hH.rest e7)
  have hR : RunsTo (w - 1) p₀ (ρ.apply fun _ => x) s_j.out (j + terminalCost p₀ s_j) :=
    ⟨j, s_j, h1, h2, rfl, rfl⟩
  obtain ⟨t', -, hR'⟩ := simulate_run p₀ ρ w x s_j.out _ hK hfit hR
  have heq := (runsTo_unique ⟨N, S_end, hr, hs, hy, hT⟩ hR').1
  refine ⟨j + terminalCost p₀ s_j, by omega, heq ▸ hR⟩

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- **Simulation, both directions.** The simulator `p` of `simulate`
halts with the output of `p₀` on the rewritten input when `p₀` halts
there, and conversely every halting run of `p` comes from a halting run
of `p₀` with the same output and no more steps. -/
theorem simulate_sound :
    ∀ (p₀ : Program) (ρ : Rewrite 1), ∃ (p : Program) (K : ℕ),
      ∀ (w : ℕ) (x : List ℕ), K ≤ 2 ^ (w - 1) → ρ.Fits w (fun _ => x) →
        (∀ y t, RunsTo (w - 1) p₀ (ρ.apply fun _ => x) y t →
          ∃ t' ≤ K * t + K * ρ.cost (fun _ => x), RunsTo w p x y t') ∧
        (∀ y T, RunsTo w p x y T → ∃ t ≤ T, RunsTo (w - 1) p₀ (ρ.apply fun _ => x) y t) := by
  intro p₀ ρ
  refine ⟨simProg p₀ ρ, simBase ρ + stepBound (simKs ρ) + 20, fun w x hK hfit => ⟨?_, ?_⟩⟩
  · intro y t hrun
    obtain ⟨t', ht', hr⟩ := simulate_run p₀ ρ w x y t (by omega) hfit hrun
    refine ⟨t', le_trans ht' ?_, hr⟩
    have h1 := Nat.mul_le_mul_right t
      (show stepBound (simKs ρ) + 20 ≤ simBase ρ + stepBound (simKs ρ) + 20 by omega)
    have h2 := Nat.mul_le_mul_right (ρ.cost fun _ => x)
      (show stepBound (simKs ρ) + 20 ≤ simBase ρ + stepBound (simKs ρ) + 20 by omega)
    omega
  · intro y T hrun
    exact simulate_back p₀ ρ w x y T (by omega) hfit hrun

end Lax185574Proofs.Simulate
