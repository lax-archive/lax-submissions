import Lax457868Proofs.RefinedProgramProbability
import Lax457868Proofs.RefinedTapeReserve
import Lax457868.RefinedWelzlOrders

/-! The remaining source-law obligation and its exact compiler consequence.
This module does not claim that the source-law obligation has been proved. -/
namespace Lax457868Proofs.RefinedFinalBridge
open Lax808846.Ram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax195003.WordRamRandomness Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodComplexity Lax11.GraphEncoding
open Lax457868Proofs.RefinedProgramSource Lax457868Proofs.RefinedProgramLayout
open Lax457868Proofs.RefinedProgramProbability Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

/-- The concrete algorithm's pending global source estimate: actual runs on
all tapes, correct output outside a small failure event, and an unconditional
near-linear mean cost. No ideal sampler or successful sample is assumed. -/
def BodyLaw (M : ℕ) : Prop :=
  ∀ (B c n : ℕ) (G : SimpleGraph (Fin n)),
    2 ≤ c → 2 ≤ n → HasLinearNeighborhoodComplexityWithConstant G c →
    ∀ x : List ℕ, EncodesGraph x n G →
    4 * (x.length + 1) ≤ B → 768 < B →
    ∀ σ : Env, RefinedSetup.Ready c n x [] σ →
      RefinedRecordedCommit.ValuesBounded B σ →
      ∀ N : ℕ, n * roundBitReserve c n ≤ N →
      ∃ (final : Tape N → Env) (cost : Tape N → ℕ) (bad : Finset (Tape N)),
        (∀ ρ, Run B algorithmBody {σ with inp := bitTape ρ} (final ρ) (cost ρ)) ∧
        (∀ ρ, ρ ∉ bad → EncodesGraphWelzlOrder G 1
          (2 * refinedCutoffK c * Nat.clog 2 n) (final ρ).out) ∧
        (∑ ρ, cost ρ) ≤ M * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N ∧
        6 * bad.card ≤ 2 ^ N

/-- A single derived constant pays for source words, layout addresses, the
clocked source time, and the compiler's final halt instruction. -/
def timeCoefficient (D : ℕ) : ℕ :=
  layoutFactor * (D + 770) + programLayout.const * sourceCoefficient D +
    sourceCoefficient D + 1

/-- Once the actual source law is established, the exact public theorem
follows with this fixed compiled program and the same input-word premise. -/
lemma main_of_body_law {M : ℕ} (hM : 1 ≤ M) (hbody : BodyLaw M) :
    ∃ (p : Program) (Ktime : ℕ), 1 ≤ Ktime ∧
      ∀ (c n : ℕ) (G : SimpleGraph (Fin n)),
        2 ≤ c → 2 ≤ n →
        HasLinearNeighborhoodComplexityWithConstant G c →
        ∀ (w : ℕ) (x : List ℕ), EncodesGraph x n G →
          (∀ v ∈ c :: x, Ktime * (x.length + v + 1) ≤ 2 ^ w) →
          let T := Ktime * (x.length + 1) * (Nat.clog 2 n + 1)
          SucceedsWithProbabilityAtLeastInTime
            (2 / 3 : ℚ) w p (c :: x) T T
            (EncodesGraphWelzlOrder G 1
              (2 * (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) *
                Nat.clog 2 c + 1) * Nat.clog 2 n)) := by
  classical
  let D := 6 * M
  let K := timeCoefficient D
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hK : 1 ≤ K := by dsimp [K, timeCoefficient]; omega
  refine ⟨compileProgram programLayout (programSource D), K, hK, ?_⟩
  intro c n G hc hn hNC w x hx hword
  let B := 2 ^ w / layoutFactor
  let T := K * (x.length + 1) * (Nat.clog 2 n + 1)
  let N := T + n * roundBitReserve c n
  have hscale : ∀ v ∈ c :: x,
      layoutFactor * (D + 770) * (x.length + v + 1) ≤ 2 ^ w := by
    intro v hv
    exact (Nat.mul_le_mul_right _ (by dsimp [K, timeCoefficient]; omega)).trans
      (hword v hv)
  obtain ⟨hfit, hbase, hinput⟩ :=
    fitted_bound_of_input_scale (D + 770) c w x (by omega) hscale
  change (D + 770) * (x.length + 1) ≤ B at hbase
  have hB : 4 * (x.length + 1) ≤ B := by
    nlinarith
  have h768 : 768 < B := by nlinarith
  have hclock : D * (x.length + 1) < B := by nlinarith
  obtain ⟨σ, hinit, R, hb, hready, hcapacity⟩ :=
    initialize_with_clock_run (bits := []) hx hc hn hB h768
      (by simpa using hinput) hD hclock
  have hlog : Nat.clog 2 n ≤ x.length := by
    have hh := Nat.clog_le_of_le_pow n.lt_two_pow_self.le
    have hxlen := hx.length_eq
    omega
  obtain ⟨final, cost, bad, hrun, hcorrect, hmean, hbad⟩ :=
    hbody B c n G hc hn hNC x hx hB h768 σ R hb N (by dsimp [N]; omega)
  have hmean' : 6 * (∑ ρ, cost ρ) ≤
      (D * (x.length + 1) * (Nat.clog 2 n + 1)) * 2 ^ N := by
    have hh := Nat.mul_le_mul_left 6 hmean
    simpa only [D, Nat.mul_assoc] using hh
  obtain ⟨good, hcard, htotal, hgood⟩ := program_runs_of_mean R
    (by simpa using hinit) hready hcapacity hD hlog
    final cost bad _ hrun hcorrect hmean' hbad
  have hcoeff : sourceCoefficient D ≤ K := by dsimp [K, timeCoefficient]; omega
  have hCr : sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1) ≤ T := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoeff)
  have hcost : programLayout.const *
      (sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1)) + 1 ≤ T := by
    have hcoef : programLayout.const * sourceCoefficient D + 1 ≤ K := by
      dsimp [K, timeCoefficient]; omega
    have hprod : 1 ≤ (x.length + 1) * (Nat.clog 2 n + 1) := by nlinarith
    have hh := Nat.mul_le_mul_right ((x.length + 1) * (Nat.clog 2 n + 1)) hcoef
    dsimp [T]
    nlinarith
  have hin : ∀ ρ : Tape T, ∀ v ∈ (c :: x) ++ bitTape ρ, v < B := by
    intro ρ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hinput v hv
    · simp only [bitTape, List.mem_ofFn] at hv
      obtain ⟨i, rfl⟩ := hv
      cases ρ i <;> simp <;> omega
  have hcount : (2 / 3 : ℚ) * 2 ^ N ≤ (good.card : ℚ) := by
    have hh : (2 : ℚ) * 2 ^ N ≤ 3 * (good.card : ℚ) := by exact_mod_cast hcard
    linarith
  exact RefinedFiniteTape.succeeds_of_long_tapes good hfit (programSource_ok D)
    hin (by dsimp [N]; omega) hCr hcost htotal hgood hcount

end Lax457868Proofs.RefinedFinalBridge
