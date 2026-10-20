import Lax457868Proofs.RefinedProgramLayout
import Lax457868Proofs.RefinedClockProbability
import Lax457868Proofs.RefinedFiniteTape

/-! Compose actual initialization, the bounded clock, and the registered RAM
compiler. The probabilistic premises remain explicit inputs to this bridge. -/
namespace Lax457868Proofs.RefinedProgramProbability
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Compile
open Lax195003.WordRamRandomness
open Lax457868Proofs.RefinedProgramSource
open Lax457868Proofs.RefinedProgramLayout
open Lax457868Proofs.ClockedSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

/-- Derived initialization and clock overhead. -/
def sourceCoefficient (D : ℕ) : ℕ :=
  324 + clockFactor algorithmBody * (D + 1)

private lemma reassociate_run {B K J : ℕ} {a b d : Com} {σ μ τ : Env}
    (h : Run B (a.seq b) σ μ K) (h' : Run B d μ τ J) :
    Run B (a.seq (b.seq d)) σ τ (K + J) := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨j, hj, hd⟩ := h'
  cases hb with
  | seq ha hb => exact ⟨_, by omega, .seq ha (.seq hb hd)⟩

/-- Actual body mean and failure counts imply uniformly bounded runs of the
whole fixed source program on every long analysis tape. -/
lemma program_runs_of_mean {B c n D N : ℕ} {x : List ℕ} {σ : Env}
    (R : RefinedSetup.Ready c n x [] σ)
    (hinit : Run B (RefinedSetup.refinedSetupSource.seq (RefinedClockSetup.clockSetup D))
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) (c :: x)) σ
      (40 * (x.length + Nat.clog 2 n + 1) + 24 * Nat.clog 2 n + 284))
    (hready : ClockedSource.Ready B (D * (x.length + 1)) σ)
    (hcapacity : capacity (D * (x.length + 1)) σ =
      D * (x.length + 1) * (Nat.clog 2 n + 1))
    (hD : 1 ≤ D) (hlog : Nat.clog 2 n ≤ x.length)
    (final : Tape N → Env) (cost : Tape N → ℕ) (bad : Finset (Tape N))
    (Accept : List ℕ → Prop)
    (hrun : ∀ ρ, Run B algorithmBody {σ with inp := bitTape ρ} (final ρ) (cost ρ))
    (hcorrect : ∀ ρ, ρ ∉ bad → Accept (final ρ).out)
    (hmean : 6 * (∑ ρ, cost ρ) ≤
      (D * (x.length + 1) * (Nat.clog 2 n + 1)) * 2 ^ N)
    (hbad : 6 * bad.card ≤ 2 ^ N) :
    ∃ good : Finset (Tape N), 2 * 2 ^ N ≤ 3 * good.card ∧
      (∀ ρ : Tape N, ∃ τ, Run B (programSource D)
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ
        (sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1))) ∧
      ∀ (ρ : Tape N), ρ ∈ good → ∃ τ, Run B (programSource D)
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ
        (sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1)) ∧
        Accept τ.out := by
  let initial : Tape N → Env := fun ρ => {σ with inp := bitTape ρ}
  have hready' (ρ : Tape N) :
      ClockedSource.Ready B (D * (x.length + 1)) (initial ρ) :=
    ⟨hready.positive, hready.sizeBound, hready.blockSize,
      hready.blocksBound, hready.slotsBound, hready.active⟩
  have hcap : 0 < D * (x.length + 1) * (Nat.clog 2 n + 1) := by positivity
  obtain ⟨good, hcard, htotal, hgood⟩ := RefinedClockProbability.clocked_runs_of_mean
    algorithmBody_fresh initial initial final cost bad Accept hrun hready'
    (fun ρ => sameSource_refl (initial ρ)) (fun _ => hcapacity) hcorrect hcap
    (by simpa only [card_tape] using hmean)
    (by simpa only [card_tape] using hbad)
  have hbound :
      (40 * (x.length + Nat.clog 2 n + 1) + 24 * Nat.clog 2 n + 284) +
        clockFactor algorithmBody *
          (D * (x.length + 1) * (Nat.clog 2 n + 1) + 1) ≤
        sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1) := by
    have hi : 40 * (x.length + Nat.clog 2 n + 1) +
        24 * Nat.clog 2 n + 284 ≤ 324 * (x.length + 1) := by omega
    have hl : 1 ≤ (x.length + 1) * (Nat.clog 2 n + 1) := by nlinarith
    have hf := Nat.mul_le_mul_left (clockFactor algorithmBody) hl
    have hi' : 324 * (x.length + 1) ≤
        324 * (x.length + 1) * (Nat.clog 2 n + 1) := by nlinarith
    dsimp [sourceCoefficient]
    nlinarith
  have whole (ρ : Tape N) (τ : Env)
      (hr : Run B (clocked algorithmBody) (initial ρ) τ
        (clockFactor algorithmBody *
          (D * (x.length + 1) * (Nat.clog 2 n + 1) + 1))) :
      Run B (programSource D)
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ
        (sourceCoefficient D * (x.length + 1) * (Nat.clog 2 n + 1)) := by
    have hh := reassociate_run
      (initialization_preserves_random_suffix R hinit (bitTape ρ)) hr
    exact hh.mono hbound
  refine ⟨good, by simpa only [card_tape] using hcard, ?_, ?_⟩
  · intro ρ
    obtain ⟨τ, hr⟩ := htotal ρ
    exact ⟨τ, whole ρ τ hr⟩
  · intro ρ hρ
    obtain ⟨τ, hr, ha⟩ := hgood ρ hρ
    exact ⟨τ, whole ρ τ hr, ha⟩

end Lax457868Proofs.RefinedProgramProbability
