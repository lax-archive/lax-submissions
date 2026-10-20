import Lax195003.WordRamRandomness
import Lax808846Proofs.Simulation
import Lax808846Proofs.Reasoning

/-! Transfer the refined source proof to the existing finite-tape word-RAM
contract. The registered compiler simulation supplies the machine execution;
no separate machine or randomness semantics are introduced here. -/

namespace Lax457868Proofs.RefinedMachineBridge

open Lax808846.Ram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Compile Lax808846Proofs.Simulation
open Lax195003.WordRamRandomness

/-- The registered compiler transfers a source cost bound, charging the final
halt instruction as well. -/
lemma compiled_run {L : Layout} {B w C : ℕ} {c : Com}
    {ext : String → ℕ} {input : List ℕ} {σ : Env}
    (hfit : L.FitsWords B w) (hok : Com.Ok L c)
    (hin : ∀ v ∈ input, v < B)
    (hr : Run B c (initEnv ext input) σ C) :
    ∃ t ≤ L.const * C + 1, RunsTo w (compileProgram L c) input σ.out t := by
  obtain ⟨k, hk, hrun⟩ := hr
  obtain ⟨t, ht, hmachine⟩ := compileProgram_runsTo hfit hok hin hrun
  exact ⟨t, ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 1), hmachine⟩

/-- Source runs on all tapes and a counted subset of correct source outputs
imply the exact public probability-and-time predicate. A separate success
flag is unnecessary: acceptance is the existing relation on output words. -/
lemma succeeds_of_source {L : Layout} {B w C r T : ℕ} {c : Com}
    {ext : String → ℕ} {input : List ℕ} {q : ℚ}
    {Accept : List ℕ → Prop} {good : Set (Fin r → Bool)}
    (hfit : L.FitsWords B w) (hok : Com.Ok L c)
    (hin : ∀ ρ : Fin r → Bool, ∀ v ∈ input ++ bitTape ρ, v < B)
    (hcost : L.const * C + 1 ≤ T)
    (htotal : ∀ ρ : Fin r → Bool,
      ∃ σ, Run B c (initEnv ext (input ++ bitTape ρ)) σ C)
    (hgood : ∀ ρ ∈ good, ∃ σ,
      Run B c (initEnv ext (input ++ bitTape ρ)) σ C ∧ Accept σ.out)
    (hcount : q * (2 ^ r : ℚ) ≤ (good.ncard : ℚ)) :
    SucceedsWithProbabilityAtLeastInTime q w (compileProgram L c)
      input r T Accept := by
  constructor
  · intro ρ
    obtain ⟨σ, hr⟩ := htotal ρ
    obtain ⟨t, ht, hmachine⟩ := compiled_run hfit hok (hin ρ) hr
    exact ⟨σ.out, t, ht.trans hcost, hmachine⟩
  · have hsub : good ⊆ {ρ : Fin r → Bool | ∃ y : List ℕ, ∃ t ≤ T,
        RunsTo w (compileProgram L c) (input ++ bitTape ρ) y t ∧ Accept y} := by
      intro ρ hρ
      obtain ⟨σ, hr, ha⟩ := hgood ρ hρ
      obtain ⟨t, ht, hm⟩ := compiled_run hfit hok (hin ρ) hr
      exact ⟨σ.out, t, ht.trans hcost, hm, ha⟩
    exact hcount.trans (by exact_mod_cast Set.ncard_le_ncard hsub)

end Lax457868Proofs.RefinedMachineBridge
