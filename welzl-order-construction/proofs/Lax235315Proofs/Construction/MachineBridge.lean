import Lax235315Proofs.Construction.DriverSetup
import Lax235315Proofs.ProgramLink
import Lax808846Proofs.Simulation
import Mathlib.Tactic

/-! Lifting the source program to the proof-local word-RAM contracts.
These lemmas discharge the compiler, address, terminal-state and success-flag
bridges; they do not assume runtime, correctness or probability. -/

namespace Lax235315Proofs.Construction.MachineBridge

open Lax808846.Ram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Compile Lax808846Proofs.Simulation Lax808846Proofs.Machine
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.ProgramLink
open Lax235315Proofs.ProofProgram Lax235315Proofs.ConstructionContracts
open Lax195003.WordRamRandomness Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax11.GraphEncoding

/-- A linear value/index bound for source executions, with room for guarded arithmetic. -/
def sourceBound (c : ℕ) (x : List ℕ) : ℕ := 64 * (x.length + c + 1)

/-- A fixed archive resource constant pays for the interleaved array addresses. -/
lemma fitsWords_of_validInput {K c n w : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (hK : 2500 ≤ K) (hvalid : ValidInput K c n w G x) :
    layout.FitsWords (sourceBound c x) w := by
  have hfit := hvalid.2.2.2 c (by simp)
  have hbase : 1 ≤ x.length + c + 1 := by omega
  refine ⟨by dsimp [sourceBound]; omega, ?_, ?_⟩
  · dsimp [sourceBound]
    nlinarith
  · norm_num [Layout.span, layout, scalarNames, arrayNames, keyNames]
    dsimp [sourceBound]
    nlinarith

/-- The full input, including any finite bit suffix, fits the source value bound. -/
lemma input_bounded {c n T : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (ρ : Fin T → Bool) :
    ∀ v ∈ (c :: x) ++ bitTape ρ, v < sourceBound c x := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_cons.mp hv with rfl | hv
    · dsimp [sourceBound]; omega
    · have hlt := Lax11Proofs.CC.mem_lt_length hx hv
      dsimp [sourceBound]; omega
  · simp only [bitTape, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    split <;> (dsimp [sourceBound]; omega)

/-- Any bounded source execution reaches the actual final halt and represents
its final environment, with the machine's final instruction charged. -/
lemma sourceRun_terminal {B w C : ℕ} {input : List ℕ} {ext : String → ℕ}
    {σ : Env} (hfit : layout.FitsWords B w)
    (hin : ∀ v ∈ input, v < B)
    (hr : Run B welzlCom (initEnv ext input) σ C) :
    ∃ (t : ℕ) (s : State), t + 1 ≤ 10 * C + 1 ∧
      run w program t (initState input) = some s ∧
      step w program s = none ∧ s.pc + 1 = program.length ∧
      Represents layout σ s := by
  obtain ⟨k, hk, hbs⟩ := hr
  obtain ⟨t, s, ht, hrun, hpc, hrep⟩ :=
    compile_correct hfit hbs welzlCom_ok (initEnv_inpBounded ext hin)
      0 (initState input) rfl (represents_initState layout ext input)
      (fits_self (compile layout welzlCom 0) [Instr.halt])
  have hhalt : (compileProgram layout welzlCom)[s.pc]? = some Instr.halt := by
    rw [hpc, compileProgram]
    rw [List.getElem?_append_right (by simp)]
    simp
  refine ⟨t, s, ?_, ?_, ?_, ?_, hrep⟩
  · dsimp [Layout.const] at ht
    omega
  · simpa [program_eq_compilation, welzlProgram, compileProgram] using hrun
  · rw [program_eq_compilation]
    change step w (compileProgram layout welzlCom) s = none
    rw [step_eq, hhalt]
    rfl
  · rw [program_eq_compilation]
    simp [welzlProgram, compileProgram, hpc]

/-- The source run's successful flag is exactly the successful-tape predicate. -/
lemma sourceRun_successful {B w C T : ℕ} {input : List ℕ}
    {ext : String → ℕ} {σ : Env} (hfit : layout.FitsWords B w)
    (hin : ∀ v ∈ input, v < B)
    (hr : Run B welzlCom (initEnv ext input) σ C)
    (hcost : 10 * C + 1 ≤ T) (hgood : σ.vars "good" = 1) :
    ∃ s t, SuccessfulTermination w input T s t ∧ s.out = σ.out := by
  obtain ⟨t, s, ht, hrun, hhalt, hpc, hrep⟩ := sourceRun_terminal hfit hin hr
  refine ⟨s, t, ⟨ht.trans hcost, hrun, hhalt, hpc, ?_⟩, hrep.out⟩
  rw [successFlagCell_eq, hrep.vars "good" (by decide), hgood]

/-- A complete source run gives a halted word-RAM run even when its flag is zero. -/
lemma sourceRun_runsTo {B w C : ℕ} {input : List ℕ}
    {ext : String → ℕ} {σ : Env} (hfit : layout.FitsWords B w)
    (hin : ∀ v ∈ input, v < B)
    (hr : Run B welzlCom (initEnv ext input) σ C) :
    ∃ t ≤ 10 * C + 1, RunsTo w program input σ.out t := by
  obtain ⟨t, s, ht, hrun, hhalt, hpc, hrep⟩ := sourceRun_terminal hfit hin hr
  refine ⟨t + 1, ht, t, s, hrun, hhalt, hrep.out, ?_⟩
  rw [terminalCost_eq, if_pos (by omega)]

/-- Determinism identifies any successful machine termination with the source
run's final environment; both the flag and the output are recovered. -/
lemma successfulTermination_agrees {B w C T t : ℕ} {input : List ℕ}
    {ext : String → ℕ} {σ : Env} {s : State} (hfit : layout.FitsWords B w)
    (hin : ∀ v ∈ input, v < B)
    (hr : Run B welzlCom (initEnv ext input) σ C)
    (hs : SuccessfulTermination w input T s t) :
    σ.vars "good" = 1 ∧ s.out = σ.out := by
  obtain ⟨u, s', hu, hrun, hhalt, hpc, hrep⟩ := sourceRun_terminal hfit hin hr
  obtain ⟨-, heq⟩ := terminal_run_unique hs.2.1 hs.2.2.1 hrun hhalt
  subst s'
  refine ⟨?_, hrep.out⟩
  rw [← hrep.vars "good" (by decide), ← successFlagCell_eq]
  exact hs.2.2.2.2

/-- Lift source output correctness to any accepted machine final state. -/
lemma correct_output_of_sourceRun {B w C T t n c : ℕ} {input : List ℕ}
    {ext : String → ℕ} {σ : Env} {s : State} {G : SimpleGraph (Fin n)}
    (hfit : layout.FitsWords B w) (hin : ∀ v ∈ input, v < B)
    (hr : Run B welzlCom (initEnv ext input) σ C)
    (hcorrect : σ.vars "good" = 1 →
      EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) σ.out)
    (hs : SuccessfulTermination w input T s t) :
    EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) s.out := by
  obtain ⟨hgood, hout⟩ := successfulTermination_agrees hfit hin hr hs
  rw [hout]
  exact hcorrect hgood

/-- Good tapes expressed only through the explicit source program and its flag. -/
def sourceGoodTapes (c n : ℕ) (x : List ℕ) (C T : ℕ) : Set (Fin T → Bool) :=
  {ρ | ∃ σ, Run (sourceBound c x) welzlCom
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) σ C ∧ σ.vars "good" = 1}

/-- Source successful tapes are genuinely successful machine tapes, without
assuming that their output is correct. -/
lemma sourceGoodTapes_subset {K c n w C : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (hK : 2500 ≤ K) (hvalid : ValidInput K c n w G x)
    (hcost : 10 * C + 1 ≤ timeBudget K n x) :
    sourceGoodTapes c n x C (timeBudget K n x) ⊆
      goodTapes w c x (timeBudget K n x) := by
  rintro ρ ⟨σ, hr, hgood⟩
  obtain ⟨s, t, hs, -⟩ := sourceRun_successful
    (fitsWords_of_validInput hK hvalid) (input_bounded hvalid.2.2.1 ρ)
    hr hcost hgood
  exact ⟨s, t, hs⟩


/-- The mathematical and encoding hypotheses used by the source driver. -/
def SourceInput (c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ) : Prop :=
  1 ≤ c ∧ HasLinearNeighborhoodComplexityWithConstant G c ∧ EncodesGraph x n G

/-- Source cost with the same near-linear shape as the machine budget. -/
def sourceCost (A n : ℕ) (x : List ℕ) : ℕ :=
  A * (x.length + 1) * (Nat.clog 2 n + 1)

/-- Complete source executions exist on every sufficiently long finite tape. -/
def SourceTotal (A : ℕ) : Prop :=
  ∀ (c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ), SourceInput c n G x →
    ∀ T, sourceCost A n x ≤ T → ∀ ρ : Fin T → Bool,
      ∃ σ, Run (sourceBound c x) welzlCom
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) σ (sourceCost A n x)

/-- A successful source final environment contains the required graph order. -/
def SourceCorrect (A : ℕ) : Prop :=
  ∀ (c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ), SourceInput c n G x →
    ∀ T, sourceCost A n x ≤ T → ∀ (ρ : Fin T → Bool) (σ : Env),
      Run (sourceBound c x) welzlCom
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) σ (sourceCost A n x) →
      σ.vars "good" = 1 →
        EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) σ.out

/-- At least two thirds of sufficiently long tapes end with the source success flag. -/
noncomputable def SourceProbability (A : ℕ) : Prop :=
  ∀ (c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ), SourceInput c n G x →
    ∀ T, sourceCost A n x ≤ T →
      (2 / 3 : ℚ) * (2 ^ T : ℚ) ≤
        ((sourceGoodTapes c n x (sourceCost A n x) T).ncard : ℚ)

lemma sourceInput_of_validInput {K c n w : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (h : ValidInput K c n w G x) : SourceInput c n G x :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- A constant factor of ten, plus a single charged halt, suffices uniformly. -/
lemma cost_lift {A K n : ℕ} {x : List ℕ} (hK : 10 * A + 1 ≤ K) :
    10 * sourceCost A n x + 1 ≤ timeBudget K n x := by
  have hprod : 1 ≤ (x.length + 1) * (Nat.clog 2 n + 1) :=
    Nat.mul_le_mul (by omega : 1 ≤ x.length + 1) (by omega : 1 ≤ Nat.clog 2 n + 1)
  have hmul := Nat.mul_le_mul_right ((x.length + 1) * (Nat.clog 2 n + 1)) hK
  dsimp [sourceCost, timeBudget]
  nlinarith

lemma sourceCost_le_timeBudget {A K n : ℕ} {x : List ℕ}
    (hK : 10 * A + 1 ≤ K) : sourceCost A n x ≤ timeBudget K n x := by
  have h := cost_lift (n := n) (x := x) hK
  omega

/-- A proved source totality/cost argument discharges the exact public runtime
contract, with no remaining machine simulation obligations. -/
lemma runtime_of_source {A K : ℕ} (htotal : SourceTotal A)
    (hfitK : 2500 ≤ K) (hcostK : 10 * A + 1 ≤ K) : HasRunningTimeBound K := by
  intro c n w G x hv ρ
  obtain ⟨σ, hr⟩ := htotal c n G x (sourceInput_of_validInput hv)
    (timeBudget K n x) (sourceCost_le_timeBudget hcostK) ρ
  obtain ⟨t, ht, hrun⟩ := sourceRun_runsTo (fitsWords_of_validInput hfitK hv)
    (input_bounded hv.2.2.1 ρ) hr
  exact ⟨σ.out, t, ht.trans (cost_lift hcostK), hrun⟩

/-- A source correctness invariant transfers to every successful machine
termination; totality supplies the source run with which determinism compares it. -/
lemma correctness_of_source {A K : ℕ} (htotal : SourceTotal A)
    (hcorrect : SourceCorrect A) (hfitK : 2500 ≤ K) (hcostK : 10 * A + 1 ≤ K) :
    HasCorrectOutput K := by
  intro c n w G x hv ρ s t hs
  have hin := sourceInput_of_validInput hv
  have hbudget := sourceCost_le_timeBudget (n := n) (x := x) hcostK
  obtain ⟨σ, hr⟩ := htotal c n G x hin (timeBudget K n x) hbudget ρ
  exact correct_output_of_sourceRun (fitsWords_of_validInput hfitK hv)
    (input_bounded hv.2.2.1 ρ) hr
    (hcorrect c n G x hin (timeBudget K n x) hbudget ρ σ hr) hs

/-- Finite source-tape counting transfers to the registered probability
contract by inclusion of the actual successful-terminal-state events. -/
lemma probability_of_source {A K : ℕ} (hprob : SourceProbability A)
    (hfitK : 2500 ≤ K) (hcostK : 10 * A + 1 ≤ K) : HasSuccessProbability K := by
  intro c n w G x hv
  have hcount := hprob c n G x (sourceInput_of_validInput hv)
    (timeBudget K n x) (sourceCost_le_timeBudget hcostK)
  have hsub := sourceGoodTapes_subset (C := sourceCost A n x)
    hfitK hv (cost_lift hcostK)
  have hcard := Set.ncard_le_ncard hsub
  exact hcount.trans (by exact_mod_cast hcard)

end Lax235315Proofs.Construction.MachineBridge
