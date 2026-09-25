import Lax235315.ConstructionRuntime
import Lax235315.ConstructionCorrectness
import Lax235315.ConstructionProbability
import Lax195003.WelzlOrdersComputation
import Lax808846Proofs.Machine
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
Conditional assembly of the three construction contracts into the registered
Welzl-order algorithm statement.  This module proves only that the runtime,
correctness, and probability claims suffice together; it does not prove any
of those three open claims.
-/

namespace Lax235315Proofs.Assembly

open Lax11.GraphEncoding
open Lax199508.GraphClasses
open Lax195003.WelzlOrdersComputation
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax195003.WordRamRandomness
open Lax808846.Ram
open Lax235315.ConstructionContracts
open Lax235315.ConstructionProgram

/-- A tape counted as successful by the finite-tape contract is accepted by
the registered randomized-computation predicate whenever the program's
successful-output contract holds. -/
theorem goodTapes_subset_accepted
    {K c n w : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hvalid : ValidInput K c n w G x)
    (hcorrect : HasCorrectOutput K) :
    goodTapes w c x (timeBudget K n x) ⊆
      {ρ | ∃ y : List ℕ, ∃ t ≤ timeBudget K n x,
        RunsTo w program ((c :: x) ++ bitTape ρ) y t ∧
          EncodesGraphWelzlOrder G 1
            (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) y} := by
  intro ρ hρ
  rcases hρ with ⟨s, t, hterm⟩
  rcases hterm with ⟨ht, hrun, hhalt, hpc, hflag⟩
  have hgoodRun : RunsTo w program ((c :: x) ++ bitTape ρ) s.out (t + 1) := by
    refine ⟨t, s, hrun, hhalt, rfl, ?_⟩
    have hpc' : s.pc < program.length := by omega
    rw [Lax808846Proofs.Machine.terminalCost_eq, if_pos hpc']
  refine ⟨s.out, t + 1, ht, hgoodRun, ?_⟩
  exact hcorrect c n w G x hvalid ρ s t
    ⟨ht, hrun, hhalt, hpc, hflag⟩

/-- For any common resource constant, the three contracts assemble into the
exact statement made by Lax195003. -/
theorem exists_program_of_contracts
    {K : ℕ} (hK : 1 ≤ K)
    (hruntime : HasRunningTimeBound K)
    (hcorrect : HasCorrectOutput K)
    (hprobability : HasSuccessProbability K) :
    ∃ (p : Lax808846.Ram.Program) (K' : ℕ), 1 ≤ K' ∧
      ∀ (C : GraphClass) (c : ℕ), 1 ≤ c →
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          HasLinearNeighborhoodComplexityWithConstant G c) →
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          ∀ (w : ℕ) (x : List ℕ), EncodesGraph x n G →
          (∀ v ∈ c :: x, K' * (x.length + v + 1) ≤ 2 ^ w) →
          let T := K' * (x.length + 1) * (Nat.clog 2 n + 1)
          SucceedsWithProbabilityAtLeastInTime
            (2 / 3 : ℚ) w p (c :: x) T T
            (EncodesGraphWelzlOrder G 1
              (12 * c ^ 2 * (Nat.clog 2 n) ^ 2)) := by
  refine ⟨program, K, hK, ?_⟩
  intro C c hc hclass n G hG w x hx hfit
  let T := K * (x.length + 1) * (Nat.clog 2 n + 1)
  have hvalid : ValidInput K c n w G x :=
    ⟨hc, hclass n G hG, hx, hfit⟩
  change SucceedsWithProbabilityAtLeastInTime
    (2 / 3 : ℚ) w program (c :: x) T T
    (EncodesGraphWelzlOrder G 1
      (12 * c ^ 2 * (Nat.clog 2 n) ^ 2))
  constructor
  · intro ρ
    exact hruntime c n w G x hvalid ρ
  · have hgood := hprobability c n w G x hvalid
    have hsubset := goodTapes_subset_accepted hvalid hcorrect
    have hcard :
        (goodTapes w c x T).ncard ≤
          ({ρ | ∃ y : List ℕ, ∃ t ≤ T,
            RunsTo w program ((c :: x) ++ bitTape ρ) y t ∧
              EncodesGraphWelzlOrder G 1
                (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) y}).ncard :=
      Set.ncard_le_ncard hsubset
    calc
      (2 / 3 : ℚ) * (2 ^ T : ℚ) ≤
          ((goodTapes w c x T).ncard : ℚ) := hgood
      _ ≤ _ := by exact_mod_cast hcard

/--
---
conclusion: Lax195003.WelzlOrdersComputation.exists_nearLinearTime_randomized_welzlOrder_program
assumptions:
  - Lax235315.ConstructionRuntime.eventually_hasRunningTimeBound
  - Lax235315.ConstructionCorrectness.eventually_hasCorrectOutput
  - Lax235315.ConstructionProbability.eventually_hasSuccessProbability
---
**Conditional assembly for the near-linear Welzl-order algorithm.** This proof
assembles the construction's three independent contracts. It is
conditional on their runtime, output-correctness, and finite-tape probability
claims; it does not discharge those claims.

# Proof strategy

Take the sum of the three eventual resource thresholds. The runtime contract
gives total halting on every tape. Every tape in the successful-final-state
set yields a `RunsTo` witness, and the output contract makes that output
acceptable. Monotonicity of finite cardinality transfers the probability
lower bound from successful tapes to accepted tapes.

# Attribution

The conditional contracts are the three separate theorem concepts in this
submission. The assembled target is the registered claim of Lax195003;
the graph result is Theorem 1.4 in the supplied arXiv v1 PDF.
-/
theorem exists_nearLinearTime_randomized_welzlOrder_program :
    ∃ (p : Program) (K : ℕ), 1 ≤ K ∧
      ∀ (C : GraphClass) (c : ℕ), 1 ≤ c →
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          HasLinearNeighborhoodComplexityWithConstant G c) →
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          ∀ (w : ℕ) (x : List ℕ), EncodesGraph x n G →
          (∀ v ∈ c :: x, K * (x.length + v + 1) ≤ 2 ^ w) →
          let T := K * (x.length + 1) * (Nat.clog 2 n + 1)
          SucceedsWithProbabilityAtLeastInTime
            (2 / 3 : ℚ) w p (c :: x) T T
            (EncodesGraphWelzlOrder G 1
              (12 * c ^ 2 * (Nat.clog 2 n) ^ 2)) := by
  obtain ⟨Kr, hKr, hRuntime⟩ :=
    Lax235315.ConstructionRuntime.eventually_hasRunningTimeBound
  obtain ⟨Kc, hKc, hCorrect⟩ :=
    Lax235315.ConstructionCorrectness.eventually_hasCorrectOutput
  obtain ⟨Kp, hKp, hProbability⟩ :=
    Lax235315.ConstructionProbability.eventually_hasSuccessProbability
  let K := Kr + Kc + Kp
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKrK : Kr ≤ K := by dsimp [K]; omega
  have hKcK : Kc ≤ K := by dsimp [K]; omega
  have hKpK : Kp ≤ K := by dsimp [K]; omega
  exact exists_program_of_contracts hK
    (hRuntime K hKrK) (hCorrect K hKcK) (hProbability K hKpK)

end Lax235315Proofs.Assembly
