import Lax235315.ConstructionProgram
import Lax195003.WelzlOrdersComputation

/-!
---
title: Separate guarantees for the construction program
type: definition
---
The construction has three independent obligations. Every random tape must
halt within the time budget. A run that reaches the final halt with its
success flag set must output a suitable graph Welzl order. At least two
thirds of all tapes must reach such a successful termination.

For a resource constant K, the time budget and tape length are both
K(|x|+1)(ceil(log₂ n)+1). The word-size condition is exactly the condition
of Lax195003 with that same K.

# Formalization notes

The successful-tape event checks the actual program counter and a designated
memory cell. It does not assume that the output is correct. The separate
output theorem must establish that implication.
The three contracts are predicates, not fields assumed by a program object.
They use the registered machine, CSR encoding, neighborhood complexity and
output relation directly. Each later claim supplies its own sufficient lower
bound on K; taking a common upper bound permits their composition without
guessing a numerical constant before the cost proof is complete.
-/

namespace Lax235315.ConstructionContracts
open Lax808846.Ram Lax11.GraphEncoding
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax195003.WelzlOrdersInGraphs Lax195003.WordRamRandomness
open Lax235315.ConstructionProgram

/-- The common step budget and random-tape length. -/
def timeBudget (K n : ℕ) (x : List ℕ) : ℕ :=
  K * (x.length + 1) * (Nat.clog 2 n + 1)

/-- A linearly bounded graph, its CSR encoding, and the registered word-size condition. -/
def ValidInput (K c n w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ) : Prop :=
  1 ≤ c ∧ HasLinearNeighborhoodComplexityWithConstant G c ∧
    EncodesGraph x n G ∧
    (∀ v ∈ c :: x, K * (x.length + v + 1) ≤ 2 ^ w)

/-- Termination at the final instruction with the success flag set, within T steps. -/
def SuccessfulTermination (w : ℕ) (input : List ℕ) (T : ℕ)
    (s : State) (t : ℕ) : Prop :=
  t ≤ T ∧ run w program t (initState input) = some s ∧
    step w program s = none ∧ s.pc + 1 = program.length ∧
      s.mem successFlagCell = 1

/-- The random tapes whose execution reaches a successful final state. -/
def goodTapes (w c : ℕ) (x : List ℕ) (T : ℕ) : Set (Fin T → Bool) :=
  {ρ | ∃ s t, SuccessfulTermination w ((c :: x) ++ bitTape ρ) T s t}

/-- Every random tape leads to a halted run within the common budget. -/
def HasRunningTimeBound (K : ℕ) : Prop :=
  ∀ (c n w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
    ValidInput K c n w G x →
      ∀ ρ : Fin (timeBudget K n x) → Bool,
        ∃ y : List ℕ, ∃ t ≤ timeBudget K n x,
          RunsTo w program ((c :: x) ++ bitTape ρ) y t

/-- Every successful final state contains an output meeting the registered crossing bound. -/
def HasCorrectOutput (K : ℕ) : Prop :=
  ∀ (c n w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
    ValidInput K c n w G x →
      ∀ (ρ : Fin (timeBudget K n x) → Bool) (s : State) (t : ℕ),
        SuccessfulTermination w ((c :: x) ++ bitTape ρ) (timeBudget K n x) s t →
          EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) s.out

/-- At least two thirds of the equally likely tapes reach a successful final state. -/
noncomputable def HasSuccessProbability (K : ℕ) : Prop :=
  ∀ (c n w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
    ValidInput K c n w G x →
      (2 / 3 : ℚ) * (2 ^ timeBudget K n x : ℚ) ≤
        ((goodTapes w c x (timeBudget K n x)).ncard : ℚ)

end Lax235315.ConstructionContracts
