import Lax457868Proofs.AlgorithmRounds
import Lax457868Proofs.RefinedContraction
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
A finite successful reduction path stores the actual refined samples and
representative contractions chosen by each executed round.
-/

namespace Lax457868Proofs.ReductionPath

open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.AlgorithmRounds
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.RefinedContraction
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.ContractionRounds
open Lax457868Proofs.SamplerContract

/-- A finite run ending when the active ground set reaches the `2k` cutoff.
Each nonterminal node records its actual sample, actual representative
contraction, and recursive continuation on the retained sets. -/
inductive SuccessfulReductionPath {n : ℕ} (G : SimpleGraph (Fin n))
    (c k : ℕ) (hG : HasLinearNeighborhoodComplexityWithConstant G c) :
    Finset (Fin n) → Finset (Fin n) → Type
  | stop {A B : Finset (Fin n)} (hstop : A.card ≤ 2 * k) :
      SuccessfulReductionPath G c k hG A B
  | step {A B : Finset (Fin n)} (W : Finset (Fin n))
      (hsample : IsRefinedSample
        (neighborhoodFamily B (finiteNeighborhood G A))
        (A : Set (Fin n)) (W : Set (Fin n))
        ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
      (contraction : TraceContraction A B (finiteNeighborhood G A) W)
      (hcontinue : 2 * k < A.card)
      (tail : SuccessfulReductionPath G c k hG
        contraction.retainedA contraction.retainedB) :
      SuccessfulReductionPath G c k hG A B

namespace SuccessfulReductionPath

/-- The number of successful contractions in the stored finite path. -/
noncomputable def rounds {n : ℕ} {G : SimpleGraph (Fin n)} {c k : ℕ}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} :
    SuccessfulReductionPath G c k hG A B → ℕ
  | .stop _ => 0
  | .step _ _ _ _ tail => rounds tail + 1

/-- The active ground-set size at a depth in the path. Depth zero is the
current set; subsequent depths follow the stored recursive contractions. -/
noncomputable def activeGroundSize {n : ℕ} {G : SimpleGraph (Fin n)} {c k : ℕ}
    {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)}
    (path : SuccessfulReductionPath G c k hG A B) : ℕ → ℕ
  | 0 => A.card
  | depth + 1 =>
      match path with
      | .stop _ => 0
      | .step _ _ _ _ tail => activeGroundSize tail depth

end SuccessfulReductionPath

open SuccessfulReductionPath

/-- A stop node contributes no contraction to the executed prefix. -/
lemma active_ground_recurrence {n : ℕ} {G : SimpleGraph (Fin n)}
    {c k : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)}
    (hc : 2 ≤ c) (path : SuccessfulReductionPath G c k hG A B) :
    ∀ i, i < rounds path →
      2 * activeGroundSize path (i + 1) ≤
        activeGroundSize path i + 2 * c ^ 2 := by
  induction path with
  | stop hstop =>
      intro i hi
      simp [rounds] at hi
  | step W hsample contraction hcontinue tail ih =>
      intro i hi
      cases i with
      | zero =>
          simpa [rounds, activeGroundSize] using
            graph_traceContraction_size_bound hG hc _ _ W hsample contraction
      | succ i =>
          have hi' : i < rounds tail := by simpa [rounds] using hi
          simpa [rounds, activeGroundSize] using ih i hi'

/-- Every depth in the successful prefix satisfies the algorithm's
continuation guard. -/
lemma active_ground_guard {n : ℕ} {G : SimpleGraph (Fin n)}
    {c k : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)}
    (path : SuccessfulReductionPath G c k hG A B) :
    ∀ i, i < rounds path → 2 * k < activeGroundSize path i := by
  induction path with
  | stop hstop =>
      intro i hi
      simp [rounds] at hi
  | step W hsample contraction hcontinue tail ih =>
      intro i hi
      cases i with
      | zero => simpa [activeGroundSize] using hcontinue
      | succ i =>
          have hi' : i < rounds tail := by simpa [rounds] using hi
          simpa [rounds, activeGroundSize] using ih i hi'

/-- The stored path has at most `clog₂(|A|)-1` contractions whenever its
initial ground set has at least two elements and `6c² ≤ k`. -/
lemma successful_path_round_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    {c k : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (hA : 2 ≤ A.card)
    (path : SuccessfulReductionPath G c k hG A B) :
    rounds path + 1 ≤ Nat.clog 2 A.card := by
  have hrun := finite_run_iterations (activeGroundSize path) c k (rounds path)
    hc hk (by simpa [activeGroundSize] using hA)
    (active_ground_recurrence hc path) (active_ground_guard path)
  simpa [activeGroundSize] using hrun

/-- The exact refined Welzl cutoff yields the logarithmic successful-round
bound for every stored path. -/
lemma refined_path_round_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    {c : ℕ} {hG : HasLinearNeighborhoodComplexityWithConstant G c}
    {A B : Finset (Fin n)} (hc : 2 ≤ c) (hA : 2 ≤ A.card)
    (path : SuccessfulReductionPath G c
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      hG A B) :
    rounds path + 1 ≤ Nat.clog 2 A.card := by
  exact successful_path_round_bound hc (refined_cutoff_ge_six_sq c hc) hA path

end Lax457868Proofs.ReductionPath
