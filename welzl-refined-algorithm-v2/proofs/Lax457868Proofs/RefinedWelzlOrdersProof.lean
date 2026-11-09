import Lax457868Proofs.RefinedGlobalAssembly
import Lax457868Proofs.RefinedPreparedMean
import Lax457868Proofs.RefinedRoundFailure

/-! The refined black-box program theorem, discharged from the actual source
cost and failure estimates and the registered word-RAM compiler. -/
namespace Lax457868Proofs.RefinedWelzlOrdersProof
open Lax11.GraphEncoding
open Lax808846.Ram
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax195003.WordRamRandomness

private lemma source_law : RefinedFinalBridge.BodyLaw
    (8931+1+RefinedRoundLoop.roundGuard.size+3*701+1064) := by
  apply RefinedGlobalAssembly.bodyLaw_of_fixed_rounds (M := 8931) (D := 701) (by decide)
  · intro B c n G x hx hG hc hB
    exact RefinedPreparedMean.fixed_prepared_mean hx hG hc hB
  · intro B c n G x hx hG hc hB
    exact RefinedRoundFailure.fixed_prepared_failure hx hG hc hB

/--
---
conclusion: Lax457868.RefinedWelzlOrders.exists_refined_randomized_welzlOrder_program
---
The fixed compiled refined algorithm meets the stated crossing, time and
success-probability bounds.

# Proof strategy

The proof counts the actual finite fair-bit executions. It bounds initial
retry cost and the accepted representative charge, then the chronological
exception-repair loop, retaining every consumed random prefix. The maintained
neighborhood separation supplies the paper's rejection bounds, and bounded
selectors and retries supply the finite failure counts. The active-size
contraction sums the round costs. The checked bounded clock and compiler
transfer give the public word-RAM contract with success probability at least
two thirds, including the complete small-input branch.

# Attribution

The algorithm and refined parameters follow the supplied refined manuscript.
The graph encoding, reconstruction and machine infrastructure reuse the
original Welzl-order submission and the registered word-RAM compiler.
-/
theorem exists_refined_randomized_welzlOrder_program :
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
              (2 * (768 * c ^ 5 *
                (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1) *
                Nat.clog 2 n)) := by
  exact RefinedFinalBridge.main_of_body_law
    (M := 8931+1+RefinedRoundLoop.roundGuard.size+3*701+1064) (by decide) source_law

end Lax457868Proofs.RefinedWelzlOrdersProof
