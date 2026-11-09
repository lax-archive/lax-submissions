import Lax457868Proofs.RefinedPrefixMean
import Lax457868Proofs.RefinedPrefixFailure

/-! Assemble the exact fixed-round source estimates into the whole program's
source law; the small branch and compiler bridge are reused unchanged. -/
namespace Lax457868Proofs.RefinedGlobalAssembly
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedFinalBridge
open Lax457868Proofs.RefinedBodyEstimate
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedPrefixMean
open Lax457868Proofs.RefinedPrefixFailure
open Lax195003.WelzlOrdersNeighborhoodComplexity

lemma bodyLaw_of_fixed_rounds {M D : ℕ}
    (hM : 10 ≤ M+1+RefinedRoundLoop.roundGuard.size+3*D+1064)
    (hmean : ∀ (B c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      Lax11.GraphEncoding.EncodesGraph x n G →
      HasLinearNeighborhoodComplexityWithConstant G c → 2 ≤ c →
      4*(x.length+1) ≤ B →
      FixedPreparedRoundMean (B := B) (c := c) (n := n) (M := M) (D := D)
        (G := G) (x := x))
    (hfailure : ∀ (B c n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      Lax11.GraphEncoding.EncodesGraph x n G →
      HasLinearNeighborhoodComplexityWithConstant G c → 2 ≤ c →
      4*(x.length+1) ≤ B →
      FixedPreparedRoundFailure (B := B) (c := c) (n := n)
        (Fcoef := n*(2*n)+n*(n*n)+1+n) (G := G) (x := x)) :
    BodyLaw (M+1+RefinedRoundLoop.roundGuard.size+3*D+1064) := by
  apply bodyLaw_of_large hM
  intro B c n G hc hn hG x hx hB h768 hlarge σ R hbounded N htape
  let F := large_body_family R hbounded hx hG hc hn hB hlarge htape
  have hlog : 0 < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simp; omega)
  have hreserve : 0 < roundBitReserve c n := by
    unfold roundBitReserve
    positivity
  have hN : n ≤ N := (Nat.le_mul_of_pos_right n hreserve).trans htape
  exact bodyEstimate_of_prefix_and_index_failure hx F hc hlarge hN
    (fun i _ => prefixRoundMeanAt_of_fixed F (hmean B c n G x hx hG hc hB) i)
    (fun i _ => index_failure_le_of_fixed F (hfailure B c n G x hx hG hc hB) hN i)

end Lax457868Proofs.RefinedGlobalAssembly
