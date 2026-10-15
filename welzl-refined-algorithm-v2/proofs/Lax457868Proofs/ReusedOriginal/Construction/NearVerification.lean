/-
Reused source module: Lax235315Proofs.Construction.NearVerification.
Source: https://github.com/lax-archive/lax-submissions/tree/33f2eca4379b6ff944489c7c59ac1990c286c21b/welzl-order-construction/proofs
License: Apache-2.0.
The mathematical code is unchanged except for namespace transport.
-/
import Lax457868Proofs.ReusedOriginal.Construction.GraphSampling
import Mathlib.Tactic

/-!
The arithmetic identity used by the program's batched near-twin verifier.
-/

namespace Lax457868Proofs.ReusedOriginal.Construction.NearVerification

open scoped symmDiff
open Finset
open Lax457868Proofs.ReusedOriginal.Construction.GraphSampling
open Lax457868Proofs.ReusedOriginal.Construction.Sampling

lemma card_finSymmDiff_eq {α : Type*} [DecidableEq α]
    (X Y : Finset α) :
    (finSymmDiff X Y).card = X.card + Y.card - 2 * (X ∩ Y).card := by
  have hIX : (X ∩ Y).card ≤ X.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hIY : (X ∩ Y).card ≤ Y.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hdisj : Disjoint (X \ Y) (Y \ X) := by
    rw [Finset.disjoint_left]
    aesop
  rw [finSymmDiff, Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff, Finset.card_sdiff]
  rw [Finset.inter_comm Y X]
  omega

/-- The value accumulated by `verifyNear` is precisely the cardinality of
the symmetric difference checked in Figure 1. -/
lemma neighborhood_symmDiff_ncard_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (b r : Fin n) :
    ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
      (G.neighborSet r ∩ (A : Set (Fin n)))).ncard =
      (traceFinset G A b).card + (traceFinset G A r).card -
        2 * (traceFinset G A b ∩ traceFinset G A r).card := by
  rw [← card_finSymmDiff_trace G A b r, card_finSymmDiff_eq]

end Lax457868Proofs.ReusedOriginal.Construction.NearVerification
