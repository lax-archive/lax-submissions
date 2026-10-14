import Lax195003.WelzlOrders
import Mathlib.Data.Set.Card

/-!
Internal contract for a refined sample of a set system on a finite ground set.
The randomized procedure and its probability analysis remain in the proof
package.
-/

namespace Lax457868Proofs.RefinedSampleSpec

open Lax195003.WelzlOrders

/-- `W` is a refined sample of `𝓕` inside `A`, with size threshold `m` and
disagreement threshold `k`. -/
def IsRefinedSample {α : Type*} (𝓕 : SetSystem α) (A W : Set α)
    (m k : ℕ) : Prop :=
  A.Finite ∧
  (∀ X ∈ 𝓕, X ⊆ A) ∧
  W ⊆ A ∧
  W.ncard ≤ m ∧
  ∀ X ∈ 𝓕, ∀ Y ∈ 𝓕, X ∩ W = Y ∩ W →
    ((X \ Y) ∪ (Y \ X)).ncard ≤ k

end Lax457868Proofs.RefinedSampleSpec
