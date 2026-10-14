import Lax195003.WelzlOrders
import Mathlib.Data.Set.Card

/-!
---
title: Refined sample
type: definition
---
A refined sample of a set system on a finite ground set is a subset of the
ground set of a prescribed maximum size such that any two members of the
system with the same trace on the sample differ on at most a prescribed
number of ground-set elements.

# Formalization notes

The size and disagreement thresholds are parameters. This separates the
mathematical output contract from the randomized procedure that produces a
sample; the procedure and its probability analysis remain in the proof
package.
-/

namespace Lax457868.RefinedSample

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

end Lax457868.RefinedSample
