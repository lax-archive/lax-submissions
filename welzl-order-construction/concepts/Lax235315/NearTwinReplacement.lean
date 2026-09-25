import Lax195003.WelzlOrders
import Mathlib.Data.Set.SymmDiff

/-!
---
title: Replacing near twins in a set system
type: lemma
---
Suppose every set in a finite set system differs from some representative
set on at most k vertices. Every order with crossing number at most m for
the representatives has crossing number at most m+2k for the original
family. This is Lemma 2.2 of Dreier--Kuske.

# Formalization notes

The claim uses the exact crossing number of Lax195003, including its
permutation convention and natural supremum. No sampling or graph hypothesis
is needed. The representative relation permits different original sets to
share the same representative.
-/

namespace Lax235315.NearTwinReplacement
open scoped symmDiff
open Lax195003.WelzlOrders

/-- Near-twin representatives incur at most two crossings per changed vertex. -/
axiom crossingNumber_le_add_two_mul {n k m : ℕ}
    {F R : SetSystem (Fin n)} {π : Equiv.Perm (Fin n)}
    (hrep : ∀ X ∈ F, ∃ Y ∈ R, (X ∆ Y).ncard ≤ k)
    (hπ : crossingNumber R π ≤ m) :
    crossingNumber F π ≤ m + 2 * k

end Lax235315.NearTwinReplacement
