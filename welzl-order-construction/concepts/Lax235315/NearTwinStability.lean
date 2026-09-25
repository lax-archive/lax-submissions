import Lax235315.SequenceCrossings

/-!
---
title: Crossing counts are stable under membership changes
type: lemma
---
If two membership sequences of equal length differ at k positions, the first
crossing count is at most the second plus 2k. Interchanging the sequences
gives the bound in the other direction. This is the local estimate behind
Lemma 2.2 of Dreier--Kuske.

# Formalization notes

No randomness or shatter-function bound is needed. Each changed position has
at most two incident consecutive pairs. For a list containing each vertex
once, Hamming distance is the size of the symmetric difference of the sets
on the listed vertices; that representation bridge is a separate obligation.
-/

namespace Lax235315.NearTwinStability
open Lax235315.SequenceCrossings

/-- Changing k membership positions increases the crossing count by at most 2k. -/
axiom crossings_le_add_twice_hamming (xs ys : List Bool)
    (h : xs.length = ys.length) :
    crossings xs ≤ crossings ys + 2 * hamming xs ys

end Lax235315.NearTwinStability
