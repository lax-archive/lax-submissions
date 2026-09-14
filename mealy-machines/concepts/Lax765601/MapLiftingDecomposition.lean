import Lax765601.PrimeMealyMachines
import Lax765601.MapLifting

/-!
---
title: Map lifting preserves decompositions into primes
type: theorem
---
If a Mealy machine decomposes into prime Mealy machines, then so does its map
lifting (Lemma A.2.4 of *Transducers*). Since map lifting commutes with
composition, it suffices to lift a single prime. A flip-flop is lifted by
resetting its state at every separator. A reversible machine needs more care,
because resetting would break reversibility: the book computes, by a reversible
machine, the state transformation $\gamma_w$ of every prefix in the variant
where the separator does nothing, stores the value at the last separator by a
flip-flop delay machine, and recovers the state transformation of the current
block by the cancellation law $\delta_w = \gamma_v^{-1} \cdot \gamma_{vw}$,
all of which is a one-state machine's work.

# Formalization notes

Finiteness of the input alphabet is assumed; the finiteness of the output
alphabet, which the book assumes globally, is not needed here and is dropped.
The map lifting is `MapLifting.mapLift`, over the alphabets `Option A` and
`Option B`.
-/

namespace Lax765601.MapLiftingDecomposition

open Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax765601.MapLifting

/-- The map lifting of a composition of prime Mealy machines is a composition of
prime Mealy machines. -/
axiom compClosure_mapLift {A B : Type} [Finite A] {f : List A → List B}
    (hf : CompClosure PrimeMealyFam A B f) :
    CompClosure PrimeMealyFam (Option A) (Option B) (mapLift f)

end Lax765601.MapLiftingDecomposition
