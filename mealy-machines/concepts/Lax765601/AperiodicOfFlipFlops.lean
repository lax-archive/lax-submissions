import Lax765601.PrimeMealyMachines
import Lax765601.Aperiodicity

/-!
---
title: Compositions of flip-flop machines are aperiodic
type: theorem
---
Every composition of flip-flop Mealy machines computes an aperiodic function:
the implication "composition of flip-flops $\Rightarrow$ aperiodic" of Theorem
A.2.8 of *Transducers*. A single flip-flop is aperiodic, because the last letter
of $f(u v^n w)$ depends only on the last letter read and on the last letter of
$u v w$ whose state transformation is a constant, neither of which depends on
$n$; and aperiodicity is preserved by composition, by the pumping form of
aperiodicity (Claim A.2.9), in which the shifts $k$ of the two functions add up.

# Formalization notes

The hypothesis is membership in the composition closure `CompClosure FlipFlopFam`
of the family of flip-flop machines. No finiteness of the alphabets is needed:
every member of the closure is a Mealy function, and the argument only uses its
state space.
-/

namespace Lax765601.AperiodicOfFlipFlops

open Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax765601.Aperiodicity

/-- A composition of flip-flop Mealy machines is aperiodic. -/
axiom aperiodic_of_compClosure_flipFlop {A B : Type} {f : List A → List B}
    (hf : CompClosure FlipFlopFam A B f) : Aperiodic f

end Lax765601.AperiodicOfFlipFlops
