import Lax765601.StateTransformations
import Lax314295.MSOLogic

/-!
---
title: Aperiodic automata recognise first-order definable languages
type: theorem
---
Every language recognised by an aperiodic deterministic automaton is
definable in first-order logic (Theorem C.4.11 of *Transducers*, the
implication from aperiodic to definable). The automaton, read as a Mealy
machine, is a composition of flip-flops by Theorem A.2.8, and the state of a
flip-flop at a position is determined by the last resetting letter before it,
which first-order logic can express; composing the formulas along the
decomposition gives a first-order description of the run.

# Formalization notes

Aperiodicity is `TransAperiodic` on the transition function of a mathlib
`DFA` with a finite state set. The alphabet is assumed finite.
-/

namespace Lax314295.FOOfAperiodic

open Lax765601.StateTransformations Lax314295.MSOLogic

/-- The language of an aperiodic dfa is first-order definable. -/
axiom foDefinable_of_aperiodic_dfa {A σ : Type} [Finite A] [Finite σ] (M : DFA A σ)
    (hM : TransAperiodic M.step) : FODefinable M.accepts

end Lax314295.FOOfAperiodic
