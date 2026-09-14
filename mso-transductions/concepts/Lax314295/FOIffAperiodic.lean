import Lax765601.StateTransformations
import Lax314295.MSOLogic

/-!
---
title: First-order definable languages are exactly the aperiodic ones
type: theorem
---
A language is definable in first-order logic if and only if it is recognised
by an aperiodic deterministic automaton (Theorem C.4.11 of *Transducers*,
Schützenberger, McNaughton and Papert). The two implications are the separate
statements `AperiodicOfFO` and `FOOfAperiodic`; this statement is their
conjunction.

# Formalization notes

The alphabet is assumed finite.
-/

namespace Lax314295.FOIffAperiodic

open Lax765601.StateTransformations Lax314295.MSOLogic

/-- A language is first-order definable if and only if some aperiodic dfa
recognises it. -/
axiom foDefinable_iff_aperiodic_dfa {A : Type} [Finite A] (L : Language A) :
    FODefinable L ↔
      ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L

end Lax314295.FOIffAperiodic
