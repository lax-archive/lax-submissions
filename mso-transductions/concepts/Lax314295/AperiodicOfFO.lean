import Lax765601.StateTransformations
import Lax314295.MSOLogic

/-!
---
title: First-order definable languages are aperiodic
type: theorem
---
Every language definable in first-order logic is recognised by an aperiodic
deterministic automaton (Theorem C.4.11 of *Transducers*, the implication from
definable to aperiodic). A first-order sentence of quantifier rank $k$ depends
only on the $k$-type of the string (Lemma C.4.13); the automaton whose states
are the $k$-types, which is finite and aperiodic by Lemma C.4.15, recognises
the language.

# Formalization notes

A deterministic automaton is mathlib's `DFA`; it is aperiodic if its transition
function satisfies the stabilisation condition `TransAperiodic` of
`Lax765601.StateTransformations`. The alphabet is assumed finite.
-/

namespace Lax314295.AperiodicOfFO

open Lax765601.StateTransformations Lax314295.MSOLogic

/-- A first-order definable language is recognised by an aperiodic dfa. -/
axiom exists_aperiodic_dfa_of_foDefinable {A : Type} [Finite A] {L : Language A}
    (hL : FODefinable L) :
    ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L

end Lax314295.AperiodicOfFO
