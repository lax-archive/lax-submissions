import Lax765601.MealyMachine
import Lax765601.StateTransformations
import Lax765601.Aperiodicity

/-!
---
title: Aperiodicity through the state transformations of the minimal machine
type: theorem
---
A function computed by a Mealy machine is aperiodic if and only if its minimal
Mealy machine satisfies the stabilisation condition (*): for every state
transformation $\delta : Q \to Q$ that arises from some input string, the
sequence $\delta^1, \delta^2, \ldots$ eventually stabilises on a single state
transformation (Lemma A.2.11 of *Transducers*). If any machine computing $f$
satisfies (*), then $f$ is aperiodic; conversely, if the minimal machine violates
(*) for the state transformation of a string $v$, then two powers $\delta^i \neq
\delta^j$ recur infinitely often, and minimality yields strings $u, w$ for which
the last letters of $f(u v^i w)$ and $f(u v^j w)$ differ, contradicting
aperiodicity. This lemma is what the book's decision procedure for aperiodicity
rests on.

# Formalization notes

The minimal machine is not constructed. Condition (*) is inherited by the
minimal machine from any machine that has it, so "the minimal machine of $f$
satisfies (*)" is equivalent to "some Mealy machine computing $f$ satisfies (*)",
which is the form stated: `TransAperiodic M.transFun` is condition (*) for the
pre-automaton underlying `M`. The book's finiteness assumptions on the alphabets
are not used and are dropped.
-/

namespace Lax765601.AperiodicityMinimalMachine

open Lax765601.MealyMachine Lax765601.StateTransformations Lax765601.Aperiodicity

/-- A Mealy function is aperiodic if and only if some Mealy machine computing it
satisfies the stabilisation condition (*) on its state transformations. -/
axiom aperiodic_iff_transAperiodic {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ TransAperiodic M.transFun

end Lax765601.AperiodicityMinimalMachine
