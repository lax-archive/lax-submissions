import Lax765601.PrimeMealyMachines
import Lax765601.Aperiodicity

/-!
---
title: Aperiodic Mealy machines are exactly the compositions of flip-flops
type: theorem
---
A function computed by a Mealy machine is aperiodic if and only if it is
computed by a composition of flip-flop Mealy machines (Theorem A.2.8 of
*Transducers*). This answers the question what the class
$(\mathrm{Flip\text{-}flop})^*$ of compositions of one kind of prime is; for the
other kind, $(\mathrm{Reversible})^*$ is the class of reversible machines
(Lemma A.2.6).

The two implications are separate results, each with its own proof:
`AperiodicOfFlipFlops` (a composition of flip-flops is aperiodic) and
`FlipFlopsOfAperiodic` (an aperiodic Mealy function decomposes into flip-flops);
this statement is their conjunction.

# Formalization notes

The theorem in the book ends with the sentence "moreover, this property can be
decided, given a Mealy machine that computes $f$". That sentence is *not*
formalised: the characterisation the book's decision procedure rests on, Lemma
A.2.11, is, but the enumeration of the state transformations arising from input
strings that turns it into an algorithm is not written down. Both alphabets are
assumed finite.
-/

namespace Lax765601.AperiodicMealy

open Lax765601.MealyMachine Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax765601.Aperiodicity

/-- A function computed by a Mealy machine is aperiodic if and only if it is a
composition of flip-flop Mealy machines. -/
axiom aperiodic_iff_compClosure_flipFlop {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔ CompClosure FlipFlopFam A B f

end Lax765601.AperiodicMealy
