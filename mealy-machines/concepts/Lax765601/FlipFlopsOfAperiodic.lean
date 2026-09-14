import Lax765601.PrimeMealyMachines
import Lax765601.Aperiodicity

/-!
---
title: Aperiodic Mealy machines are compositions of flip-flops
type: theorem
---
Every aperiodic function computed by a Mealy machine is computed by a
composition of flip-flop Mealy machines: the implication "aperiodic
$\Rightarrow$ composition of flip-flops" of Theorem A.2.8 of *Transducers*, the
hard half. By Lemma A.2.11 the function is computed by a machine whose state
transformations satisfy the stabilisation condition (*); the proof of the
Krohn–Rhodes theorem is then run for this machine, and every machine arising in
the induction inherits (*), since it only uses state transformations of the
original one, so that no reversible machine with more than one state ever
appears and every prime in the decomposition is a flip-flop.

# Formalization notes

The two alphabets are assumed finite, as for the Krohn–Rhodes theorem, whose
construction this statement repeats inside the class of flip-flops. The
conclusion is membership in `CompClosure FlipFlopFam`.
-/

namespace Lax765601.FlipFlopsOfAperiodic

open Lax765601.MealyMachine Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax765601.Aperiodicity

/-- An aperiodic function computed by a Mealy machine is a composition of flip-flop
Mealy machines. -/
axiom compClosure_flipFlop_of_aperiodic {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) (ha : Aperiodic f) :
    CompClosure FlipFlopFam A B f

end Lax765601.FlipFlopsOfAperiodic
