import Mathlib.Data.List.TFAE
import Lax132576.RationalFunctions
import Lax132576.Bimachines

/-!
---
title: Eilenberg's theorem: rational functions, unambiguous automata and bimachines
type: theorem
---
For a string-to-string function the following are equivalent (Theorem B.2.3 of
*Transducers*, Eilenberg): (1) it is a rational relation which happens to be
functional; (2) it is computed by an unambiguous nondeterministic automaton
with output; (3) it is computed by a bimachine. The book proves
(3) ⇒ (1) ⇒ (2) ⇒ (3); here the three implications with content are separate
statements — `RationalOfBimachine`, `UnambiguousOfRational` and
`BimachineOfRational` — and this statement is their conjunction, the
implication (2) ⇒ (1) being immediate since an unambiguous automaton is an
automaton.

# Formalization notes

`List.TFAE` is mathlib's "the following are equivalent" for a list of
propositions. Both alphabets are assumed finite.
-/

namespace Lax132576.RationalUnambiguousBimachine

open Lax132576.RationalRelations Lax132576.RationalFunctions Lax132576.Bimachines

/-- Eilenberg's theorem: a function is rational, computed by an unambiguous
automaton with output, or computed by a bimachine, equivalently. -/
axiom tfae_rational_unambiguous_bimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    [IsRationalFun f, IsUnambiguousRel (fun w v => v = f w), IsBimachine f].TFAE

end Lax132576.RationalUnambiguousBimachine
