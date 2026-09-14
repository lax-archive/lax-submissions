import Lax132576.RationalFunctions

/-!
---
title: Rational functions are computed by unambiguous automata
type: theorem
---
Every rational function is computed by an unambiguous nondeterministic
automaton with output, one with exactly one accepting run per input string:
the implication (1) ⇒ (2) of Theorem B.2.3 of *Transducers* (Eilenberg). It is
a consequence of the uniformisation lemma (Lemma B.2.5): the graph of a
function is a total rational relation, so it contains an unambiguous rational
relation, which must be the graph itself.

# Formalization notes

The conclusion is `IsUnambiguousRel` for the graph `fun w v => v = f w`. Both
alphabets are assumed finite, as the uniformisation construction needs.
-/

namespace Lax132576.UnambiguousOfRational

open Lax132576.RationalRelations Lax132576.RationalFunctions

/-- The graph of a rational function is computed by an unambiguous automaton with
output. -/
axiom isUnambiguousRel_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsUnambiguousRel (fun w v => v = f w)

end Lax132576.UnambiguousOfRational
