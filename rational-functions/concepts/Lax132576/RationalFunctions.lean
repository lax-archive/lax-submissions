import Lax132576.RationalRelations

/-!
---
title: Rational functions
type: definition
---
A *rational function* (Definition B.2.1 of *Transducers*) is the special case
of a rational relation in which each input string is related to exactly one
output string. The definition is semantic: the underlying automaton is
nondeterministic and merely happens to have a unique output for every input,
possibly through several runs; Theorem B.2.3 gives the deterministic model, the
bimachine, that computes exactly these functions. Rational functions inherit
closure under composition and continuity from rational relations, and every
Mealy machine is a rational function.

# Formalization notes

A function is rational if its graph `fun w v => v = f w` is a rational
relation. Since `f` is a total function, this is exactly "a rational relation
in which each input has exactly one output"; partial rational functions do not
occur in the book's statements.
-/

namespace Lax132576.RationalFunctions

open Lax132576.RationalRelations

/-- A string-to-string function is rational if its graph is a rational relation.
-/
def IsRationalFun {A B : Type} (f : List A → List B) : Prop :=
  IsRationalRel (fun w v => v = f w)

end Lax132576.RationalFunctions
