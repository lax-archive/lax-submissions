import Lax765601.Continuity
import Lax765601.ElementaryProperties
import Lax765601.MealyMachine

/-!
---
title: Machine-independent characterisation of Mealy machines
type: theorem
---
A function $f : A^* \to B^*$ is computed by a Mealy machine if and only if it is
(a) continuous, (b) prefix preserving, and (c) length preserving (Theorem
B.4.1 of *Transducers*). A Mealy machine clearly has the three properties;
conversely, for every output letter $b$ the language of inputs whose output
ends with $b$ is regular by continuity, each input position contributes exactly
one output letter by prefix and length preservation, and the product of the
automata of these languages is the state space of a Mealy machine computing
$f$.

# Formalization notes

Both alphabets are assumed finite: the product over the output letters is a
finite product. The three properties are those of `Lax765601.Continuity` and
`Lax765601.ElementaryProperties`.
-/

namespace Lax132576.MealyMachineIndependent

open Lax765601.Continuity Lax765601.ElementaryProperties Lax765601.MealyMachine

/-- A function is computed by a Mealy machine if and only if it is continuous,
prefix preserving and length preserving. -/
axiom isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f

end Lax132576.MealyMachineIndependent
