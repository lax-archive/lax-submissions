import Lax765601.MealyMachine
import Lax765601.ElementaryProperties
import Lax132576.RationalFunctions

/-!
---
title: Which rational functions are Mealy machines
type: theorem
---
A rational function $f : A^* \to B^*$ is computed by a Mealy machine if and only
if it is letter-to-letter — the output has the length of the input — and
deterministic: input strings that agree on their first $n$ letters have outputs
that agree on their first $n$ letters (Theorem B.2.7 of *Transducers*). Mealy
machines are the special case of the rational functions that the theorem
pins down; the proof goes through the machine-independent characterisation of
Theorem B.4.1, since a rational function is continuous.

# Formalization notes

"Letter-to-letter" is `LengthPreserving` and "deterministic" is
`PrefixDetermined` of `Lax765601.ElementaryProperties`. Both alphabets are
assumed finite, as Theorem B.4.1 needs.
-/

namespace Lax132576.RationalMealyCharacterisation

open Lax765601.MealyMachine Lax765601.ElementaryProperties Lax132576.RationalFunctions

/-- A rational function is computed by a Mealy machine if and only if it is
letter-to-letter and prefix determined. -/
axiom isMealy_iff_of_isRationalFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsMealy f ↔ LengthPreserving f ∧ PrefixDetermined f

end Lax132576.RationalMealyCharacterisation
