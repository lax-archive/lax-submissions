import Mathlib.Data.Set.Finite.Basic
import Lax765601.MealyMachine
import Lax765601.ElementaryProperties
import Lax765601.Derivatives

/-!
---
title: Myhill–Nerode for Mealy machines
type: theorem
---
A string-to-string function is computed by a Mealy machine if and only if (1) it
has finitely many derivatives, (2) it is letter-to-letter, and (3) its $n$-th
output letter depends only on the first $n$ input letters (Lemma A.2.10 of
*Transducers*). From a machine, the derivative $f(w\_)$ is determined by the
state reached after reading $w$, so there are finitely many. Conversely, the
*minimal machine* of $f$ has the derivatives as its states, the derivative of the
empty string as initial state, and the transitions
$$f(w\_) \xrightarrow{a\,/\,\text{last letter of } f(wa)} f(wa\_),$$
which are well defined because the output letter and the target depend only on
the derivative $f(w\_)$ and not on $w$.

# Formalization notes

Condition (3) is `PrefixDetermined f`, "the first `n` output letters depend only
on the first `n` input letters", which for a letter-to-letter function says
exactly that the `n`-th output letter depends only on the first `n` input
letters. The set of derivatives is the range of `deriv f`, and its finiteness is
mathlib's `Set.Finite`. No finiteness of the alphabets is assumed: the states of
the minimal machine are the derivatives, whatever the alphabets.
-/

namespace Lax765601.MealyDerivatives

open Lax765601.MealyMachine Lax765601.ElementaryProperties Lax765601.Derivatives

/-- A function is computed by a Mealy machine if and only if it has finitely many
derivatives, is letter-to-letter, and its first `n` output letters depend only on
its first `n` input letters. -/
axiom isMealy_iff {A B : Type} (f : List A → List B) :
    IsMealy f ↔ (Set.range (deriv f)).Finite ∧ LengthPreserving f ∧ PrefixDetermined f

end Lax765601.MealyDerivatives
