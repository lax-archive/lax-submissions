import Lax132576.RationalFunctions
import Lax132576.PrimeRationalFunctions

/-!
---
title: Rational functions decompose into prime rational functions
type: theorem
---
Every rational function is a composition of prime rational functions — prime
Mealy machines, their right-to-left variants, string homomorphisms and the
separator function $w \mapsto w\#$ (Theorem B.2.6 of *Transducers*, the
implication ⇒). By Eilenberg's theorem the function is computed by a
bimachine; one appends the separator, labels every position with the state of
the prefix automaton (a Mealy machine, decomposed by the Krohn–Rhodes theorem)
and with the state of the suffix automaton (a right-to-left Mealy machine, the
state being stored one position to the right, which is what the separator is
for), and a homomorphism produces the output of every gap.

# Formalization notes

The conclusion is membership in `CompClosure PrimeRationalFam`. Both alphabets
are assumed finite, as the Krohn–Rhodes decomposition of the two automata
needs.
-/

namespace Lax132576.PrimesOfRational

open Lax765601.CompositionClosure Lax132576.RationalFunctions Lax132576.PrimeRationalFunctions

/-- A rational function is a composition of prime rational functions. -/
axiom compClosure_primeRational_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : CompClosure PrimeRationalFam A B f

end Lax132576.PrimesOfRational
