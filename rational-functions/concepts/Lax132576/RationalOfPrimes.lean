import Lax132576.RationalFunctions
import Lax132576.PrimeRationalFunctions

/-!
---
title: Compositions of prime rational functions are rational
type: theorem
---
Every composition of prime rational functions is rational (Theorem B.2.6 of
*Transducers*, the implication ⇐): each prime is rational — a Mealy machine and
a homomorphism are read directly as automata with output, the separator
function needs one empty-input transition, and a right-to-left Mealy machine is
a bimachine with a trivial prefix automaton — and rational functions are closed
under composition (Theorem B.1.4).

# Formalization notes

The hypothesis is membership in `CompClosure PrimeRationalFam`; both alphabets
are assumed finite, as the bimachine of a right-to-left machine needs.
-/

namespace Lax132576.RationalOfPrimes

open Lax765601.CompositionClosure Lax132576.RationalFunctions Lax132576.PrimeRationalFunctions

/-- A composition of prime rational functions is rational. -/
axiom isRationalFun_of_compClosure_primeRational {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : CompClosure PrimeRationalFam A B f) : IsRationalFun f

end Lax132576.RationalOfPrimes
