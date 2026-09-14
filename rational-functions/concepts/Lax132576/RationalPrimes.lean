import Lax132576.RationalFunctions
import Lax132576.PrimeRationalFunctions

/-!
---
title: The rational functions are the compositions of prime rational functions
type: theorem
---
A string-to-string function is rational if and only if it is a composition of
prime rational functions: prime Mealy machines, their right-to-left variants,
string homomorphisms and the separator function $w \mapsto w\#$ (Theorem B.2.6
of *Transducers*). This is the Krohn–Rhodes theorem one step up the transducer
ladder. The two implications are the separate statements `PrimesOfRational` and
`RationalOfPrimes`; this statement is their conjunction.

# Formalization notes

Both alphabets are assumed finite.
-/

namespace Lax132576.RationalPrimes

open Lax765601.CompositionClosure Lax132576.RationalFunctions Lax132576.PrimeRationalFunctions

/-- A function is rational if and only if it is a composition of prime rational
functions. -/
axiom isRationalFun_iff_compClosure_primeRational {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ CompClosure PrimeRationalFam A B f

end Lax132576.RationalPrimes
