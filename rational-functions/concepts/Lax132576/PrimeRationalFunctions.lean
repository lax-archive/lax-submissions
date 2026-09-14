import Lax765601.PrimeMealyMachines
import Lax132576.StringHomomorphisms

/-!
---
title: The prime rational functions
type: definition
---
The *prime rational functions* of Theorem B.2.6 of *Transducers* are the
following four kinds of functions:

1. the prime Mealy machines, i.e. the reversible and the flip-flop Mealy
   machines;
2. their *right-to-left* variants — Mealy machines that process the input from
   right to left, the initial state being used after the rightmost position;
3. the string homomorphisms;
4. the function $w \mapsto w\#$ which appends a fresh separator symbol to the
   input string.

Theorem B.2.6 says that the rational functions are exactly the compositions of
prime rational functions, the analogue of the Krohn–Rhodes theorem one step up
the transducer ladder.

# Formalization notes

A right-to-left Mealy machine computes `f` exactly when the function
`w ↦ reverse (f (reverse w))` is computed by a Mealy machine, which is how the
second kind is stated. The separator function needs the output alphabet to be
the input alphabet plus one letter; this is expressed by a bijection
`e : Option A ≃ B`, the separator being `e none`. `PrimeRationalFam` is a family
in the sense of `Lax765601.CompositionClosure`, so that "composition of prime
rational functions" is its composition closure.
-/

namespace Lax132576.PrimeRationalFunctions

open Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax132576.StringHomomorphisms

/-- The family of prime rational functions: prime Mealy machines, their
right-to-left variants, string homomorphisms, and the separator function
`w ↦ w #`. -/
def PrimeRationalFam : Family := fun A B f =>
  PrimeMealyFam A B f ∨
  PrimeMealyFam A B (fun w => (f w.reverse).reverse) ∨
  (∃ φ : A → List B, f = homOf φ) ∨
  (∃ e : Option A ≃ B, f = fun w => w.map (fun a => e (some a)) ++ [e none])

end Lax132576.PrimeRationalFunctions
