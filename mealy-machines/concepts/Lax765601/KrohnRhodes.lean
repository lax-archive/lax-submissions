import Lax765601.PrimeMealyMachines

/-!
---
title: The Krohn–Rhodes decomposition theorem
type: theorem
---
Every Mealy machine $f$ admits a decomposition
$$f = f_1 \cdot f_2 \cdots f_n$$
in which each Mealy machine $f_1, \ldots, f_n$ is either reversible or flip-flop
(Theorem A.2.2 of *Transducers*, the Krohn–Rhodes theorem). No uniqueness is
claimed. Since Mealy machines are closed under composition, the class of
functions computed by Mealy machines is exactly the closure under composition of
the prime Mealy machines,
$$\mathrm{Mealy} = (\mathrm{Reversible} \cup \mathrm{Flip\text{-}flop})^*.$$

The proof of the book has two steps: map lifting is compatible with
decompositions into primes (Lemma A.2.4), and the state transformation
transducer of every pre-automaton is a composition of primes (Lemma A.2.5), by an
induction on the number of states and the number of letters whose state
transformation is not a permutation; the output of the machine is then recovered
from the state transformations of the prefixes by a delay machine and a
letter-to-letter homomorphism.

# Formalization notes

The conclusion is membership in the composition closure of the family of prime
Mealy machines, `CompClosure PrimeMealyFam`, with finite intermediate alphabets
built into the closure. Both alphabets are assumed finite, as in the book, where
finiteness of the input alphabet is what the induction on the number of letters
uses. The converse inclusion, that a composition of primes is computed by a
Mealy machine, is closure under composition (Theorem A.1.3) and is not part of
this statement.
-/

namespace Lax765601.KrohnRhodes

open Lax765601.MealyMachine Lax765601.CompositionClosure Lax765601.PrimeMealyMachines

/-- Every function computed by a Mealy machine is a composition of reversible and
flip-flop Mealy machines. -/
axiom compClosure_primeMealy_of_isMealy {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) : CompClosure PrimeMealyFam A B f

end Lax765601.KrohnRhodes
