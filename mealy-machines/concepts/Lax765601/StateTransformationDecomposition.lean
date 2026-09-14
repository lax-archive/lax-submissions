import Lax765601.PrimeMealyMachines
import Lax765601.StateTransformations

/-!
---
title: The state transformation transducer is a composition of primes
type: theorem
---
For every pre-automaton, its state transformation transducer — the Mealy
machine whose $n$-th output letter is the state transformation of the first $n$
input letters — is a composition of prime Mealy machines (Lemma A.2.5 of
*Transducers*, the main lemma in the proof of the Krohn–Rhodes theorem).

The book proves it by induction on the number of states and, for a tie, on the
number of letters whose state transformation is not a permutation. A
pre-automaton all of whose letters are permutations is reversible as it stands.
Otherwise one fixes a letter $a$ whose state transformation has a proper image
$P \subset Q$, decomposes the input into its first $a$-block, the middle
$a$-blocks and the $a$-free suffix, and computes the three state
transformations in five stages: the map lifting of the induction hypothesis for
the alphabet without $a$ (Lemma A.2.4) handles the $a$-free pieces, two
flip-flops distribute the state transformations of the blocks, the induction
hypothesis for the smaller state space $P$ handles the middle part, and a
letter-to-letter homomorphism assembles the result.

# Formalization notes

The pre-automaton is its transition function `δ : Q → A → Q`, and the transducer
is `StateTransformations.stateTransTransducer δ`, of type
`Mealy A (Q → Q) (Q → Q)`; the conclusion is membership of its semantics in the
composition closure of the primes. Both the alphabet and the state space are
assumed finite, the two induction parameters. The formal induction keeps the
input alphabet fixed and makes the letter `a` act as the identity instead of
removing it, which measures the second parameter by the number of
non-permutation letters.
-/

namespace Lax765601.StateTransformationDecomposition

open Lax765601.MealyMachine Lax765601.CompositionClosure Lax765601.PrimeMealyMachines
  Lax765601.StateTransformations

/-- The state transformation transducer of a finite pre-automaton over a finite
alphabet is a composition of prime Mealy machines. -/
axiom compClosure_stateTransTransducer {A Q : Type} [Finite A] [Finite Q] (δ : Q → A → Q) :
    CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer δ).eval

end Lax765601.StateTransformationDecomposition
