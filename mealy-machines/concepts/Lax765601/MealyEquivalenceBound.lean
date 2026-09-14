import Mathlib.SetTheory.Cardinal.Finite
import Lax765601.MealyMachine

/-!
---
title: Decidable equivalence of Mealy machines
type: theorem
---
The equivalence problem for Mealy machines — do two given machines compute the
same function? — is decidable (Theorem A.1.2 of *Transducers*). The book reduces
it to the equivalence of regular languages: a letter-to-letter function is
determined by the languages "the last output letter is $b$", one for each output
letter $b$, and each of them is recognised by the automaton underlying the
machine. In the form stated here, two Mealy machines with $n_1$ and $n_2$ states
are equivalent if and only if they agree on all input strings of length at most
$n_1 n_2$ — a finite check, since the alphabet is finite.

# Formalization notes

Decidability is expressed by its mathematical content, the finite check, rather
than by a decision procedure on encodings of machines: the product of the numbers
of states bounds the length of a shortest input on which two inequivalent
machines differ, because a pair of runs that repeats a pair of states can be
shortened by cutting out the loop. `Nat.card Q` is the number of states of a
finite state space. The statement holds over any input alphabet, finite or not;
finiteness of the alphabet is what makes the check a finite one.
-/

namespace Lax765601.MealyEquivalenceBound

open Lax765601.MealyMachine

/-- Two Mealy machines are equivalent if and only if they agree on every input
string of length at most the product of their numbers of states. -/
axiom eval_eq_iff_short {A B Q₁ Q₂ : Type} [Finite Q₁] [Finite Q₂]
    (M : Mealy A B Q₁) (N : Mealy A B Q₂) :
    M.eval = N.eval ↔
      ∀ w : List A, w.length ≤ Nat.card Q₁ * Nat.card Q₂ → M.eval w = N.eval w

end Lax765601.MealyEquivalenceBound
