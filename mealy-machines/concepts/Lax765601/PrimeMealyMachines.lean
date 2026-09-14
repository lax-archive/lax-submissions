import Mathlib.Logic.Function.Defs
import Lax765601.MealyMachine
import Lax765601.CompositionClosure

/-!
---
title: Prime Mealy machines: reversible and flip-flop
type: definition
---
The *prime Mealy machines* are defined in terms of the state transformations of
their letters (Definition A.2.1 of *Transducers*). There are two kinds.

* *Reversible* machines: the state transformation of every letter is a
  permutation of the state space.
* *Flip-flop* machines: the state transformation of every letter is either the
  identity or a constant, all states being mapped to the same one.

A one-state machine is both. The machine outputting $abab\cdots$ on $a^n$ is
reversible; the delay machine, which shifts the input one position to the right,
is a flip-flop. Since composing permutations gives a permutation and composing
constants gives a constant, nothing changes if the definition is phrased for the
state transformations of input strings rather than of letters.

The Krohn–Rhodes theorem (Theorem A.2.2) says that every Mealy machine is a
composition of prime Mealy machines; Theorem A.2.8 characterises the compositions
of flip-flops alone.

# Formalization notes

`Reversible` and `FlipFlop` are properties of a machine. The families that the
composition closure is taken over are families of *functions* (as in
`CompositionClosure`), so a function is a prime if it is computed by some prime
machine with a finite state space: `PrimeMealyFam` collects the reversible and
the flip-flop functions, and `FlipFlopFam` the flip-flop ones alone, for
Theorem A.2.8. Bijectivity is mathlib's `Function.Bijective`.
-/

namespace Lax765601.PrimeMealyMachines

open Lax765601.MealyMachine Lax765601.CompositionClosure

/-- A Mealy machine is reversible if the state transformation of every letter is a
permutation of the state space. -/
def Reversible {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, Function.Bijective (M.letterTrans a)

/-- A Mealy machine is a flip-flop if the state transformation of every letter is
the identity or a constant. -/
def FlipFlop {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, M.letterTrans a = id ∨ ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀

/-- A function is computed by a reversible Mealy machine with a finite state
space. -/
def IsReversibleMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ Reversible M

/-- A function is computed by a flip-flop Mealy machine with a finite state
space. -/
def IsFlipFlopMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ FlipFlop M

/-- The family of prime Mealy machines: the functions computed by a reversible or
by a flip-flop machine. -/
def PrimeMealyFam : Family := fun _ _ f => IsReversibleMealy f ∨ IsFlipFlopMealy f

/-- The family of flip-flop Mealy machines. -/
def FlipFlopFam : Family := fun _ _ f => IsFlipFlopMealy f

end Lax765601.PrimeMealyMachines
