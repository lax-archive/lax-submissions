import Mathlib.Data.Finite.Defs

/-!
---
title: Sequential transducers
type: definition
---
A *sequential transducer* (Section B.4.2 of *Transducers*) is defined like a
Mealy machine, except that its transition function has type
$$Q \times A \to Q \times B^*,$$
so that a transition may produce an output string of any length, including the
empty one, instead of exactly one letter. The functions computed by sequential
transducers, the *sequential functions*, lie strictly between the Mealy
machines and the rational functions; Theorem B.4.6 characterises them without
reference to a machine.

# Formalization notes

`run` concatenates the output strings of the transitions taken from a given
state, and `eval` is the run from the initial state; `IsSequential f` asks for a
finite state space.
-/

namespace Lax132576.SequentialTransducers

/-- A sequential transducer: a Mealy machine whose transitions produce output
strings of variable length. -/
structure Sequential (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a target state and an output string. -/
  step : Q → A → Q × List B

namespace Sequential

variable {A B Q : Type}

/-- The output produced from a given state on an input string. -/
def run (T : Sequential A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (T.step q a).2 ++ T.run (T.step q a).1 w

/-- The semantics of a sequential transducer. -/
def eval (T : Sequential A B Q) (w : List A) : List B := T.run T.init w

/-- The transition function of the underlying automaton. -/
def transFun (T : Sequential A B Q) : Q → A → Q := fun q a => (T.step q a).1

end Sequential

/-- A function computed by a sequential transducer with a finite state space. -/
def IsSequential {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Sequential A B Q), T.eval = f

end Lax132576.SequentialTransducers
