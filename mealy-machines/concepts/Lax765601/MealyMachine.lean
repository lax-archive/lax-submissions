import Mathlib.Data.Finite.Defs

/-!
---
title: Mealy machines
type: definition
---
A *Mealy machine* is a deterministic finite automaton whose transitions are
labelled by output letters, and which has no accepting states, since its purpose
is to produce an output string rather than to accept or reject. Formally
(Definition A.1.1 of *Transducers*), it consists of an input alphabet $A$, an
output alphabet $B$, a state space $Q$, an initial state $q_0 \in Q$ and a
transition function
$$\delta : Q \times A \to Q \times B.$$
Its semantics is the function $f : A^* \to B^*$ obtained by running the
underlying automaton on the input string and labelling each position by the
output letter of the corresponding transition; it is a *letter-to-letter*
function, the output having the same length as the input. A function is
*computed by a Mealy machine* if it is the semantics of a Mealy machine with a
finite state space.

The *state transformation* of an input letter $a$ is the map $Q \to Q$ describing
how reading $a$ updates the state, the output being ignored; the underlying
*pre-automaton* of the machine is the family of these maps, i.e. a deterministic
automaton without initial and accepting states (Section A.2).

# Formalization notes

`Mealy A B Q` carries the initial state and the transition function; the three
alphabets are the type parameters. Finiteness of the state space is not part of
the structure — it is where it belongs, in `IsMealy`, which asks for *some*
finite state space `Q` and some machine over it. Alphabets are arbitrary types;
the finiteness the book assumes globally is a hypothesis of the statements that
need it.

`run` is the output produced from a given state, defined by recursion on the
input string, and `eval` is the run from the initial state. Nothing else is
derivable from these and is omitted; the dfa obtained by forgetting outputs is
`transFun`.
-/

namespace Lax765601.MealyMachine

/-- A Mealy machine with input alphabet `A`, output alphabet `B` and state space
`Q`: an initial state and a transition function `Q × A → Q × B`. -/
structure Mealy (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a source state and an input letter determine a
  target state and an output letter. -/
  step : Q → A → Q × B

namespace Mealy

variable {A B Q : Type}

/-- The output produced by the machine on an input string, when started in a
given state. -/
def run (M : Mealy A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (M.step q a).2 :: M.run (M.step q a).1 w

/-- The semantics of a Mealy machine: the output produced from the initial state.
-/
def eval (M : Mealy A B Q) (w : List A) : List B := M.run M.init w

/-- The state transformation of an input letter: how reading the letter updates
the state. -/
def letterTrans (M : Mealy A B Q) (a : A) : Q → Q := fun q => (M.step q a).1

/-- The underlying pre-automaton: the transition function with the output letters
forgotten. -/
def transFun (M : Mealy A B Q) : Q → A → Q := fun q a => (M.step q a).1

end Mealy

/-- A string-to-string function is computed by a Mealy machine if it is the
semantics of a Mealy machine with a finite state space. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

end Lax765601.MealyMachine
