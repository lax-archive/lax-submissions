import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
---
title: Streaming string transducers
type: definition
---
A *streaming string transducer* (Definition C.3.1 of *Transducers*) processes
its input in a single left-to-right pass, storing intermediate results in
finitely many *registers* that hold strings over the output alphabet. It has a
finite set of states with an initial state, a finite set of registers, all
initially empty, and a transition function that on a state and an input letter
gives a new state and a *register update*: for every register, a string over
the output alphabet and the register names, which is evaluated by substituting
the current contents of the registers. Updates are *copyless*: each register
name occurs at most once across all the strings of an update, so that no
register content is ever duplicated. After the whole input has been read, a
final output string over the output alphabet and the register names, chosen by
the final state, is evaluated in the same way. Streaming string transducers
compute exactly the regular functions (Theorem C.3.2).

# Formalization notes

A string over the output alphabet and the register names is a `List (X ⊕ B)`;
`subst η s` substitutes the contents `η` of the registers into it. `Copyless`
counts the register occurrences over all registers, which needs the register
set to be a `Fintype` (for the enumeration), whereas the state space is only
required to be finite in `IsSST`. The copyless restriction is part of the
structure, as in the definition.
-/

namespace Lax916827.StreamingStringTransducers

/-- A register update is copyless if each register name occurs at most once in the
concatenation of the strings assigned to the registers. -/
def Copyless {X B : Type} [Fintype X] (u : X → List (X ⊕ B)) : Prop :=
  ((Finset.univ.toList.map u).flatten.filterMap
      (fun z => match z with | Sum.inl x => some x | Sum.inr _ => none)).Nodup

/-- A streaming string transducer with states `Q` and registers `X`. -/
structure SST (A B Q X : Type) [Fintype X] where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a new state and a register update. -/
  step : Q → A → Q × (X → List (X ⊕ B))
  /-- Every register update is copyless. -/
  step_copyless : ∀ q a, Copyless (step q a).2
  /-- The final output string, chosen by the final state. -/
  final : Q → List (X ⊕ B)

namespace SST

variable {A B Q X : Type} [Fintype X]

/-- Substituting the contents of the registers into a string over `X + B`. -/
def subst (η : X → List B) (s : List (X ⊕ B)) : List B :=
  (s.map (fun z => match z with | Sum.inl x => η x | Sum.inr b => [b])).flatten

/-- Reading one input letter: the new state and the new register contents. -/
def stepConfig (T : SST A B Q X) (c : Q × (X → List B)) (a : A) : Q × (X → List B) :=
  ((T.step c.1 a).1, fun x => subst c.2 ((T.step c.1 a).2 x))

/-- The state and register contents after reading an input string, starting from
the initial state with empty registers. -/
def runConfig (T : SST A B Q X) (w : List A) : Q × (X → List B) :=
  w.foldl T.stepConfig (T.init, fun _ => [])

/-- The semantics: the final output string of the last state, with the final
register contents substituted. -/
def eval (T : SST A B Q X) (w : List A) : List B :=
  subst (T.runConfig w).2 (T.final (T.runConfig w).1)

end SST

/-- A function computed by a streaming string transducer with finite state space
and finitely many registers. -/
def IsSST {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q X : Type) (_ : Finite Q) (instX : Fintype X) (T : @SST A B Q X instX), T.eval = f

end Lax916827.StreamingStringTransducers
