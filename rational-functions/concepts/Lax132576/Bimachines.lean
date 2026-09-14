import Lax765601.StateTransformations

/-!
---
title: Bimachines
type: definition
---
A *bimachine* (Definition B.2.2 of *Transducers*) is a deterministic model for
the rational functions. It consists of input and output alphabets $A$ and $B$,
two deterministic automata over $A$ without accepting states — the *prefix*
automaton and the *suffix* automaton — and an output function
$$(\text{states of the prefix automaton}) \times (\text{states of the suffix automaton}) \to B^*.$$
On an input $a_1 \cdots a_n$ it considers, for every $i \in \{0, \ldots, n\}$,
the factorisation into the prefix $a_1 \cdots a_i$ and the suffix
$a_{i+1} \cdots a_n$, runs the prefix automaton on the prefix and the suffix
automaton on the *reverse* of the suffix, applies the output function to the
resulting pair of states, and concatenates the $n + 1$ pieces in increasing
order of $i$. Bimachines compute exactly the rational functions (Theorem
B.2.3). A bimachine is *aperiodic* if both its automata are aperiodic, i.e.
satisfy the stabilisation condition on state transformations; aperiodic
bimachines compute exactly the first-order relabellings (Theorem C.4.16).

# Formalization notes

Each automaton is an initial state and a transition function; the state
transformation of a string is `strTrans` of `Lax765601.StateTransformations`,
and reading the suffix in reverse is `strTrans M.suffixStep (w.drop i).reverse`.
`IsBimachine f` asks for finite state spaces of both automata.
-/

namespace Lax132576.Bimachines

open Lax765601.StateTransformations

/-- A bimachine: a deterministic prefix automaton, a deterministic suffix automaton
(run on the reverse of the suffix) and an output function on pairs of states. -/
structure Bimachine (A B P S : Type) where
  /-- Initial state of the prefix automaton. -/
  prefixInit : P
  /-- Transition function of the prefix automaton. -/
  prefixStep : P → A → P
  /-- Initial state of the suffix automaton. -/
  suffixInit : S
  /-- Transition function of the suffix automaton. -/
  suffixStep : S → A → S
  /-- The output function. -/
  out : P → S → List B

namespace Bimachine

variable {A B P S : Type}

/-- The semantics of a bimachine: for every gap `i` of the input, the prefix
automaton is run on the first `i` letters and the suffix automaton on the reverse
of the rest, and the pieces of output are concatenated. -/
def eval (M : Bimachine A B P S) (w : List A) : List B :=
  ((List.range (w.length + 1)).map (fun i =>
    M.out (strTrans M.prefixStep (w.take i) M.prefixInit)
          (strTrans M.suffixStep (w.drop i).reverse M.suffixInit))).flatten

end Bimachine

/-- A function computed by a bimachine with finite state spaces. -/
def IsBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S), M.eval = f

/-- A function computed by an aperiodic bimachine: both automata satisfy the
stabilisation condition on their state transformations. -/
def IsAperiodicBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ TransAperiodic M.prefixStep ∧ TransAperiodic M.suffixStep

end Lax132576.Bimachines
