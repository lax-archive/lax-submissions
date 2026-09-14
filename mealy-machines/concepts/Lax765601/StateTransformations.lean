import Mathlib.Logic.Function.Iterate
import Lax765601.MealyMachine

/-!
---
title: State transformations of a pre-automaton
type: definition
---
A *pre-automaton* is a deterministic finite automaton without designated initial
and accepting states: an input alphabet $A$, a state space $Q$ and a family of
*state transformations* $\delta_a : Q \to Q$, one for each letter $a \in A$
(Section A.2 of *Transducers*). The state transformation $\delta_w$ of an input
string $w$ is the composition of the state transformations of its letters, in
the order in which they are read.

The *state transformation transducer* of a pre-automaton is the Mealy machine of
type $A^* \to (Q \to Q)^*$ whose $n$-th output letter is the state
transformation of the first $n$ input letters. It is the object that the proof of
the Krohn–Rhodes theorem decomposes (Lemma A.2.5).

A pre-automaton satisfies the *stabilisation condition* (*) of Lemma A.2.11 if
for every state transformation $\delta$ that arises from some input string, the
sequence of powers $\delta^1, \delta^2, \ldots$ eventually stabilises on a single
state transformation. This is the condition on a minimal Mealy machine that
characterises aperiodicity.

# Formalization notes

A pre-automaton is just its transition function `δ : Q → A → Q`; no structure is
introduced. `strTrans δ w` is the state transformation of the string `w`, a
left fold of `δ` along `w`, so that the letters act in reading order. The
transition function of the state transformation transducer stores the state
transformation of the prefix read so far as its state and outputs it after every
letter, as the book describes; its state space `Q → Q` is finite when `Q` is.
`f^[n]` is the `n`-th iterate of `f`.
-/

namespace Lax765601.StateTransformations

open Lax765601.MealyMachine

/-- The state transformation of an input string, for the pre-automaton `δ`: the
letters act one after the other, in reading order. -/
def strTrans {A Q : Type} (δ : Q → A → Q) (w : List A) : Q → Q := fun q => w.foldl δ q

/-- The stabilisation condition (*) of Lemma A.2.11: for every state
transformation `δ_w` arising from an input string, the sequence of its powers
`δ_w¹, δ_w², …` eventually stabilises. -/
def TransAperiodic {A Q : Type} (δ : Q → A → Q) : Prop :=
  ∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, (strTrans δ w)^[n] = (strTrans δ w)^[N]

/-- The state transformation transducer of a pre-automaton: the Mealy machine
whose `n`-th output letter is the state transformation of the first `n` input
letters. -/
def stateTransTransducer {A Q : Type} (δ : Q → A → Q) : Mealy A (Q → Q) (Q → Q) where
  init := id
  step := fun t a => (fun q => δ (t q) a, fun q => δ (t q) a)

end Lax765601.StateTransformations
