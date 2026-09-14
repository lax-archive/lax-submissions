import Mathlib.Algebra.BigOperators.Finprod
import Lax132576.LabelledAutomata

/-!
---
title: Weighted automata
type: definition
---
A *weighted automaton* over a semiring $\mathbb{S}$ (Definition B.3.2 of
*Transducers*) is defined like a nondeterministic automaton with output, except
that the transitions carry elements of $\mathbb{S}$ instead of output strings,
and that every input string is required to have only finitely many accepting
runs. Its semantics is the function $A^* \to \mathbb{S}$ mapping an input
string $w$ to
$$\sum_{\rho} \text{weight of } \rho,$$
the sum over the accepting runs $\rho$ over $w$ of the product of the weights
of the transitions of $\rho$, taken in the order of the run — which matters when
the multiplication of $\mathbb{S}$ is not commutative. The finiteness
requirement is what makes the sum well defined. Over the Boolean semiring
weighted automata are nondeterministic automata; over the semiring of regular
languages they are the rational relations; over $\mathbb{Q}$ they have
decidable equivalence (Theorem B.3.3).

# Formalization notes

A semiring (Definition B.3.1) is mathlib's `Semiring`. A weighted automaton is
a labelled automaton (`LabelledAutomata`) with labels in `S`; `weightOf` is
the ordered product of the labels of a path, `FinitelyManyRuns` the
requirement of the definition, and `wEval` the sum over the set of accepting
runs, written as mathlib's finite sum over a set (`∑ᶠ`), which is the intended
sum whenever the set is finite. `IsWeighted f` asks for a finite state space
and an automaton satisfying the finiteness requirement.
-/

namespace Lax132576.WeightedAutomata

open Lax132576.LabelledAutomata

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, in the
order in which they are taken. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (LabAut.labelsOf ts).prod

/-- The semantics of a weighted automaton: the sum of the weights of the accepting
runs over the input. -/
noncomputable def wEval (M : LabAut A S Q) (w : List A) : S :=
  ∑ᶠ ts ∈ M.acceptingOn w, weightOf ts

/-- The requirement of Definition B.3.2: every input string has only finitely
many accepting runs. -/
def FinitelyManyRuns (M : LabAut A S Q) : Prop := ∀ w : List A, (M.acceptingOn w).Finite

/-- A function `A* → S` computed by a weighted automaton over the semiring `S`
with a finite state space. -/
def IsWeighted {A S : Type} [Semiring S] (f : List A → S) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : LabAut A S Q), FinitelyManyRuns M ∧ wEval M = f

end Lax132576.WeightedAutomata
