import Lax132576.LabelledAutomata

/-!
---
title: Nondeterministic automata with output and rational relations
type: definition
---
A *nondeterministic automaton with output* (Definition B.1.1 of *Transducers*)
consists of input and output alphabets $A$ and $B$, a finite set of states $Q$,
initial and final subsets $I, F \subseteq Q$, and a finite transition relation
$$\delta \subseteq Q \times A^* \times B^* \times Q.$$
It is a directed graph whose edges are labelled by pairs of an input string and
an output string; a run is a path from an initial to a final state, and its
input and output strings are the concatenations of the labels along it. The
semantics of the automaton is the relation $R \subseteq A^* \times B^*$ of the
pairs (input string, output string) of its accepting runs, and a relation is
*rational* (Definition B.1.2) if it is the semantics of such an automaton.
Rational relations are input/output symmetric, and a single input may have
infinitely many outputs, through transitions with empty input.

An automaton with output is *unambiguous* if every input string has exactly
one accepting run; the relations computed by unambiguous automata are the second
item of Theorem B.2.3. A state is *productive* if it occurs in some accepting
run (Claim B.4.4).

# Formalization notes

An automaton with output is a labelled automaton (`LabelledAutomata`) whose
labels are output strings, `NFAO A B Q := LabAut A (List B) Q`. `rel M w v` says
that some accepting run reads `w` and writes `v`. `IsRationalRel R` asks for a
finite state space and an automaton over it whose relation is `R`; the
alphabets are arbitrary types, their finiteness being a hypothesis of the
theorems that need it.
-/

namespace Lax132576.RationalRelations

open Lax132576.LabelledAutomata

/-- A nondeterministic automaton with output: a labelled automaton whose labels
are output strings. -/
abbrev NFAO (A B Q : Type) := LabAut A (List B) Q

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path: the concatenation of the outputs of its
transitions. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B := (LabAut.labelsOf ts).flatten

/-- The relation computed by an automaton with output: `w` is related to `v` if
some accepting run reads `w` and writes `v`. -/
def rel (M : NFAO A B Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

/-- An automaton with output is unambiguous if every input string has exactly one
accepting run. -/
def Unambiguous (M : NFAO A B Q) : Prop :=
  ∀ w : List A, ∃! ts, M.Accepting ts ∧ LabAut.inputOf ts = w

/-- A state is productive if it occurs in some accepting run. -/
def Productive (M : NFAO A B Q) (q : Q) : Prop :=
  ∃ q₀ ∈ M.init, ∃ p ∈ M.final, ∃ ts₁ ts₂, M.Path q₀ ts₁ q ∧ M.Path q ts₂ p

end NFAO

/-- A relation is rational if it is computed by a nondeterministic automaton with
output with a finite state space. -/
def IsRationalRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), ∀ w v, R w v ↔ M.rel w v

/-- A relation computed by an unambiguous automaton with output. -/
def IsUnambiguousRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), M.Unambiguous ∧ ∀ w v, R w v ↔ M.rel w v

end Lax132576.RationalRelations
