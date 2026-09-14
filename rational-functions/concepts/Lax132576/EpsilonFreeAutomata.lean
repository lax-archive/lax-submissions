import Mathlib.Computability.DFA
import Lax132576.RationalRelations

/-!
---
title: Extended transitions and the elimination of ε-transitions
type: definition
---
Transitions with empty input ($\varepsilon$-transitions) are essential to
automata with output in two roles: producing an output for the empty input, and
producing infinitely many outputs for one input. Lemma B.2.4 of *Transducers*
shows that, up to these two caveats, they can be eliminated. An automaton with
*extended transitions* carries, instead of an output string, a regular language
of output strings on every transition; the relation it computes takes as
outputs all strings in the concatenation of the languages along an accepting
run. An automaton (with ordinary or extended transitions) is in the
*ε-free normal form* of the lemma if in every accepting run, either the input
is nonempty and each transition reads exactly one letter, or the input is empty
and the run consists of exactly one transition.

# Formalization notes

An automaton with extended transitions is a labelled automaton whose labels are
languages over `B`; `IsExtendedNFAO` asks that every label be regular, and
`extRel` is its relation, `v` ranging over the product of the languages of the
run. `EpsilonFree` is the normal form, stated for any labelled automaton so that
both halves of Lemma B.2.4 can use it.
-/

namespace Lax132576.EpsilonFreeAutomata

open Lax132576.LabelledAutomata

/-- An automaton with extended transitions: transitions are labelled by an input
string and a regular language of output strings. -/
def IsExtendedNFAO {A B Q : Type} (M : LabAut A (Language B) Q) : Prop :=
  ∀ t ∈ M.δ, Language.IsRegular t.2.2.1

/-- The relation computed by an automaton with extended transitions: the output
is any string in the concatenation of the languages along an accepting run. -/
def extRel {A B Q : Type} (M : LabAut A (Language B) Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ v ∈ (LabAut.labelsOf ts).prod

/-- The normal form of Lemma B.2.4: in every accepting run, either the input is
nonempty and each transition reads exactly one letter, or the input is empty and
the run has exactly one transition. -/
def EpsilonFree {A L Q : Type} (M : LabAut A L Q) : Prop :=
  ∀ ts, M.Accepting ts →
    (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
    (LabAut.inputOf ts = [] → ts.length = 1)

end Lax132576.EpsilonFreeAutomata
