import Lax132576.EpsilonFreeAutomata

/-!
---
title: Elimination of ε-transitions, with extended transitions
type: theorem
---
Every rational relation is computed by an automaton with output and extended
transitions in which every accepting run is in ε-free normal form: if the input
string is nonempty, each transition reads exactly one letter, and if the input
is empty, the run has exactly one transition (Lemma B.2.4 of *Transducers*,
first sentence). After arranging that no state is both initial and final and
that every transition reads at most one letter, the usual elimination replaces,
for every letter $a$ and states $p, q$, the runs from $p$ to $q$ reading $a$ and
any number of empty-input transitions by one transition labelled with the
regular language of their outputs; a fresh initial and a fresh final state with
one transition between them, labelled with the outputs on the empty input, take
care of the empty string.

# Formalization notes

The automaton is a `LabAut` with regular languages as labels
(`IsExtendedNFAO`), its relation is `extRel`, and the normal form is
`EpsilonFree`. Both alphabets are assumed finite.
-/

namespace Lax132576.EpsilonEliminationExtended

open Lax132576.LabelledAutomata Lax132576.RationalRelations Lax132576.EpsilonFreeAutomata

/-- Every rational relation is computed by an ε-free automaton with extended
transitions. -/
axiom exists_extended_epsilonFree {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    ∃ (Q : Type) (_ : Finite Q) (M : LabAut A (Language B) Q),
      IsExtendedNFAO M ∧ EpsilonFree M ∧ ∀ w v, R w v ↔ extRel M w v

end Lax132576.EpsilonEliminationExtended
