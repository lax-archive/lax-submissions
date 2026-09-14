import Lax132576.RationalRelations

/-!
---
title: Uniformisation of total rational relations
type: theorem
---
If a rational relation is total — every input string has at least one output —
then it contains an unambiguous rational relation (Lemma B.2.5 of
*Transducers*). After eliminating ε-transitions, the unambiguous automaton
follows the run of the original automaton that is lexicographically minimal
for a chosen linear order on the states: its states are pairs $P \ni p$ of the
set $P$ of states that can still reach acceptance, chosen deterministically
from right to left, and the minimal state $p \in P$ reachable so far, chosen
deterministically from left to right; the output of a transition is one chosen
output of the original automaton between its two states on its letter.

# Formalization notes

The contained relation `S` is unambiguous in the sense of `IsUnambiguousRel`,
and `S ⊆ R` is stated pointwise. Both alphabets are assumed finite.
-/

namespace Lax132576.Uniformisation

open Lax132576.RationalRelations

/-- A total rational relation contains an unambiguous rational relation. -/
axiom exists_isUnambiguousRel_le {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S

end Lax132576.Uniformisation
