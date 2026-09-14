import Lax132576.EpsilonFreeAutomata

/-!
---
title: Elimination of ε-transitions for finitely valued relations
type: theorem
---
If a rational relation is such that every input string has finitely many
outputs, then it is computed by an ordinary automaton with output in ε-free
normal form: extended transitions are not needed (Lemma B.2.4 of
*Transducers*, second sentence). In the elimination construction, the regular
languages labelling the new transitions are then finite, and each such
transition is replaced by finitely many transitions with one output string
each.

# Formalization notes

The finiteness of the set of outputs of every input is the hypothesis
`∀ w, {v | R w v}.Finite`; the automaton is an ordinary `NFAO` and the normal
form is `EpsilonFree`. Both alphabets are assumed finite.
-/

namespace Lax132576.EpsilonEliminationFinite

open Lax132576.RationalRelations Lax132576.EpsilonFreeAutomata

/-- A finitely valued rational relation is computed by an ε-free automaton with
output. -/
axiom exists_nfao_epsilonFree {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (hfin : ∀ w, {v | R w v}.Finite) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), EpsilonFree M ∧ ∀ w v, R w v ↔ M.rel w v

end Lax132576.EpsilonEliminationFinite
