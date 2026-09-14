import Lax765601.ElementaryProperties
import Lax132576.RationalFunctions

/-!
---
title: Length preserving rational functions have length preserving automata
type: theorem
---
If a rational function is length preserving, then it is computed by an
automaton with output in which the input and the output string of every
transition have the same length (Lemma B.4.5 of *Transducers*). The book's
proof takes the typing of Claim B.4.4 and works in the free group over the
output alphabet: the new states are pairs $(q, x)$ of a state and a reduced
string $x$ of length $\tau(q)$, possibly negative, and a transition
$q \xrightarrow{w / x^{-1} v y} p$ of the original automaton becomes the
transition $(q, x) \xrightarrow{w / v} (p, y)$, whose lengths agree.

# Formalization notes

The conclusion asks for a finite state space and an automaton all of whose
transitions `(p, u, v, q)` satisfy `u.length = v.length`, whose relation is the
graph of `f`. Both alphabets are assumed finite.
-/

namespace Lax132576.LengthPreservingNormalForm

open Lax765601.ElementaryProperties Lax132576.RationalRelations Lax132576.RationalFunctions

/-- A length preserving rational function is computed by an automaton with output
whose every transition reads and writes strings of the same length. -/
axiom exists_nfao_length_eq {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hlen : LengthPreserving f) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length = t.2.2.1.length) ∧ ∀ w v, M.rel w v ↔ v = f w

end Lax132576.LengthPreservingNormalForm
