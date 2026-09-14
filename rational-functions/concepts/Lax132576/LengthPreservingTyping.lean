import Lax765601.ElementaryProperties
import Lax132576.RationalRelations

/-!
---
title: Length preservation through a typing of the states
type: theorem
---
Fix an automaton with output computing a function $f$, all of whose states are
productive. A *typing* is a function $\tau : Q \to \mathbb{Z}$ such that every
run from an initial state to a state $q$ satisfies
$$|\text{output}| = |\text{input}| + \tau(q).$$
The function $f$ is length preserving if and only if a typing exists and maps
every accepting state to zero (Claim B.4.4 of *Transducers*). If no typing
exists, two runs reach the same state with different length differences and
the function cannot be length preserving; if a typing exists but some accepting
state has nonzero type, a run reaching it witnesses the same.

# Formalization notes

The automaton `M` computes `f` in the sense that its relation is the graph of
`f`; productivity of all states is a hypothesis, as the book assumes
implicitly. Runs are paths from an initial state, and the typing condition is
stated for all of them.
-/

namespace Lax132576.LengthPreservingTyping

open Lax765601.ElementaryProperties Lax132576.LabelledAutomata Lax132576.RationalRelations

/-- A function computed by an automaton with output with productive states is length
preserving if and only if the automaton has a typing vanishing on the accepting
states. -/
axiom lengthPreserving_iff_typing {A B Q : Type} (M : NFAO A B Q)
    (hprod : ∀ q, M.Productive q) {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w) :
    LengthPreserving f ↔
      ∃ τ : Q → ℤ,
        (∀ q ∈ M.init, ∀ ts p, M.Path q ts p →
          ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + τ p) ∧
        ∀ p ∈ M.final, τ p = 0

end Lax132576.LengthPreservingTyping
