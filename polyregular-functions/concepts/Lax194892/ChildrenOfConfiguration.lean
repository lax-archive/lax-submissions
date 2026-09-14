import Lax194892.ForTransducers
import Lax194892.ChildConfigurationGraphs

/-!
---
title: A for-transducer produces the children of a configuration
type: theorem
---
For every $k$-pebble transducer there is a for-transducer which inputs the
string representation of a configuration and outputs all children of that
configuration, as the concatenation of their string representations in order
of execution (Lemma D.2.5 of *Transducers*). It is the composition of Claims
D.2.6 and D.2.7: from the configuration to its child configuration graph, and
from the graph to the children.

# Formalization notes

The book does not state the hypothesis that the stack of the input
configuration has fewer than `k` pebbles, but its proof begins with exactly that
case distinction ("if `ℓ = k` there is nothing to do"), so the statement
carries it; the children are given as a child sequence `ch 0, …, ch m`, and the
output is the concatenation of their representations. The input alphabet and
the state space are assumed finite.
-/

namespace Lax194892.ChildrenOfConfiguration

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding
  Lax194892.ChildConfigurationGraphs Lax194892.ForTransducers

/-- A for-transducer maps the representation of a configuration to the
concatenation of the representations of its children. -/
axiom exists_forTransducer_children {A B Q : Type} [Finite A] [Finite Q] {k : ℕ}
    (M : Pebble A B Q k) :
    ∃ f : List (ConfLetter A Q k) → List (ConfLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → Vtx Q) (m : ℕ),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k →
        IsChildSeq M w q₀ st ch m →
        f (confEnc q₀ st w)
          = ((List.range (m + 1)).map fun t => confEnc (ch t).1 (st ++ [(ch t).2]) w).flatten

end Lax194892.ChildrenOfConfiguration
