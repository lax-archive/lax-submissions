import Lax194892.ForTransducers
import Lax194892.ChildConfigurationGraphs

/-!
---
title: A for-transducer reads the children off a child configuration graph
type: theorem
---
There is a for-transducer which inputs the string representation of a child
configuration graph and outputs the concatenation of the string representations
of the corresponding child configurations (Claim D.2.7 of *Transducers*). A
two-pebble transducer walks along the path of the graph, one pebble marking the
current child and the other printing its representation, and pebble transducers
are for-transducers (Theorem D.2.4); the book instead proceeds by induction on
the width of the graph, as for snake graphs.

# Formalization notes

The output is characterised by `CGOutIs`, which determines it; the
for-transducer is required to agree with it on every string that represents a
run of children. The input alphabet and the state space are assumed finite.
-/

namespace Lax194892.ChildrenOfChildGraph

open Lax194892.ChildConfigurationGraphs Lax194892.ForTransducers

/-- A for-transducer maps the representation of a child configuration graph to the
concatenation of the representations of the children. -/
axiom exists_forTransducer_cgOut {A Q : Type} [Finite A] [Finite Q] (k : ℕ) :
    ∃ f : List (CGLetter A Q k) → List (ConfLetter A Q k),
      IsForTransducer f ∧ ∀ u v, CGOutIs u v → f u = v

end Lax194892.ChildrenOfChildGraph
