import Lax194892.ForTransducers
import Lax194892.ChildConfigurationGraphs

/-!
---
title: A for-transducer produces the child configuration graph
type: theorem
---
There is a for-transducer which inputs the string representation of a
configuration and outputs the string representation of its child configuration
graph (Claim D.2.6 of *Transducers*). Each letter of the graph is a Boolean
combination of regular properties of the configuration with one marked gap —
whether a given pair of children in adjacent columns is joined by a balanced
run (Claim D.2.3) — so the graph is computed by a rational function, hence by a
for-transducer.

# Formalization notes

As for Lemma D.2.5 the stack is required to have fewer than `k` pebbles, and
the index `nid` of the moving pebble, recorded in the output alphabet, is the
height of the stack. The input alphabet and the state space are assumed
finite.
-/

namespace Lax194892.ChildGraphOfConfiguration

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding
  Lax194892.ChildConfigurationGraphs Lax194892.ForTransducers

/-- A for-transducer maps the representation of a configuration to the
representation of its child configuration graph. -/
axiom exists_forTransducer_childGraph {A B Q : Type} [Finite A] [Finite Q] {k : ℕ}
    (M : Pebble A B Q k) :
    ∃ f : List (ConfLetter A Q k) → List (CGLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → Vtx Q) (m : ℕ) (nid : Fin k),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k → (nid : ℕ) = st.length →
        IsChildSeq M w q₀ st ch m →
        f (confEnc q₀ st w) = cgOfChildren w st nid ch m

end Lax194892.ChildGraphOfConfiguration
