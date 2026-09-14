import Mathlib.Computability.Primrec.List
import Lax916827.TwoWayTransducers

/-!
---
title: Codes of two-way transducers
type: definition
---
The equivalence problem for regular functions (Theorem C.1.4 of *Transducers*)
is decided on two-way transducers, which by Theorem C.2.9 compute exactly the
regular functions. A two-way transducer with states and letters in
$\mathbb{N}$ is described by a finite *code*: a lookup table for its transition
function, listing for finitely many triples (letter to the left, state, letter
to the right) the transition taken there. The initial state is $0$, and a
triple absent from the table halts with empty output. A code is *total* if the
transducer it describes halts on every input.

# Formalization notes

`TwoWayCode` is a list of table entries; it is `Primcodable` as a list of pairs,
so that decidability can be stated with `DecidableUnderPromise` of
`Lax132576.TransducerCodes`. `twoWayCodeRel c` is the relation computed by the
coded transducer (a partial function, by determinism), and `TwoWayCodeTotal` the
promise that it is total.
-/

namespace Lax916827.TwoWayCodes

open Lax916827.TwoWayTransducers

/-- A code of a two-way transducer over `ℕ`: a lookup table from triples (letter to
the left, state, letter to the right) to transitions. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

/-- The two-way transducer described by a code: initial state `0`, and the table
entry of a triple, or halting with empty output when the triple is absent. -/
def twoWayCodeAut (c : TwoWayCode) : TwoWay ℕ ℕ ℕ where
  init := 0
  step := fun l q r =>
    match c.lookup (l, q, r) with
    | some x => x
    | none => Sum.inl []

/-- The relation computed by the coded transducer. -/
def twoWayCodeRel (c : TwoWayCode) : List ℕ → List ℕ → Prop := (twoWayCodeAut c).Computes

/-- The coded transducer computes a total function: it halts on every input. -/
def TwoWayCodeTotal (c : TwoWayCode) : Prop := ∀ w, ∃ v, twoWayCodeRel c w v

end Lax916827.TwoWayCodes
