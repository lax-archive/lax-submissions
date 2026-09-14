import Mathlib.Data.Set.Finite.Basic
import Lax916827.TwoWayTransducers

/-!
---
title: The string representation of the reachable configuration graph
type: definition
---
The proof of Theorem C.2.2 of *Transducers* represents the *reachable
configuration graph* of a two-way transducer on a fixed input — the
configurations on its run, with the transition between consecutive ones — as a
string over a finite alphabet $C$. The graph is sliced along the letters of the
input: the slice at a letter is a bipartite graph whose vertices are two copies
of the state space $Q$, one for the gap to the left of the letter and one for
the gap to its right, with a directed edge, labelled by an output string, for
every transition of the run that crosses the letter; each vertex has at most one
outgoing edge, and it goes to the other copy of $Q$. The alphabet $C$ consists
of these slices, and is finite because only the finitely many output strings
occurring in the transition function label edges. A special letter represents
the graph of the empty input, which has no letter to slice at.

Lemma C.2.3 says that the map from an input to the representation of its
reachable configuration graph is rational; Lemma C.2.4 that the representations
whose output string lies in a regular language form a regular language. The
output string of a representation is read by a two-way transducer over $C$ that
walks along the represented path and prints the labels it meets.

# Formalization notes

A slice is a function `Bool × Q → VOut Q L` giving the outgoing edge of every
vertex: none, an edge to a state of the other copy with a label, or the halting
vertex with the label of the halting transition (recorded on both copies of the
cut where the transducer halts, since the halting vertex belongs to no copy).
The labels are the output strings occurring in the transition function of the
transducer, `Lab M`, a finite set. `enc M w` records, in the slice of the letter
at position `i`, the outgoing edges of the *reachable* configurations at the
gaps `i` and `i + 1`: a configuration not visited by the run gets no edge, and
the empty input gets the special letter carrying the output of the halting
transition on the empty input, if the run halts there. `pathTrans M` is the
transducer over `C` that walks along the path; on a string that represents
nothing its behaviour is irrelevant.
-/

namespace Lax916827.ConfigurationGraphs

open Lax916827.TwoWayTransducers

/-- The outgoing edge of a vertex inside one slice: none, an edge to the state `q'`
of the other copy labelled `l`, or the halting vertex with the output `l`. -/
inductive VOut (Q L : Type) where
  /-- No outgoing edge inside this slice. -/
  | nil : VOut Q L
  /-- An edge to the state `q'` of the other copy, labelled `l`. -/
  | move (q' : Q) (l : L) : VOut Q L
  /-- The transducer halts here, producing `l`. -/
  | halt (l : L) : VOut Q L

/-- A slice of the configuration graph at a letter: the outgoing edge of every
vertex, `(false, q)` being the state `q` at the gap to the left of the letter and
`(true, q)` at the gap to its right. -/
abbrev Slice (Q L : Type) := Bool × Q → VOut Q L

/-- The alphabet `C`: the slices, and the special letter for the empty input,
carrying the output of the halting transition on the empty input if the run
halts there. -/
abbrev CLet (Q L : Type) := Slice Q L ⊕ Option L

namespace TwoWay

variable {A B Q : Type}

/-- The output string produced by a transition. -/
def transOut (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : List B :=
  match M.step l q r with
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

/-- The output strings occurring in the transition function. -/
def OutLabels (M : TwoWay A B Q) : Set (List B) :=
  Set.range (fun p : Option A × Q × Option A => transOut M p.1 p.2.1 p.2.2)

/-- The finite set of edge labels: the output strings of the transitions. -/
abbrev Lab (M : TwoWay A B Q) : Type := {o : List B // o ∈ OutLabels M}

/-- The label of the edge produced by a transition. -/
def labOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : Lab M :=
  ⟨transOut M l q r, ⟨(l, q, r), rfl⟩⟩

/-- The outgoing edge recorded, in the direction `d`, for the state `q` at a gap
with adjacent letters `l` and `r`: the left copy of a slice records the
transitions moving right, the right copy those moving left, and a halting
transition is recorded on both copies of its gap. -/
def edgeOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) (d : Bool) : VOut Q (Lab M) :=
  match M.step l q r with
  | Sum.inl _ => VOut.halt (labOf M l q r)
  | Sum.inr (q', _, dir) => if dir = d then VOut.move q' (labOf M l q r) else VOut.nil

/-- The letter to the left of the gap `j` of `w`, if any. -/
def prevAt (w : List A) (j : ℕ) : Option A := if j = 0 then none else w[j - 1]?

open scoped Classical in
/-- The outgoing edge, in the direction `d`, of the state `q` at the gap `j` of
`w`, for the *reachable* configurations only: a configuration the run does not
visit has no edge. -/
noncomputable def cutV (M : TwoWay A B Q) (w : List A) (j : ℕ) (q : Q) (d : Bool) :
    VOut Q (Lab M) :=
  if M.Visits w (Cfg.conf (w.take j) q (w.drop j)) then edgeOf M (prevAt w j) q w[j]? d
  else VOut.nil

/-- The slice of the reachable configuration graph of `M` on `w` at the letter of
position `i`. -/
noncomputable def encSlice (M : TwoWay A B Q) (w : List A) (i : ℕ) : Slice Q (Lab M) :=
  fun v => cutV M w (if v.1 then i + 1 else i) v.2 (!v.1)

/-- The special letter for the empty input: the output of the halting transition on
the empty input, if the run on the empty input halts at once. -/
def emptyOut (M : TwoWay A B Q) : Option (Lab M) :=
  match M.step none M.init none with
  | Sum.inl _ => some (labOf M none M.init none)
  | Sum.inr _ => none

/-- The string representation of the reachable configuration graph of `M` on `w`:
one slice per input letter, and the special letter for the empty input. -/
noncomputable def enc (M : TwoWay A B Q) (w : List A) : List (CLet Q (Lab M)) :=
  if w.isEmpty then [Sum.inr (emptyOut M)]
  else (List.range w.length).map (fun i => Sum.inl (encSlice M w i))

variable {L : Type}

/-- The outgoing edge at the current gap recorded by the letter to the right of
the head. -/
def readR (r : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match r with
  | some (Sum.inl s) => s (false, q)
  | some (Sum.inr (some lab)) => VOut.halt lab
  | _ => VOut.nil

/-- The outgoing edge at the current gap recorded by the letter to the left of the
head. -/
def readL (l : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match l with
  | some (Sum.inl s) => s (true, q)
  | _ => VOut.nil

/-- The two-way transducer over `C` that walks along the path of a represented
configuration graph, printing the labels of the edges it follows; on a string
that represents nothing it halts with empty output. -/
def pathTrans (M : TwoWay A B Q) : TwoWay (CLet Q (Lab M)) B Q where
  init := M.init
  step := fun l q r =>
    match readR r q with
    | VOut.move q' lab => Sum.inr (q', lab.val, true)
    | VOut.halt lab => Sum.inl lab.val
    | VOut.nil =>
      match readL l q with
      | VOut.move q' lab => Sum.inr (q', lab.val, false)
      | VOut.halt lab => Sum.inl lab.val
      | VOut.nil => Sum.inl []

end TwoWay

end Lax916827.ConfigurationGraphs
