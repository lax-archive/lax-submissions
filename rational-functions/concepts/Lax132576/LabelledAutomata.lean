import Mathlib.Data.Set.Finite.Basic

/-!
---
title: Automata with labelled transitions
type: definition
---
The two nondeterministic models of Part B of *Transducers* — nondeterministic
automata with output (Definition B.1.1) and weighted automata (Definition
B.3.2) — are automata whose finitely many transitions are labelled by an input
string together with a label from some set: an output string in the first
case, an element of a semiring in the second. This concept is their common
basis: a finite set of transitions
$$\delta \subseteq Q \times A^* \times L \times Q,$$
each a directed edge from a state to a state carrying an input string and a
label, together with initial and final subsets of the state space. A *run* is a
path that begins in an initial state and ends in a final state; its input string
is the concatenation of the input strings of its transitions, and its labels are
read off in the order in which the transitions are taken.

# Formalization notes

A path is the list of the transitions it uses, so that two runs with the same
input are different objects when they use different transitions — which is what
"exactly one accepting run" (unambiguity) and "finitely many accepting runs"
(weighted automata) have to count. `Path M q ts p` says that `ts` is a path from
`q` to `p`, and `Accepting` that a path starts in an initial state and ends in a
final one. The state space is a type parameter; its finiteness is required in
`RationalRelations` and `WeightedAutomata` where a function is said to be
computed by an automaton. The transition relation is a `Set` with a finiteness
proof, as the book's "finite set".
-/

namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

/-- A path in the automaton, given as the list of the transitions it uses. -/
inductive Path (M : LabAut A L Q) : Q → List (Q × List A × L × Q) → Q → Prop
  | nil (q : Q) : Path M q [] q
  | cons {q : Q} {u : List A} {l : L} {q' : Q} {ts : List (Q × List A × L × Q)} {p : Q} :
      (q, u, l, q') ∈ M.δ → Path M q' ts p → Path M q ((q, u, l, q') :: ts) p

/-- The input string of a path: the concatenation of the input strings of its
transitions. -/
def inputOf (ts : List (Q × List A × L × Q)) : List A := (ts.map (fun t => t.2.1)).flatten

/-- The labels along a path, in the order of the transitions. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

/-- A path is accepting if it starts in an initial state and ends in a final state.
-/
def Accepting (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) : Prop :=
  ∃ q ∈ M.init, ∃ p ∈ M.final, M.Path q ts p

/-- The accepting paths with a given input string. -/
def acceptingOn (M : LabAut A L Q) (w : List A) : Set (List (Q × List A × L × Q)) :=
  {ts | M.Accepting ts ∧ inputOf ts = w}

end LabAut

end Lax132576.LabelledAutomata
