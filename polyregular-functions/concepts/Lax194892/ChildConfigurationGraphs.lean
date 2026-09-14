import Mathlib.Data.Nat.Find
import Mathlib.Data.Finite.Defs
import Lax194892.PebbleConfigurationEncoding

/-!
---
title: Children of a configuration and child configuration graphs
type: definition
---
Section D.2 of *Transducers* organises a run of a pebble transducer as a
tree: the *children* of a configuration of height $\ell$ are the configurations
of height $\ell + 1$ that the run visits after it before coming back down to
height $\ell$; between two consecutive children the run stays above height
$\ell + 1$. The children are described by the *child configuration graph*: a
directed graph whose vertices are pairs of a state and a gap — the position of
the moving pebble $\ell + 1$ — with an edge for the run between two consecutive
children, annotated with the input string and the positions of the fixed
pebbles $1, \ldots, \ell$. Like a configuration, a child configuration graph is
represented as a string over a fixed finite alphabet with one letter per gap of
the input, and the *output* of the graph is the concatenation of the string
representations of the children in order of execution. Lemma D.2.5 and Claims
D.2.6–D.2.7 say that a for-transducer computes the graph from the configuration
and the children from the graph.

# Formalization notes

A child is the vertex `(q, p)` standing for the configuration whose stack is
the parent's with the gap `p` on top (`cfgOf`); `FirstChild` and `NextChild` are
runs that stay strictly above the children's height (`StrictAbove`, a run of at
least one step whose intermediate configurations have height at least `h`),
and `IsChildSeq M w q st ch m` says that `ch 0, …, ch m` is the list of the
children of `(q, st)`. `confEnc` is the string representation of a single
configuration (the shape of `PebbleConfigurationEncoding`, for one
configuration). A letter of the child configuration graph carries the input
letter, the fixed pebbles of the gap, the index of the moving pebble, which
states are the first child in this column, and for every state the outgoing
and the incoming edge of the vertex, the latter redundant but what makes the
representation locally checkable (`Chk`). `cgOfChildren` is the representation
of the graph of a configuration with children `ch`, and `CGOutIs u v` says
that `v` is the concatenation of the children's representations read off the
graph `u` (`CGPath`); a string determines at most one such `v`.
-/

namespace Lax194892.ChildConfigurationGraphs

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

-- ## The children of a configuration

/-- The stack has height at least `h`; the halting vertex has no height. -/
def HeightGe {Q : Type} (h : ℕ) : PebbleCfg Q → Prop
  | PebbleCfg.conf _ st => h ≤ st.length
  | PebbleCfg.halt => False

/-- A run of at least one step whose intermediate configurations have height at
least `h`. -/
inductive StrictAbove {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (h : ℕ) :
    PebbleCfg Q → PebbleCfg Q → Prop
  /-- A single step. -/
  | one {c c' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → StrictAbove M w h c c'
  /-- A step to a configuration of height at least `h`, followed by such a run. -/
  | cons {c c' c'' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → HeightGe h c' →
      StrictAbove M w h c' c'' → StrictAbove M w h c c''

/-- A vertex of a child configuration graph: a state and a gap. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- The configuration of the child `v` of a configuration with stack `st`: the
moving pebble sits on top. -/
def cfgOf {Q : Type} (st : List ℕ) (v : Vtx Q) : PebbleCfg Q := PebbleCfg.conf v.1 (st ++ [v.2])

/-- `v'` is the child following the child `v`: the run from `v` first returns to
the children's height at `v'`. -/
def NextChild {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (st : List ℕ)
    (v v' : Vtx Q) : Prop :=
  StrictAbove M w (st.length + 2) (cfgOf st v) (cfgOf st v')

/-- `v` is the first child of the configuration `(q, st)`. -/
def FirstChild {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ)
    (v : Vtx Q) : Prop :=
  StrictAbove M w (st.length + 2) (PebbleCfg.conf q st) (cfgOf st v)

/-- `ch 0, …, ch m` is the list of the children of `(q, st)`, in order of
execution. -/
structure IsChildSeq {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (q : Q)
    (st : List ℕ) (ch : ℕ → Vtx Q) (m : ℕ) : Prop where
  /-- The list starts with the first child. -/
  first : FirstChild M w q st (ch 0)
  /-- Each child is followed by the next one. -/
  next : ∀ t < m, NextChild M w st (ch t) (ch (t + 1))
  /-- The last child has no successor. -/
  stop : ∀ v, ¬ NextChild M w st (ch m) v

-- ## String representations

/-- A letter of the representation of a configuration: the state, the input letter
following the gap, and the pebbles in the gap. -/
abbrev ConfLetter (A Q : Type) (k : ℕ) := Q × Option A × (Fin k → Bool)

/-- The string representation of the configuration `(q, st)` of `w`: one letter per
gap. -/
def confEnc {A Q : Type} {k : ℕ} (q : Q) (st : List ℕ) (w : List A) : List (ConfLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q, w[p]?, ann k st p)

/-- The direction of an edge: inside the column, one column right, one column left. -/
abbrev Dir := Option Bool

/-- The column that the direction `d` leads to from the column `p`. -/
def dest (p : ℕ) : Dir → Option ℕ
  | none => some p
  | some true => some (p + 1)
  | some false => if p = 0 then none else some (p - 1)

/-- The direction from the column `a` to the adjacent column `b`. -/
def dirOf (a b : ℕ) : Dir := if b = a then none else if a < b then some true else some false

/-- A letter of the representation of a child configuration graph: one gap of the
input, with the input letter, the fixed pebbles, the index of the moving pebble,
the states that are the first child in this column, and the outgoing and
incoming edges of the vertices of this column. -/
structure CGLetter (A Q : Type) (k : ℕ) where
  /-- The input letter following this gap, absent for the last gap. -/
  lett : Option A
  /-- The fixed pebbles sitting in this gap. -/
  peb : Fin k → Bool
  /-- The index of the moving pebble. -/
  nid : Fin k
  /-- The states `q` for which `(q, this column)` is the first child. -/
  src : Q → Bool
  /-- The outgoing edge of `(q, this column)`. -/
  nxt : Q → Option (Q × Dir)
  /-- The incoming edge of `(q, this column)`. -/
  prv : Q → Option (Q × Dir)

open scoped Classical in
/-- The index at which `v` occurs among the first `m` children, if any. -/
noncomputable def idxAt {Q : Type} (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) : Option ℕ :=
  if h : ∃ t, t < m ∧ ch t = v then some (Nat.find h) else none

open scoped Classical in
/-- The index `t < m` such that `v` is the child following `ch t`, if any. -/
noncomputable def idxSuccAt {Q : Type} (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) : Option ℕ :=
  if h : ∃ t, t < m ∧ ch (t + 1) = v then some (Nat.find h) else none

open scoped Classical in
/-- The representation of the child configuration graph whose children are
`ch 0, …, ch m`, over an input with `n + 1` gaps carrying the letters `lett` and
the fixed pebbles `peb`, the moving pebble having the index `nid`. -/
noncomputable def cgOfPath {A Q : Type} {k : ℕ} (lett : ℕ → Option A) (peb : ℕ → Fin k → Bool)
    (nid : Fin k) (n : ℕ) (ch : ℕ → Vtx Q) (m : ℕ) : List (CGLetter A Q k) :=
  (List.range (n + 1)).map fun j =>
    { lett := lett j
      peb := peb j
      nid := nid
      src := fun q' => decide ((q', j) = ch 0)
      nxt := fun q' => (idxAt ch m (q', j)).map fun t => ((ch (t + 1)).1, dirOf j (ch (t + 1)).2)
      prv := fun q' => (idxSuccAt ch m (q', j)).map fun t => ((ch t).1, dirOf (ch t).2 j) }

/-- The representation of the child configuration graph of a configuration of `w`
with stack `st`, moving pebble `nid` and children `ch 0, …, ch m`. -/
noncomputable def cgOfChildren {A Q : Type} {k : ℕ} (w : List A) (st : List ℕ) (nid : Fin k)
    (ch : ℕ → Vtx Q) (m : ℕ) : List (CGLetter A Q k) :=
  cgOfPath (fun j => w[j]?) (fun j => ann k st j) nid w.length ch m

-- ## Reading the children off a represented graph

/-- The vertex that the edge out of `v` leads to, if any. -/
def succOf {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) : Option (Vtx Q) :=
  (u[v.2]?).bind fun c => (c.nxt v.1).bind fun x => (dest v.2 x.2).map fun p' => (x.1, p')

/-- `v` is marked as the first child. -/
def IsSrc {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) : Prop :=
  ∃ c, u[v.2]? = some c ∧ c.src v.1 = true

/-- The representation of the child that the vertex `v` stands for: the state of
`v`, the input letters and the fixed pebbles of the graph, and the moving pebble
in the column of `v`. -/
def confAt {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) :
    List (ConfLetter A Q k) :=
  u.mapIdx fun j c => (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j)))

/-- The letter to the left of the gap `i`. -/
def leftLet {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (i : ℕ) : Option (CGLetter A Q k) :=
  if i = 0 then none else u[i - 1]?

open Classical in
/-- The local consistency test on two adjacent letters: every edge recorded by
`nxt` between or inside their columns is recorded by `prv` at its target, and a
vertex marked as the first child has no incoming edge. -/
noncomputable def pairOK {A Q : Type} {k : ℕ} (a b : Option (CGLetter A Q k)) : Bool := decide (
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → ca.nxt q = some (q', some true) →
      cb.prv q' = some (q, some true)) ∧
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → cb.nxt q = some (q', some false) →
      ca.prv q' = some (q, some false)) ∧
  (∀ q q' : Q, ∀ cb, b = some cb → cb.nxt q = some (q', none) → cb.prv q' = some (q, none)) ∧
  (∀ q : Q, ∀ cb, b = some cb → cb.src q = true → cb.prv q = none))

/-- The string is locally consistent at every gap. -/
def Chk {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) : Prop :=
  ∀ i ≤ u.length, pairOK (leftLet u i) u[i]? = true

/-- `p 0, …, p m` is the run of children described by the locally consistent
string `u`: `p 0` is the unique first child, each `p (t+1)` is reached from `p t`
by the recorded edge, and `p m` has no outgoing edge. -/
structure CGPath {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) :
    Prop where
  /-- The string is locally consistent. -/
  chk : Chk u
  /-- `p 0` is the unique vertex marked as the first child. -/
  srcEq : ∀ v, IsSrc u v ↔ v = p 0
  /-- Every vertex of the run sits in a real column. -/
  inRange : ∀ t ≤ m, (u[(p t).2]?).isSome
  /-- Consecutive children are joined by the recorded edge. -/
  step : ∀ t < m, succOf u (p t) = some (p (t + 1))
  /-- The last child has no outgoing edge. -/
  last : succOf u (p m) = none

/-- The concatenation of the representations of the children, in order. -/
def cgOut {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) :
    List (ConfLetter A Q k) :=
  ((List.range (m + 1)).map fun t => confAt u (p t)).flatten

/-- `v` is the string representation of the children of the configuration whose
child configuration graph `u` represents. -/
def CGOutIs {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : List (ConfLetter A Q k)) :
    Prop :=
  ∃ m p, CGPath u m p ∧ v = cgOut u m p

end Lax194892.ChildConfigurationGraphs
