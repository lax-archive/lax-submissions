import Mathlib.Data.Set.Card

/-!
---
title: Snake graphs and their outputs
type: definition
---
A *snake graph* with states $Q$, length $n$ and output alphabet $B$ (Section
C.2.4 of *Transducers*) is a directed graph with edges labelled by $B + 1$ whose
vertices are pairs of a row $q \in Q$ and a column $i \in \{0, 1, \ldots, n\}$,
in which edges only go between adjacent columns and all edges lie on a single
directed path. The *output* of a snake graph is the concatenation of the labels
along that path, the extra label of $B + 1$ contributing nothing; its *width* is
the largest number of times the path visits one column. Like configuration
graphs, snake graphs are represented as strings over a finite alphabet $C$
once the state set is fixed: a letter is a bipartite graph on two copies of
$Q$ describing the edges between two adjacent columns. The book's *snake
lemma* (Lemma C.2.12) says that for every $k$ the function mapping a string
over $C$ to the output of the snake graph it represents, if it represents one
of width at most $k$, and to $\varepsilon$ otherwise, is regular; this is the
induction on the width by which two-way transducers are decomposed into primes.

# Formalization notes

A letter `SnakeLetter Q B` assigns to every vertex of the two copies of `Q` —
`(false, q)` in the left column, `(true, q)` in the right one — its outgoing
edge to the other copy, with a label in `Option B`, if it has one; the letter
at position `i` of a string carries the edges between the columns `i` and
`i + 1`, so a string of length `n` describes a graph on `Q × {0, …, n}`. The
book's special letter for the empty input is not needed: the empty string
represents the one-column graph with no edges. A snake path is a directed path
with pairwise distinct vertices covering every edge of the graph; a string
represents at most one output, so `snakeOut k` is well defined by a choice.
The width of the represented graph is bounded by the number of vertices of a
column that carry an edge, and the lemma is stated for every `k`, not only
`k ≤ |Q|`.
-/

namespace Lax916827.SnakeGraphs

/-- The alphabet `C` of snake letters for the state set `Q` and output alphabet `B`:
a letter gives, for every vertex of the two copies of `Q`, its outgoing edge to
the other copy with a label in `B + 1`, if any. -/
abbrev SnakeLetter (Q B : Type) := Bool × Q → Option (Q × Option B)

/-- A vertex of a snake graph: a row `q` and a column `i`. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- The edge relation of the graph represented by `w`: an edge from `v` to `v'`
labelled `o` is recorded by the letter between their columns, read from the left
copy when `v'` is in the next column and from the right copy when it is in the
previous one. -/
def Edge {Q B : Type} (w : List (SnakeLetter Q B)) (v v' : Vtx Q) (o : Option B) : Prop :=
  (v'.2 = v.2 + 1 ∧ ∃ c, w[v.2]? = some c ∧ c (false, v.1) = some (v'.1, o)) ∨
  (v.2 = v'.2 + 1 ∧ ∃ c, w[v'.2]? = some c ∧ c (true, v.1) = some (v'.1, o))

/-- The vertex `v` carries an edge, incoming or outgoing. -/
def Incident {Q B : Type} (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop :=
  (∃ v' o, Edge w v v' o) ∨ (∃ u o, Edge w u v o)

/-- All edges of the graph represented by `w` lie on the single directed path
`p 0, …, p m` with pairwise distinct vertices and edge labels `lab`: this is
what makes the graph a snake graph. -/
structure IsSnakePath {Q B : Type} (w : List (SnakeLetter Q B)) (m : ℕ) (p : ℕ → Vtx Q)
    (lab : ℕ → Option B) : Prop where
  /-- Consecutive vertices of the path are joined by an edge with the recorded
  label. -/
  edge : ∀ t < m, Edge w (p t) (p (t + 1)) (lab t)
  /-- The vertices of the path are pairwise distinct. -/
  inj : ∀ s ≤ m, ∀ t ≤ m, p s = p t → s = t
  /-- Every edge of the graph is an edge of the path. -/
  covers : ∀ v v' o, Edge w v v' o → ∃ t < m, p t = v ∧ p (t + 1) = v' ∧ lab t = o

/-- The output along a path: the concatenation of the labels of its edges, the
label `none` contributing nothing. -/
def pathOut {B : Type} (lab : ℕ → Option B) (m : ℕ) : List B :=
  ((List.range m).map (fun t => (lab t).toList)).flatten

/-- `v` is the output of the snake graph represented by `w`. -/
def SnakeOutIs {Q B : Type} (w : List (SnakeLetter Q B)) (v : List B) : Prop :=
  ∃ m p lab, IsSnakePath w m p lab ∧ v = pathOut lab m

/-- The number of times the snake visits the column `i`: the number of vertices of
that column carrying an edge. -/
noncomputable def colVisits {Q B : Type} (w : List (SnakeLetter Q B)) (i : ℕ) : ℕ :=
  {q : Q | Incident w (q, i)}.ncard

/-- The width of the represented graph is at most `k`. -/
def SnakeWidthLe {Q B : Type} (w : List (SnakeLetter Q B)) (k : ℕ) : Prop :=
  ∀ i, colVisits w i ≤ k

open Classical in
/-- The function of the snake lemma: the output of the snake graph represented by
`w`, if `w` represents one of width at most `k`, and the empty string otherwise.
-/
noncomputable def snakeOut {Q B : Type} (k : ℕ) (w : List (SnakeLetter Q B)) : List B :=
  if h : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v then h.2.choose else []

end Lax916827.SnakeGraphs
