/-
**The alphabet of snake letters, and the output of a snake graph.**

Lemma `lem:output-of-snake-graph-is-regular` of *Transducers* (M. Bojańczyk) is stated for an
alphabet `C` that represents snake graphs:

> Formally speaking, a *snake graph* with states `Q`, length `n` and alphabet `B` is a directed
> graph with edges labelled by `B + 1` that satisfies the following properties: each vertex consists
> of a row `q ∈ Q` and a column `i ∈ {0,1,…,n}`; all edges in the graph are on a single directed
> path; edges can only go between adjacent columns.  Similarly to configuration graphs in the proof
> of Theorem `thm:continuity-2dfas`, snake graphs can be represented as strings over a finite
> alphabet `C`, once the set of states is fixed.

The alphabet of Theorem `thm:continuity-2dfas` -- rendered in
`RequestProject/PartC/ConfGraph.lean` as `Transducers.CLet` -- "consists of bipartite graphs, where
the vertices are two copies of `Q`, edges are directed and labelled with output strings, each vertex
has at most one outgoing edge, and this edge must go to the other copy of `Q`".  For snake graphs
the labels are the elements of `B + 1`, and there is no halting vertex, so a letter is exactly a
function

  `Bool × Q → Option (Q × Option B)`,

which is `Transducers.SnakeLetter Q B`.  The vertex `(false, q)` is the state `q` in the left copy
(the column to the left of the sliced letter), `(true, q)` is the state `q` in the right copy, and
the value of the function at a vertex is its outgoing edge inside this slice: the state it leads to
in the other copy, and the label of the edge.  A string `w ∈ C*` of length `n` therefore describes a
graph on the vertices `Q × {0,…,n}`, in which the letter at position `i` carries the edges between
the columns `i` and `i + 1`; `SnakeGraph.Edge w` is that graph.  The book's special letter for the
empty input is not needed here: the empty string represents the graph with one column and no edges,
which is a snake graph, with the empty output.

This file defines:

* `Transducers.SnakeLetter`: the alphabet `C`;
* `SnakeGraph.Edge`: the graph a string over `C` describes;
* `SnakeGraph.IsSnakePath`: a directed path that covers *all* the edges of that graph, with
  pairwise distinct vertices -- this is the book's condition that all edges lie on a single directed
  path;
* `SnakeGraph.SnakeOutIs w v`: `v` is the concatenation of the labels along such a path, i.e. `v` is
  *the output of the snake graph* represented by `w`;
* `SnakeGraph.colVisits w i`: the number of vertices of the column `i` that carry an edge, i.e. the
  number of times the snake visits that column, and `SnakeGraph.SnakeWidthLe` for the book's width;
* `SnakeGraph.snakeOut k`: the function of Lemma `lem:output-of-snake-graph-is-regular` -- the
  output of the snake graph represented by `w`, if `w` represents one and its width is at most `k`,
  and the empty string otherwise.

The last definition uses a choice, and is legitimate because the output is unique:
`SnakeGraph.snakeOutIs_unique`, proved at the end of this file, says that a string represents at
most one output.
-/
import Lax916827Proofs.Source.PartC.SnakeReg
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- **The book's alphabet `C` of snake letters**, for the state set `Q` and the output alphabet `B`.
A letter is a bipartite graph on two copies of `Q`: the vertex `(false, q)` is the state `q` in the
left copy of the slice and `(true, q)` is the state `q` in the right copy, and the letter assigns to
each vertex its outgoing edge -- a state of the *other* copy together with a label in `B + 1` --
if it has one.  This is the alphabet of Theorem `thm:continuity-2dfas` (`Transducers.CLet`) with the
labels of the snake graphs and without the halting vertex. -/
abbrev SnakeLetter (Q B : Type) := Bool × Q → Option (Q × Option B)

namespace SnakeGraph

variable {Q B : Type}

/-- A vertex of a snake graph: a row `q ∈ Q` and a column `i ∈ ℕ`.  Only the columns
`0, …, w.length` carry edges. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- **The snake graph represented by a string over the alphabet `C`.**  There is an edge from `v` to
`v'` labelled `o` if either the letter at position `v.2` sends the left-copy vertex `v.1` to the
right-copy vertex `v'.1` (and then `v'` is in the next column), or the letter at position `v'.2`
sends the right-copy vertex `v.1` to the left-copy vertex `v'.1` (and then `v'` is in the previous
column).  In particular edges only go between adjacent columns. -/
def Edge (w : List (SnakeLetter Q B)) (v v' : Vtx Q) (o : Option B) : Prop :=
  (v'.2 = v.2 + 1 ∧ ∃ c, w[v.2]? = some c ∧ c (false, v.1) = some (v'.1, o)) ∨
  (v.2 = v'.2 + 1 ∧ ∃ c, w[v'.2]? = some c ∧ c (true, v.1) = some (v'.1, o))

/-- The edge relation of the snake graph represented by `w`, with the label forgotten. -/
def EdgeRel (w : List (SnakeLetter Q B)) (v v' : Vtx Q) : Prop := ∃ o, Edge w v v' o

/-- The vertex `v` has an outgoing edge. -/
def HasOut (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop := ∃ v' o, Edge w v v' o

/-- The vertex `v` has an incoming edge. -/
def HasIn (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop := ∃ u o, Edge w u v o

/-- The vertex `v` carries an edge. -/
def Incident (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop := HasOut w v ∨ HasIn w v

/-- The vertex `v` is a source: it has an outgoing edge and no incoming edge. -/
def Src (w : List (SnakeLetter Q B)) (v : Vtx Q) : Prop := HasOut w v ∧ ¬ HasIn w v

/-! ## Elementary facts about the edges -/

lemma edge_col_le_left {w : List (SnakeLetter Q B)} {v v' : Vtx Q} {o : Option B}
    (h : Edge w v v' o) : v.2 ≤ w.length := by
  rcases h with ⟨hc, c, hcw, -⟩ | ⟨hc, c, hcw, -⟩
  · have : v.2 < w.length := by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hcw
      exact h
    omega
  · have : v'.2 < w.length := by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hcw
      exact h
    omega

lemma edge_col_le_right {w : List (SnakeLetter Q B)} {v v' : Vtx Q} {o : Option B}
    (h : Edge w v v' o) : v'.2 ≤ w.length := by
  rcases h with ⟨hc, c, hcw, -⟩ | ⟨hc, c, hcw, -⟩
  · have : v.2 < w.length := by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hcw
      exact h
    omega
  · have : v'.2 < w.length := by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hcw
      exact h
    omega

lemma col_le_of_hasOut {w : List (SnakeLetter Q B)} {v : Vtx Q} (h : HasOut w v) :
    v.2 ≤ w.length := by
  obtain ⟨v', o, h⟩ := h; exact edge_col_le_left h

lemma col_le_of_hasIn {w : List (SnakeLetter Q B)} {v : Vtx Q} (h : HasIn w v) :
    v.2 ≤ w.length := by
  obtain ⟨u, o, h⟩ := h; exact edge_col_le_right h

lemma col_le_of_incident {w : List (SnakeLetter Q B)} {v : Vtx Q} (h : Incident w v) :
    v.2 ≤ w.length := by
  rcases h with h | h
  · exact col_le_of_hasOut h
  · exact col_le_of_hasIn h

/-! ## Snake graphs: all edges on a single directed path -/

/-- **All the edges of the graph represented by `w` lie on a single directed path**: `p 0, …, p m`
is a directed path whose vertices are pairwise distinct, `lab t` is the label of its `t`-th edge,
and every edge of the graph is an edge of the path.  This is the book's definition of a snake
graph. -/
structure IsSnakePath (w : List (SnakeLetter Q B)) (m : ℕ) (p : ℕ → Vtx Q)
    (lab : ℕ → Option B) : Prop where
  /-- Consecutive vertices of the path are joined by an edge with the recorded label. -/
  edge : ∀ t < m, Edge w (p t) (p (t + 1)) (lab t)
  /-- The vertices of the path are pairwise distinct. -/
  inj : ∀ s ≤ m, ∀ t ≤ m, p s = p t → s = t
  /-- Every edge of the graph is an edge of the path. -/
  covers : ∀ v v' o, Edge w v v' o → ∃ t < m, p t = v ∧ p (t + 1) = v' ∧ lab t = o

/-- The output along a path: the concatenation of the labels of its edges (the label `none`, the
element of `B + 1` that is not a letter, contributes nothing). -/
def pathOut (lab : ℕ → Option B) (m : ℕ) : List B :=
  ((List.range m).map (fun t => (lab t).toList)).flatten

/-- `w` represents a snake graph. -/
def RepresentsSnake (w : List (SnakeLetter Q B)) : Prop := ∃ m p lab, IsSnakePath w m p lab

/-- `v` is **the output of the snake graph** represented by `w`. -/
def SnakeOutIs (w : List (SnakeLetter Q B)) (v : List B) : Prop :=
  ∃ m p lab, IsSnakePath w m p lab ∧ v = pathOut lab m

/-- The number of times the snake visits the column `i`: the number of vertices of that column that
carry an edge.  (On a snake graph with at least one edge these are exactly the vertices of the
path.) -/
noncomputable def colVisits (w : List (SnakeLetter Q B)) (i : ℕ) : ℕ :=
  {q : Q | Incident w (q, i)}.ncard

/-- **The width of the snake graph is at most `k`**: no column is visited more than `k` times. -/
def SnakeWidthLe (w : List (SnakeLetter Q B)) (k : ℕ) : Prop := ∀ i, colVisits w i ≤ k

open Classical in
/-- **The function of Lemma `lem:output-of-snake-graph-is-regular`**: a string `w` over the alphabet
`C` of snake letters is mapped to the output of the snake graph it represents, if it represents a
snake graph of width at most `k`, and to the empty string otherwise.  The definition uses a choice,
which is legitimate by `SnakeGraph.snakeOutIs_unique`: a string represents at most one output. -/
noncomputable def snakeOut (k : ℕ) (w : List (SnakeLetter Q B)) : List B :=
  if h : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v then h.2.choose else []

/-! ## A string represents at most one output -/

namespace IsSnakePath

variable {w : List (SnakeLetter Q B)} {m : ℕ} {p : ℕ → Vtx Q} {lab : ℕ → Option B}

/-- On a snake graph, a vertex has at most one outgoing edge. -/
lemma outUnique (h : IsSnakePath w m p lab) {v v₁ v₂ : Vtx Q} {o₁ o₂ : Option B}
    (h₁ : Edge w v v₁ o₁) (h₂ : Edge w v v₂ o₂) : v₁ = v₂ ∧ o₁ = o₂ := by
  obtain ⟨t₁, ht₁, hp₁, hq₁, hl₁⟩ := h.covers _ _ _ h₁
  obtain ⟨t₂, ht₂, hp₂, hq₂, hl₂⟩ := h.covers _ _ _ h₂
  have : t₁ = t₂ := h.inj t₁ (le_of_lt ht₁) t₂ (le_of_lt ht₂) (by rw [hp₁, hp₂])
  subst this
  exact ⟨by rw [← hq₁, hq₂], by rw [← hl₁, hl₂]⟩

/-- On a snake graph, a vertex has at most one incoming edge. -/
lemma inUnique (h : IsSnakePath w m p lab) {u₁ u₂ v : Vtx Q} {o₁ o₂ : Option B}
    (h₁ : Edge w u₁ v o₁) (h₂ : Edge w u₂ v o₂) : u₁ = u₂ ∧ o₁ = o₂ := by
  obtain ⟨t₁, ht₁, hp₁, hq₁, hl₁⟩ := h.covers _ _ _ h₁
  obtain ⟨t₂, ht₂, hp₂, hq₂, hl₂⟩ := h.covers _ _ _ h₂
  have : t₁ + 1 = t₂ + 1 := h.inj (t₁ + 1) (by omega) (t₂ + 1) (by omega) (by rw [hq₁, hq₂])
  have ht : t₁ = t₂ := by omega
  subst ht
  exact ⟨by rw [← hp₁, hp₂], by rw [← hl₁, hl₂]⟩

/-- The first vertex of the path has no incoming edge. -/
lemma no_hasIn_zero (h : IsSnakePath w m p lab) : ¬ HasIn w (p 0) := by
  rintro ⟨u, o, hu⟩
  obtain ⟨t, ht, hp, hq, -⟩ := h.covers _ _ _ hu
  have : t + 1 = 0 := h.inj (t + 1) (by omega) 0 (by omega) hq
  omega

/-- The last vertex of the path has no outgoing edge. -/
lemma no_hasOut_last (h : IsSnakePath w m p lab) : ¬ HasOut w (p m) := by
  rintro ⟨v', o, hv⟩
  obtain ⟨t, ht, hp, -, -⟩ := h.covers _ _ _ hv
  have : t = m := h.inj t (by omega) m (by omega) hp
  omega

/-- Every vertex of the path other than the first one has an incoming edge. -/
lemma hasIn_succ (h : IsSnakePath w m p lab) {t : ℕ} (ht : t < m) : HasIn w (p (t + 1)) :=
  ⟨p t, lab t, h.edge t ht⟩

/-- Every vertex of the path other than the last one has an outgoing edge. -/
lemma hasOut_of_lt (h : IsSnakePath w m p lab) {t : ℕ} (ht : t < m) : HasOut w (p t) :=
  ⟨p (t + 1), lab t, h.edge t ht⟩

/-- A vertex reachable from `v` along the graph is a later vertex of the path. -/
lemma transGen_index (h : IsSnakePath w m p lab) {v v' : Vtx Q}
    (hr : Relation.TransGen (EdgeRel w) v v') :
    ∃ s t, s < t ∧ t ≤ m ∧ p s = v ∧ p t = v' := by
  induction hr with
  | single hvv =>
      obtain ⟨o, ho⟩ := hvv
      obtain ⟨t, ht, hp, hq, -⟩ := h.covers _ _ _ ho
      exact ⟨t, t + 1, by omega, by omega, hp, hq⟩
  | tail hxy hyz ih =>
      obtain ⟨s, t, hst, htm, hps, hpt⟩ := ih
      obtain ⟨o, ho⟩ := hyz
      obtain ⟨t', ht', hp', hq', -⟩ := h.covers _ _ _ ho
      have htt : t' = t := h.inj t' (by omega) t htm (by rw [hp', hpt])
      subst htt
      exact ⟨s, t' + 1, by omega, by omega, hps, hq'⟩

/-- A snake graph has no directed cycle. -/
lemma acyclic (h : IsSnakePath w m p lab) (v : Vtx Q) : ¬ Relation.TransGen (EdgeRel w) v v := by
  intro hv
  obtain ⟨s, t, hst, htm, hps, hpt⟩ := h.transGen_index hv
  have : s = t := h.inj s (by omega) t htm (by rw [hps, hpt])
  omega

/-- The first vertex of the path is the only possible source of a snake graph. -/
lemma src_eq (h : IsSnakePath w m p lab) {v : Vtx Q} (hv : Src w v) : v = p 0 := by
  obtain ⟨⟨v', o, hvv⟩, hin⟩ := hv
  obtain ⟨t, ht, hp, -, -⟩ := h.covers _ _ _ hvv
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [← hp]
  · exfalso
    refine hin ⟨p (t - 1), lab (t - 1), ?_⟩
    have := h.edge (t - 1) (by omega)
    rwa [show t - 1 + 1 = t by omega, hp] at this

end IsSnakePath

/-- **A string represents at most one snake graph output.**  Two paths that cover all the edges of
the graph coincide, so the output of a snake graph is well defined. -/
theorem snakeOutIs_unique {w : List (SnakeLetter Q B)} {v v' : List B}
    (h : SnakeOutIs w v) (h' : SnakeOutIs w v') : v = v' := by
  obtain ⟨m, p, lab, hp, rfl⟩ := h
  obtain ⟨m', p', lab', hp', rfl⟩ := h'
  -- the two paths have the same first vertex
  have hstart : m = 0 ∨ m' = 0 ∨ p 0 = p' 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl rfl
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · exact Or.inr (Or.inl rfl)
    refine Or.inr (Or.inr ?_)
    have hsrc : Src w (p' 0) := ⟨hp'.hasOut_of_lt hm', hp'.no_hasIn_zero⟩
    exact (hp.src_eq hsrc).symm
  -- if one of the paths is trivial, the graph has no edge and so is the other
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hnoedge : ∀ u u' o, ¬ Edge w u u' o := by
      intro u u' o hu
      obtain ⟨t, ht, -⟩ := hp.covers _ _ _ hu
      omega
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · rfl
    · exact absurd (hp'.edge 0 hm') (hnoedge _ _ _)
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · have hnoedge : ∀ u u' o, ¬ Edge w u u' o := by
      intro u u' o hu
      obtain ⟨t, ht, -⟩ := hp'.covers _ _ _ hu
      omega
    exact absurd (hp.edge 0 hm) (hnoedge _ _ _)
  -- both paths are nontrivial: they agree step by step
  have h0 : p 0 = p' 0 := by
    rcases hstart with h | h | h
    · omega
    · omega
    · exact h
  have key : ∀ t, t ≤ m → t ≤ m' → p t = p' t := by
    intro t
    induction t with
    | zero => intro _ _; exact h0
    | succ t ih =>
        intro ht ht'
        have hpt := ih (by omega) (by omega)
        have he := hp.edge t (by omega)
        have he' := hp'.edge t (by omega)
        rw [hpt] at he
        exact (hp'.outUnique he he').1
  have hlab : ∀ t, t < m → t < m' → lab t = lab' t := by
    intro t ht ht'
    have hpt := key t (by omega) (by omega)
    have he := hp.edge t ht
    have he' := hp'.edge t ht'
    rw [hpt] at he
    exact (hp'.outUnique he he').2
  have hmm : m = m' := by
    by_contra hne
    rcases Nat.lt_or_ge m m' with hlt | hge
    · -- `p m = p' m` has an outgoing edge on the second path but not on the first
      have hpm := key m (by omega) (by omega)
      exact hp.no_hasOut_last ⟨p' (m + 1), lab' m, by rw [hpm]; exact hp'.edge m hlt⟩
    · have hlt : m' < m := by omega
      have hpm := key m' (by omega) (by omega)
      exact hp'.no_hasOut_last ⟨p (m' + 1), lab m', by rw [← hpm]; exact hp.edge m' hlt⟩
  subst hmm
  unfold pathOut
  congr 1
  refine List.map_congr_left ?_
  intro t ht
  rw [List.mem_range] at ht
  rw [hlab t ht ht]

/-- The value of `snakeOut` on a string that represents a snake graph of width at most `k`. -/
lemma snakeOut_eq {k : ℕ} {w : List (SnakeLetter Q B)} {v : List B}
    (hk : SnakeWidthLe w k) (hv : SnakeOutIs w v) : snakeOut k w = v := by
  have h : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v := ⟨hk, ⟨v, hv⟩⟩
  rw [snakeOut, dif_pos h]
  exact snakeOutIs_unique h.2.choose_spec hv

/-- `snakeOut` is empty on the strings that do not represent a snake graph of width at most `k`. -/
lemma snakeOut_of_not {k : ℕ} {w : List (SnakeLetter Q B)}
    (h : ¬ (SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v)) : snakeOut k w = [] := by
  rw [snakeOut, dif_neg h]

end SnakeGraph

end Lax916827Proofs.Transducers
