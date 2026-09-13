import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Lax17.Degree

/-!
---
title: Edge expansion and cut-matching transcripts
type: definition
---
The edge boundary of a vertex set consists of the graph edges with exactly one
endpoint in the set.  A finite graph is an \((a/b)\)-edge-expander when every
set containing at most half of the vertices has boundary at least
\((a/b)\) times its size.

A cut-matching transcript is a finite list of perfect matchings across
bisections.  Its boundary count retains the round of each matching edge, so
parallel copies contributed in different rounds are counted separately.
-/

namespace Lax17.Expansion

universe u

open Lax17.Degree

/-- An unordered pair crosses the vertex set `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ x y : V, e = s(x, y) ∧
    ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S))

/-- The finite edge boundary of `S`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V)
    (fun e => e ∈ G.edgeSet ∧ Crosses S e)
    (Classical.decPred _)
    Finset.univ

/-- Every set of at most half the vertices expands by a factor of `a / b`. -/
def IsEdgeExpander {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧
    ∀ S : Finset V, 0 < S.card → 2 * S.card ≤ Fintype.card V →
      b * (edgeBoundary G S).card ≥ a * S.card

/-- A balanced vertex separator `A ∪ B ∪ S = V`, oriented so that `A` is
the smaller side and both large sides have size at most two thirds of the
graph. -/
structure BalancedSeparator {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B S : Finset V) : Prop where
  cover : A ∪ B ∪ S = Finset.univ
  left_right_disjoint : Disjoint A B
  left_separator_disjoint : Disjoint A S
  right_separator_disjoint : Disjoint B S
  left_card_le_right_card : A.card ≤ B.card
  right_balanced : 3 * B.card ≤ 2 * Fintype.card V
  no_edge_left_right :
    ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ¬ G.Adj a b

/-- Every balanced separator has size at least `|V| / d`, expressed without
division. -/
def NoSmallBalancedSeparator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ ⦃A B S : Finset V⦄, BalancedSeparator G A B S →
    Fintype.card V ≤ d * S.card

/-- One cut-matching round: a bisection and a perfect matching from its left
half to its right half. -/
structure MatchingRound (V : Type u) [Fintype V] [DecidableEq V] where
  left : Finset V
  right : Finset V
  sides_disjoint : Disjoint left right
  sides_equipotent : left.card = right.card
  sides_cover : left ∪ right = Finset.univ
  partner : {x : V // x ∈ left} ≃ {x : V // x ∈ right}

namespace MatchingRound

/-- Whether the matching edge starting at `x` crosses `S`. -/
def Crosses {V : Type u} [Fintype V] [DecidableEq V]
    (R : MatchingRound V) (S : Finset V)
    (x : {x : V // x ∈ R.left}) : Prop :=
  (x.1 ∈ S ∧ (R.partner x).1 ∉ S) ∨
    ((R.partner x).1 ∈ S ∧ x.1 ∉ S)

/-- Matching edges of one round that cross `S`, indexed by their endpoint on
the left side of the bisection. -/
noncomputable def boundary {V : Type u} [Fintype V] [DecidableEq V]
    (R : MatchingRound V) (S : Finset V) :
    Finset {x : V // x ∈ R.left} :=
  @Finset.filter {x : V // x ∈ R.left}
    (R.Crosses S) (Classical.decPred _) Finset.univ

end MatchingRound

/-- A finite cut-matching transcript. -/
abbrev CutMatchingTranscript (V : Type u) [Fintype V] [DecidableEq V] :=
  List (MatchingRound V)

namespace CutMatchingTranscript

/-- Number of matching-edge instances crossing `S`; edges from different
rounds are counted with multiplicity. -/
noncomputable def edgeBoundaryCount {V : Type u} [Fintype V] [DecidableEq V]
    (T : CutMatchingTranscript V) (S : Finset V) : ℕ :=
  (T.map fun R => (R.boundary S).card).sum

/-- Every nonempty set of at most half the vertices has at least half as many
crossing matching-edge instances as vertices. -/
def IsHalfEdgeExpander {V : Type u} [Fintype V] [DecidableEq V]
    (T : CutMatchingTranscript V) : Prop :=
  ∀ S : Finset V, 0 < S.card → 2 * S.card ≤ Fintype.card V →
    S.card ≤ 2 * T.edgeBoundaryCount S

end CutMatchingTranscript

end Lax17.Expansion
