import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym

/-!
---
title: Paths, linkages, and separators
type: definition
---
A path is a simple finite walk with named endpoints.  A vertex linkage is an
indexed family of paths joining two terminal sets whose vertex sets are
pairwise disjoint; an edge linkage asks instead that their edge sets be
pairwise disjoint.  Vertex and edge separators are finite sets meeting every
path between the terminal sets.

All endpoint conventions are oriented.  Reversing every path gives the
corresponding unoriented formulation.
-/

namespace Lax17.Paths

universe u

/-- A simple finite path in `G`, with its orientation recorded. -/
structure Path {V : Type u} (G : SimpleGraph V) where
  source : V
  target : V
  walk : G.Walk source target
  simple : walk.IsPath

namespace Path

/-- The finite set of vertices used by a path. -/
noncomputable def vertices {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset V :=
  P.walk.support.toFinset

/-- The finite set of edges used by a path. -/
noncomputable def edges {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

/-- Every vertex of `P` lies in `C`. -/
def StaysIn {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (C : Finset V) : Prop :=
  P.vertices ⊆ C

/-- The internal vertices of `P` avoid `X`. -/
def InternallyAvoids {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (X : Finset V) : Prop :=
  ∀ v ∈ P.vertices, v ∈ X → v = P.source ∨ v = P.target

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

/-- Exactly `k` pairwise edge-disjoint paths oriented from `A` to `B`. -/
structure EdgeLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  edge_disjoint :
    Pairwise fun i j => Disjoint (path i).edges (path j).edges

/-- A path joining two members of a linkage whose internal vertices avoid
every path of that linkage. -/
structure VertexLinkage.BridgeBetween
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V} {k : ℕ}
    (P : VertexLinkage G A B k) (i j : Fin k) where
  path : Path G
  source_on_first : path.source ∈ (P.path i).vertices
  target_on_second : path.target ∈ (P.path j).vertices
  internally_avoids_rows :
    ∀ r : Fin k, path.InternallyAvoids (P.path r).vertices

/-- Every two distinct paths of the linkage have a bridge contained in `C`. -/
def VertexLinkage.HasPairwiseBridgesIn
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V} {k : ℕ}
    (P : VertexLinkage G A B k) (C : Finset V) : Prop :=
  ∀ ⦃i j : Fin k⦄, i ≠ j →
    ∃ bridge : P.BridgeBetween i j, bridge.path.StaysIn C

/-- Edges of `G` with one endpoint in `X` and the other in `Y`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V)
    (fun e => e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    (Classical.decPred fun e =>
      e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    Finset.univ

/-- A partition of `C` separating `A` from `B` by fewer than `k` edges. -/
structure EdgeCutPartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) (k : ℕ) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = C
  disjoint : Disjoint left right
  left_terminals : A ⊆ left
  right_terminals : B ⊆ right
  boundary_small : (edgeBoundary G left right).card < k

/-- A vertex set meeting every oriented `A`-to-`B` path. -/
def IsVertexSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ v ∈ P.vertices, v ∈ X

/-- An edge set meeting every oriented `A`-to-`B` path. -/
def IsEdgeSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (F : Finset (Sym2 V)) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ e ∈ P.edges, e ∈ F

end Lax17.Paths
