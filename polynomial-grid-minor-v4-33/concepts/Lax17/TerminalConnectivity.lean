import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum

/-!
---
title: Terminal element connectivity and split-off operations
type: definition
---
A finite edge-indexed graph is a loopless undirected multigraph whose parallel
edge copies retain distinct names.  Terminal element connectivity counts a
separator made from nonterminal vertices and edge copies.  Deletion removes
one named edge; contraction identifies its endpoints and discards resulting
loops; splitting off two edges at a centre replaces them by an edge between
their other endpoints, discarding that edge when it would be a loop.

These definitions are the natural multigraph language for the
Hind--Oellermann and Mader reductions used in the grid-minor proof.
-/

namespace Lax17.TerminalConnectivity

universe u v

/-- A finite loopless undirected multigraph with named edge copies. -/
structure EdgeIndexedGraph (V : Type u) where
  Edge : Type
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge → V
  right : Edge → V
  end_ne : ∀ e : Edge, left e ≠ right e

namespace EdgeIndexedGraph

instance {V : Type u} (H : EdgeIndexedGraph V) : Fintype H.Edge :=
  H.edgeFintype

instance {V : Type u} (H : EdgeIndexedGraph V) : DecidableEq H.Edge :=
  H.edgeDecidableEq

/-- Named edge copies incident with `x`. -/
def incidentEdges {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (x : V) : Finset H.Edge :=
  Finset.univ.filter fun e => H.left e = x ∨ H.right e = x

/-- Degree, counting parallel copies separately. -/
def degree {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (x : V) : ℕ :=
  (H.incidentEdges x).card

/-- A named edge has exactly one endpoint in `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) (e : H.Edge) : Prop :=
  (H.left e ∈ S ∧ H.right e ∉ S) ∨
    (H.right e ∈ S ∧ H.left e ∉ S)

/-- The named edge boundary of `S`. -/
noncomputable def boundary {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) : Finset H.Edge :=
  @Finset.filter H.Edge (H.Crosses S) (Classical.decPred _) Finset.univ

/-- Boundary edges whose endpoints survive deletion of `removed`. -/
noncomputable def availableBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (removed S : Finset V) : Finset H.Edge :=
  (H.boundary S).filter fun e =>
    H.left e ∉ removed ∧ H.right e ∉ removed

/-- A terminal-separating cut made from nonterminal vertices and named edge
copies. -/
structure ElementCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (terminals : Finset V) (a b : V) where
  removedVertices : Finset V
  removedVertices_nonterminal : Disjoint removedVertices terminals
  removedEdges : Finset H.Edge
  side : Finset V
  source_mem : a ∈ side
  target_not_mem : b ∉ side
  side_disjoint_removed : Disjoint side removedVertices
  crossing_removed :
    ∀ e : H.Edge,
      H.left e ∉ removedVertices →
        H.right e ∉ removedVertices →
          H.Crosses side e →
            e ∈ removedEdges

namespace ElementCut

/-- Number of removed vertices and named edge copies. -/
def order
    {V : Type u} [Fintype V] [DecidableEq V]
    {H : EdgeIndexedGraph V} {terminals : Finset V} {a b : V}
    (C : ElementCut H terminals a b) : ℕ :=
  C.removedVertices.card + C.removedEdges.card

end ElementCut

/-- Every two distinct terminals need at least `k` nonterminal vertices and
edge copies to separate them. -/
def TerminalElementConnectedAtLeast
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (terminals : Finset V) (k : ℕ) : Prop :=
  ∀ ⦃a : V⦄, a ∈ terminals →
    ∀ ⦃b : V⦄, b ∈ terminals → a ≠ b →
      ∀ removed side : Finset V,
        Disjoint removed terminals →
        a ∈ side → b ∉ side → Disjoint side removed →
          k ≤ removed.card + (H.availableBoundary removed side).card

/-- Delete one named edge copy. -/
def deleteEdge {V : Type u} (H : EdgeIndexedGraph V) (e₀ : H.Edge) :
    EdgeIndexedGraph V where
  Edge := {e : H.Edge // e ≠ e₀}
  left e := H.left e.1
  right e := H.right e.1
  end_ne e := H.end_ne e.1

/-- A concrete model of contracting `e₀`.  The vertex map has precisely the
contracted endpoint pair as its only nontrivial fibre, and the target edges
are exactly the surviving non-loop edge copies. -/
structure IsContraction
    {V : Type u} {W : Type v} [DecidableEq W]
    (H : EdgeIndexedGraph V) (e₀ : H.Edge)
    (K : EdgeIndexedGraph W) (mapVertex : V → W) where
  vertex_surjective : Function.Surjective mapVertex
  endpoints_identified :
    mapVertex (H.left e₀) = mapVertex (H.right e₀)
  fibres :
    ∀ ⦃x y : V⦄, mapVertex x = mapVertex y →
      x = y ∨
        (x = H.left e₀ ∧ y = H.right e₀) ∨
        (x = H.right e₀ ∧ y = H.left e₀)
  edgeEquiv :
    {e : H.Edge //
      e ≠ e₀ ∧ mapVertex (H.left e) ≠ mapVertex (H.right e)} ≃ K.Edge
  edge_endpoints :
    ∀ e,
      (K.left (edgeEquiv e) = mapVertex (H.left e.1) ∧
        K.right (edgeEquiv e) = mapVertex (H.right e.1)) ∨
      (K.left (edgeEquiv e) = mapVertex (H.right e.1) ∧
        K.right (edgeEquiv e) = mapVertex (H.left e.1))

/-- Image of the terminal set under a contraction map. -/
def terminalImage {V : Type u} {W : Type v} [DecidableEq W]
    (mapVertex : V → W) (terminals : Finset V) : Finset W :=
  terminals.image mapVertex

/-- Two distinct named edges incident with `s`, with their other endpoints. -/
structure SplitPair {V : Type u} (H : EdgeIndexedGraph V) (s : V) where
  first : H.Edge
  second : H.Edge
  edge_ne : first ≠ second
  firstOther : V
  secondOther : V
  first_ends :
    (H.left first = s ∧ H.right first = firstOther) ∨
      (H.right first = s ∧ H.left first = firstOther)
  second_ends :
    (H.left second = s ∧ H.right second = secondOther) ∨
      (H.right second = s ∧ H.left second = secondOther)

/-- Edge names surviving or created by a split-off.  The right summand is
inhabited exactly when the newly created edge is not a loop. -/
def SplitEdge
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : Type :=
  {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
    {_unit : Unit // p.firstOther ≠ p.secondOther}

noncomputable instance splitEdgeFintype
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : Fintype (SplitEdge p) :=
  letI : Fintype {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype {_unit : Unit // p.firstOther ≠ p.secondOther} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  inferInstanceAs
    (Fintype
      ({e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
        {_unit : Unit // p.firstOther ≠ p.secondOther}))

noncomputable instance splitEdgeDecidableEq
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : DecidableEq (SplitEdge p) :=
  Classical.decEq (SplitEdge p)

/-- Split off a pair of edges at `s`, discarding a newly created loop. -/
noncomputable def splitOff {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) {s : V}
    (p : H.SplitPair s) : EdgeIndexedGraph V where
  Edge := SplitEdge p
  left
    | Sum.inl e => H.left e.1
    | Sum.inr _ => p.firstOther
  right
    | Sum.inl e => H.right e.1
    | Sum.inr _ => p.secondOther
  end_ne
    | Sum.inl e => H.end_ne e.1
    | Sum.inr e => e.2

/-- `u` and `v` cannot be separated by fewer than `k` edge copies. -/
def PairEdgeConnectedAtLeast
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (u v : V) (k : ℕ) : Prop :=
  ∀ S : Finset V, u ∈ S → v ∉ S → k ≤ (H.boundary S).card

/-- Splitting `p` preserves every local edge-connectivity value away from its
centre. -/
def IsMaderAdmissible
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) {s : V} (p : H.SplitPair s) : Prop :=
  ∀ u v : V, u ≠ s → v ≠ s → u ≠ v → ∀ k : ℕ,
    H.PairEdgeConnectedAtLeast u v k ↔
      (H.splitOff p).PairEdgeConnectedAtLeast u v k

/-- A named edge is the whole boundary of some vertex set. -/
def IsNamedCutEdge {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (e : H.Edge) : Prop :=
  ∃ S : Finset V, H.boundary S = {e}

/-- No edge incident with `s` is a named cut edge. -/
def NoIncidentCutEdge {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (s : V) : Prop :=
  ∀ e ∈ H.incidentEdges s, ¬ H.IsNamedCutEdge e

/-- A simple path in an edge-indexed multigraph. -/
structure Path {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (source target : V) where
  length : ℕ
  vertex : Fin (length + 1) → V
  edge : Fin length → H.Edge
  source_eq : vertex 0 = source
  target_eq : vertex (Fin.last length) = target
  edge_ends :
    ∀ i : Fin length,
      (H.left (edge i) = vertex i.castSucc ∧
        H.right (edge i) = vertex i.succ) ∨
      (H.right (edge i) = vertex i.castSucc ∧
        H.left (edge i) = vertex i.succ)
  vertex_injective : Function.Injective vertex

namespace Path

/-- The internal vertices of an edge-indexed path. -/
def internalVertices
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V}
    {source target : V} (P : Path H source target) : Finset V :=
  ((Finset.univ.image P.vertex).erase source).erase target

/-- The named edge copies used by an edge-indexed path. -/
def edgeSet
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V}
    {source target : V} (P : Path H source target) : Finset H.Edge :=
  Finset.univ.image P.edge

end Path

/-- `k` paths from `a` to `b` sharing neither internal vertices nor named
edge copies. -/
structure ElementLinkage
    {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (a b : V) (k : ℕ) where
  path : Fin k → Path H a b
  internal_disjoint :
    Pairwise fun i j =>
      Disjoint (path i).internalVertices (path j).internalVertices
  edge_disjoint :
    Pairwise fun i j =>
      Disjoint (path i).edgeSet (path j).edgeSet

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
