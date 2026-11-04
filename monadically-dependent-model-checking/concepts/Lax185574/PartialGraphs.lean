import Lax185574.GaifmanGraph
import Lax185574.Encodings
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

/-!
---
title: Partial graphs
type: definition
---
A *partial graph* H consists of a finite vertex set V = V(H), two
disjoint sets E(H), N(H) ⊆ (V choose 2) of *edges* and *non-edges*, and
a partition of V whose parts are treated as colors. The pairs in
R(H) = E(H) ∪ N(H) are *resolved*, and all other pairs are
*unresolved*. H is viewed as a logical structure with binary relations E
and N and a unary predicate for every color. Distances dist^H and balls
Ball^H_r(v) are measured in the Gaifman graph (V, R(H)), the graph of
resolved pairs.

For the model-checking algorithm, the parts are given names, to track
them over time. Fix a countably infinite set of unary symbols, called
*colors*. A partial graph G is regarded as a relational structure with
the two symmetric binary relations E and N and a unary relation Y for
every color Y. The vertices of color Y form its *color class* Y^G, and
the nonempty color classes are the *parts* of G. The size of the
representation of G is given by |G| = |V(G)| and
‖G‖ = |V(G)| + |R(G)|.

# Formalization notes

The paper introduces partial graphs in the technical overview and
extends the notion in the preliminaries of the model-checking part. Both
passages describe the same objects. All metric notions count resolved
pairs, edges and non-edges alike.

Colors are natural numbers. Edges and non-edges are simple graphs on the
vertex type, so they are symmetric and irreflexive by construction, and
a resolved pair is an edge of their supremum. The language of partial
graphs has the two binary symbols and one unary symbol per natural
number. Its Gaifman graph is exactly the graph of resolved pairs. That
graph is what `ball` uses, so `ball` agrees with
`Lax185574.GaifmanGraph.ball` on the structure of a partial graph.

The induced partial graph G[X], defined in the paper together with
`Lax185574.ConstructionWidth`, is the induced substructure of
`Lax185574.GaifmanGraph`, applied to the structure of G. Statements
about G[X] do not use this substructure. They are stated through the
partial graph G and the set X, see `Lax185574.LocalDefinability`, and
need no separate definition.

For a partial graph on `Fin n`, |G| is `n`. The size ‖G‖ =
|V(G)| + |R(G)|, used in running-time bounds, is `PartialGraph.size`.

The distance matrix D_G of a partial graph, with entries
D_G(u, v) = dist^G(u, v) ∈ ℕ ∪ {∞}, is `Lax185574.DistanceMatrix`. It is
∞ for vertices in different components of the graph of resolved pairs.
The algorithms of the model-checking procedure receive it as an
additional input, and maintain it along the construction sequence.
-/

namespace Lax185574.PartialGraphs

open FirstOrder FirstOrder.Language
open Lax185574.GaifmanGraph

universe z

/-- A partial graph on the vertex type `V`: disjoint edges and
non-edges, and one color per vertex. -/
structure PartialGraph (V : Type z) where
  /-- The edges `E(G)`. -/
  edge : SimpleGraph V
  /-- The non-edges `N(G)`. -/
  nonEdge : SimpleGraph V
  /-- No pair is both an edge and a non-edge. -/
  disjoint : Disjoint edge nonEdge
  /-- The color of each vertex. -/
  color : V → ℕ

variable {V : Type z}

namespace PartialGraph

/-- The resolved pairs `R(G) = E(G) ∪ N(G)`, the Gaifman graph of the
partial graph. -/
def resolved (G : PartialGraph V) : SimpleGraph V := G.edge ⊔ G.nonEdge

/-- `Ball^G_r(v)`: the vertices within distance `r` of `v` along
resolved pairs. -/
def ball (G : PartialGraph V) (r : ℕ) (v : V) : Set V :=
  {u | WithinDist G.resolved r v u}

/-- The color class `Y^G`. -/
def colorClass (G : PartialGraph V) (Y : ℕ) : Set V := {v | G.color v = Y}

/-- The size `‖G‖ = |V(G)| + |R(G)|` of a partial graph on `Fin n`. -/
noncomputable def size {n : ℕ} (G : PartialGraph (Fin n)) : ℕ :=
  n + Set.ncard G.resolved.edgeSet

end PartialGraph

/-- The relation symbols of partial graphs: edges, non-edges and one
unary symbol per color. -/
inductive Rel : ℕ → Type
  | edge : Rel 2
  | nonEdge : Rel 2
  | color (Y : ℕ) : Rel 1

/-- The language of partial graphs. -/
def language : Language :=
  ⟨fun _ => Empty, Rel⟩
  deriving Language.IsRelational

/-- A partial graph as a relational structure. -/
@[implicit_reducible]
def PartialGraph.structure (G : PartialGraph V) : language.Structure V where
  funMap f := isEmptyElim f
  RelMap
    | .edge => fun x => G.edge.Adj (x 0) (x 1)
    | .nonEdge => fun x => G.nonEdge.Adj (x 0) (x 1)
    | .color Y => fun x => G.color (x 0) = Y

open Lax185574.Encoding in
/-- A partial graph on `Fin n` is encoded by the family of its colors,
then its edges and then its non-edges, each graph as in
`Lax185574.Encodings`. So the encoding is `n` and the `n` colors, then
`n` and for every vertex in order the set of its neighbors along edges,
then `n` and for every vertex the set of its neighbors along non-edges.
It is determined by the partial graph and has length O(‖G‖). Running
times are stated in terms of ‖G‖, which is only meaningful for an
encoding without padding. The edges and non-edges are relations, so the
encoding is not derived. -/
noncomputable instance {n : ℕ} : Encode (PartialGraph (Fin n)) where
  encode G := encode (G.color, G.edge, G.nonEdge)

end Lax185574.PartialGraphs
