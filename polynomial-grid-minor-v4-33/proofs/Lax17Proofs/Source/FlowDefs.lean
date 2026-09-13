import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Finite path flows in simple graphs

This file defines the finite path-flow objects used by the Chekuri--Chuzhoy
boosting theorem.  The definitions are deliberately concrete: a flow is a
finite indexed family of oriented simple paths with a nonnegative rational
weight on each path.

The max-flow/min-cut and integrality theorems are exposed separately in
`«statements-and-proofs».FlowContract`; this file contains no external graph-flow
axioms.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [DecidableEq V]

/-- Cut-based `α`-well-linkedness for a terminal set in the whole graph, with
`α` represented as `alphaNum / alphaDen`.

For every partition `X,Y` of the whole finite vertex set, the edge boundary
between the two sides has size at least an `alphaNum / alphaDen` fraction of the
smaller terminal side:

`alphaNum * min |X ∩ T| |Y ∩ T| ≤ alphaDen * |E_G(X,Y)|`.

This is Definition 2.5 of Chekuri--Chuzhoy in scaled natural-number form. -/
def ScaledEdgeWellLinked [Fintype V]
    (G : _root_.SimpleGraph V) (T : Finset V)
    (alphaNum alphaDen : ℕ) : Prop :=
  0 < alphaNum ∧ alphaNum ≤ alphaDen ∧
    ∀ X Y : Finset V, X ∪ Y = (univ : Finset V) → Disjoint X Y →
      alphaNum * min (X ∩ T).card (Y ∩ T).card ≤
        alphaDen * (Section44.edgeBoundary G X Y).card

/-- The rational value of the scaled parameter `alphaDen / alphaNum`, used as
the edge-congestion bound corresponding to an `alphaNum / alphaDen`
well-linked set. -/
noncomputable def scaledCongestion (alphaNum alphaDen : ℕ) : ℚ :=
  (alphaDen : ℚ) / (alphaNum : ℚ)

/-- A finite oriented path flow from `S` to `T`.

Each indexed path is oriented from a vertex of `S` to a vertex of `T`, and has a
nonnegative rational weight. -/
structure OrientedPathFlow
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The finite index type for paths carrying nonzero or zero flow. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The path assigned to each index. -/
  path : Index → GraphPath G
  /-- Each path starts on the source side. -/
  source_mem : ∀ i : Index, (path i).source ∈ S
  /-- Each path ends on the target side. -/
  target_mem : ∀ i : Index, (path i).target ∈ T
  /-- Rational path weights. -/
  weight : Index → ℚ
  /-- Path weights are nonnegative. -/
  weight_nonneg : ∀ i : Index, 0 ≤ weight i

namespace OrientedPathFlow

variable {G : _root_.SimpleGraph V} {S T : Finset V}

instance (F : OrientedPathFlow G S T) : Fintype F.Index := F.indexFintype
instance (F : OrientedPathFlow G S T) : DecidableEq F.Index := F.indexDecidableEq

/-- Total value of a finite path flow. -/
noncomputable def value (F : OrientedPathFlow G S T) : ℚ :=
  ∑ i : F.Index, F.weight i

/-- Total flow whose path starts at `v`. -/
noncomputable def sourceLoad (F : OrientedPathFlow G S T) (v : V) : ℚ :=
  ∑ i : F.Index, if (F.path i).source = v then F.weight i else 0

/-- Total flow whose path ends at `v`. -/
noncomputable def targetLoad (F : OrientedPathFlow G S T) (v : V) : ℚ :=
  ∑ i : F.Index, if (F.path i).target = v then F.weight i else 0

/-- Total flow using an edge. -/
noncomputable def edgeLoad (F : OrientedPathFlow G S T) (e : Sym2 V) : ℚ :=
  ∑ i : F.Index, if e ∈ (F.path i).edgeSet then F.weight i else 0

/-- Total flow using a vertex. -/
noncomputable def vertexLoad (F : OrientedPathFlow G S T) (v : V) : ℚ :=
  ∑ i : F.Index, if v ∈ (F.path i).vertexSet then F.weight i else 0

/-- Total flow using a vertex as a non-endpoint internal vertex. -/
noncomputable def internalVertexLoad (F : OrientedPathFlow G S T) (v : V) : ℚ :=
  ∑ i : F.Index,
    if v ∈ (F.path i).vertexSet ∧ v ≠ (F.path i).source ∧ v ≠ (F.path i).target
    then F.weight i else 0

/-- Edge congestion is at most `η`: every graph edge carries load at most `η`. -/
def EdgeCongestionAtMost (F : OrientedPathFlow G S T) (η : ℚ) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → F.edgeLoad e ≤ η

/-- Vertex congestion is at most `η`: every vertex carries load at most `η`. -/
def VertexCongestionAtMost (F : OrientedPathFlow G S T) (η : ℚ) : Prop :=
  ∀ v : V, F.vertexLoad v ≤ η

/-- Every source terminal sends exactly one unit of flow. -/
def SourceLoadExactlyOne (F : OrientedPathFlow G S T) : Prop :=
  ∀ v ∈ S, F.sourceLoad v = 1

/-- Every target terminal receives exactly one unit of flow. -/
def TargetLoadExactlyOne (F : OrientedPathFlow G S T) : Prop :=
  ∀ v ∈ T, F.targetLoad v = 1

/-- Every target terminal receives at most one unit of flow. -/
def TargetLoadAtMostOne (F : OrientedPathFlow G S T) : Prop :=
  ∀ v ∈ T, F.targetLoad v ≤ 1

/-- The flow is a unit flow from `S` to `T`: each source sends one unit and
each target receives one unit. -/
def IsUnitFlow (F : OrientedPathFlow G S T) : Prop :=
  F.SourceLoadExactlyOne ∧ F.TargetLoadExactlyOne

/-- A valid vertex-capacitated flow of value at least `k`, with unit vertex
capacities. -/
def HasUnitVertexCapacityValueAtLeast
    (G : _root_.SimpleGraph V) (S T : Finset V) (k : ℕ) : Prop :=
  ∃ F : OrientedPathFlow G S T,
    (k : ℚ) ≤ F.value ∧ F.VertexCongestionAtMost 1

end OrientedPathFlow

end SimpleGraph

end Lax17Proofs
