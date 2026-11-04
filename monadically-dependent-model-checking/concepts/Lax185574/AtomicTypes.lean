import Lax185574.FirstOrderTypes
import Mathlib.ModelTheory.Graph

/-!
---
title: Atomic types of vertices and of pairs
type: definition
---
The *atomic type* of a tuple v̄ over a set Y of elements of a structure A
is atp^A(v̄/Y) ≔ tp^A_0(v̄/Y), and ATypes^A(X/Y) ≔ Types^A_{1,0}(X/Y) is
the set of atomic types over Y of the elements of X.

For a graph, Π = {(x = y), (x ≠ y) ∧ E(x, y), (x ≠ y) ∧ ¬E(x, y)} is the
set of the three possible atomic types of a pair of vertices. For an
s-tuple p̄ = (p₁, …, p_s) of vertices and a vertex v, the atomic type
atp(v/p̄) is identified with the s-tuple in Π^s whose i-th component is
the atomic type of the pair (v, pᵢ).

# Formalization notes

The number |ATypes^G(X/Y)| is `atomicTypeCount`. It is literally the
number of types of quantifier rank 0 of single vertices of X over Y in
the structure of the graph G, as defined in `FirstOrderTypes`.

The three atomic types of a pair form the type `PairType`, and
atp(v/p̄) is `atomicTypeOver G p v`. The partition 𝒫_S of V(G) into
atomic types over a set S is `Partitions.atomicTypes`. Two vertices have
the same atomic type over a tuple p̄ exactly when they lie in the same
part of 𝒫_S for the set S of entries of p̄.
-/

namespace Lax185574.AtomicTypes

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes

universe u

variable {V : Type u}

/-- `|ATypes^G(X/Y)|`: the number of atomic types over `Y`, in the graph
`G`, of the vertices of `X`. -/
noncomputable def atomicTypeCount (G : SimpleGraph V) (X Y : Set V) : ℕ :=
  @typeCountOver Language.graph V G.structure 1 0 X Y

/-- The three atomic types of a pair of vertices in a graph, the set Π. -/
inductive PairType
  /-- The type `x = y`. -/
  | eq
  /-- The type `x ≠ y ∧ E(x, y)`. -/
  | adj
  /-- The type `x ≠ y ∧ ¬E(x, y)`. -/
  | nonAdj
  deriving DecidableEq

/-- There are three atomic types of pairs. -/
instance : Fintype PairType :=
  ⟨{.eq, .adj, .nonAdj}, fun x => by cases x <;> decide⟩

open Classical in
/-- The atomic type of the pair `(u, v)` in the graph `G`. -/
noncomputable def pairType (G : SimpleGraph V) (u v : V) : PairType :=
  if u = v then .eq else if G.Adj u v then .adj else .nonAdj

/-- `atp(v/p̄)`, as an element of `Π^s`: its `i`-th component is the
atomic type of the pair `(v, pᵢ)`. -/
noncomputable def atomicTypeOver (G : SimpleGraph V) {s : ℕ} (p : Fin s → V)
    (v : V) : Fin s → PairType :=
  fun i => pairType G v (p i)

end Lax185574.AtomicTypes
