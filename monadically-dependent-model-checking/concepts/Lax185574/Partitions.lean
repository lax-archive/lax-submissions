import Lax185574.Encodings
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic

/-!
---
title: Partitions, transversals and the partition into atomic types
type: definition
---
For two partitions 𝒫, 𝒬 of the same set, 𝒫 ≼ 𝒬 says that 𝒫 refines 𝒬,
that is, each part of 𝒫 is contained in some part of 𝒬. For a partition
𝒫 of V and X ⊆ V, X/𝒫 is the set of parts of 𝒫 that meet X. The part of
𝒫 containing an element v is 𝒫(v). Further, ≡_𝒫 is the equivalence
relation on V whose classes are the parts of 𝒫. A *transversal* of 𝒫 is
a set that contains exactly one vertex of every part.

For a graph G and S ⊆ V(G), two vertices u, v have the same atomic type
over S if and only if either u = v, or u, v ∉ S and N(u) ∩ S = N(v) ∩ S.
The *partition into atomic types* 𝒫_S partitions S into singletons and
the vertices of V(G) ∖ S according to their neighborhoods in S.

# Formalization notes

A partition of V is an equivalence relation on V, a `Setoid V`. Its
parts are the equivalence classes, so ≡_𝒫 is the relation itself and
𝒫 ≼ 𝒬 is the order `P ≤ Q` of setoids. The partition into singletons is
`⊥`, and the partition with one part is `⊤`. The number |X/𝒫| is the
number of classes of elements of X, `partCount`. It is the exact count
on a finite vertex type, which is the case in every statement that uses
it.

The partition into atomic types is the kernel of the map
v ↦ (S ∩ {v}, S ∩ N(v)). Two vertices have the same image exactly when
they are equal, or both lie outside S and have the same neighborhood in
S. So this is the partition of the paper. It is also the partition
into types of quantifier rank 0 over S in the sense of
`Lax185574.FirstOrderTypes`, which the paper mentions as the definition.

Algorithms exchange partitions of `Fin n` as the finite set of their
parts, each part a finite set of vertices, in the encodings of
`Lax185574.Encodings`. This is the instance below.
-/

namespace Lax185574.Partitions

open Lax185574.Encoding

universe z

variable {V : Type z}

/-- `|X/𝒫|`: the number of parts of `P` that meet `X`. -/
noncomputable def partCount (P : Setoid V) (X : Set V) : ℕ :=
  (Quotient.mk P '' X).ncard

/-- The part `𝒫(v)` of `P` that contains `v`. -/
def part (P : Setoid V) (v : V) : Set V := {u | P u v}

/-- `T` is a transversal of `P`: every part of `P` contains exactly one
vertex of `T`. -/
def IsTransversal (P : Setoid V) (T : Set V) : Prop :=
  ∀ v : V, ∃! t : V, t ∈ T ∧ P t v

/-- The partition `𝒫_S` into atomic types over `S`: vertices of `S` are
singletons, and vertices outside `S` are grouped by their neighborhood
in `S`. -/
def atomicTypes (G : SimpleGraph V) (S : Set V) : Setoid V :=
  Setoid.ker fun v => (S ∩ {v}, S ∩ G.neighborSet v)

/-- The parts of a partition of `Fin n`, as a finite set of finite
sets. -/
noncomputable def parts {n : ℕ} (P : Setoid (Fin n)) : Finset (Finset (Fin n)) :=
  open Classical in Finset.univ.image fun v => Finset.univ.filter fun u => P u v

/-- A partition of `Fin n` is encoded by the finite set of its parts.
A setoid is a relation, so the encoding is not derived. -/
noncomputable instance {n : ℕ} : Encode (Setoid (Fin n)) where
  encode P := encode (parts P)

end Lax185574.Partitions
