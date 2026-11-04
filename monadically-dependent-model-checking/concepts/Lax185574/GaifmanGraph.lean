import Mathlib.ModelTheory.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Gaifman graph, distances, balls and induced substructures
type: definition
---
The *Gaifman graph* of a relational structure A with domain V has
vertex set V. Two distinct elements are adjacent if they occur together
in some tuple of some relation of A. For a structure with unary and
binary relations, these are the pairs uv such that (u, v) or (v, u) lies
in a binary relation. The distance dist^A(u, v) is the distance in the
Gaifman graph, and Ball^A_r(ā) is the set of elements at distance at
most r from some entry of the tuple ā.

For a set B of elements of a relational structure A, the *induced
substructure* A[B] has domain B, and each relation of A is restricted
to B. The paper uses A[B] without defining it.

# Formalization notes

"At distance at most r" is witnessed by a walk of length at most r, as
in `Lax3.ColoredGraphs`. Elements in different components are therefore
at infinite distance. The induced substructure is defined for relational
languages, where every subset is closed under the (absent) functions.
Its domain is the subtype of `B`.
-/

namespace Lax185574.GaifmanGraph

open FirstOrder FirstOrder.Language

universe u v z

variable {L : Language.{u, v}} {V : Type z} [L.Structure V]

variable (L) in
/-- The Gaifman graph: distinct elements are adjacent if they occur
together in a tuple of some relation. -/
def gaifmanGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun a b =>
    ∃ (l : ℕ) (R : L.Relations l) (x : Fin l → V),
      Structure.RelMap R x ∧ a ∈ Set.range x ∧ b ∈ Set.range x

/-- The vertices `u` and `v` of the graph `G` are within distance `d`:
some walk from `u` to `v` has length at most `d`. -/
def WithinDist {W : Type*} (G : SimpleGraph W) (d : ℕ) (u v : W) : Prop :=
  ∃ p : G.Walk u v, p.length ≤ d

variable (L) in
/-- `Ball^A_r(ā)`: the elements within distance `r` of some entry of the
tuple `a` in the Gaifman graph. -/
def ball (r : ℕ) {k : ℕ} (a : Fin k → V) : Set V :=
  {b | ∃ i, WithinDist (gaifmanGraph L (V := V)) r (a i) b}

/-- The induced substructure `A[B]` of a relational structure: the
relations of `A`, restricted to `B`. -/
@[implicit_reducible]
def induced [L.IsRelational] (B : Set V) : L.Structure B where
  funMap f := isEmptyElim f
  RelMap R x := Structure.RelMap R (fun i => (x i : V))

end Lax185574.GaifmanGraph
