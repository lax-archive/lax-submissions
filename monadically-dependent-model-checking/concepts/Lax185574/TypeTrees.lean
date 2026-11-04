import Lax185574.DistanceLogic
import Mathlib.Data.Fin.VecNotation

/-!
---
title: Type trees and their canonical representation
type: definition
---
Let G be a partial graph, k, q ∈ ℕ and ā a tuple of ℓ vertices. The
*atomic (k, q)-type* atp_{k,q}(ā) is the set of atomic distFO formulas
of distance rank (k, q) with free variables among x₁, …, x_ℓ that ā
satisfies in G. The *(k, q)-type tree* of ā is

  tree_{k,q}(ā) = (atp_{k,q}(ā), 𝓔_{k,q}(ā)),

where 𝓔_{k,0}(ā) = ∅ and, for q ≥ 1,

  𝓔_{k,q}(ā) = {(i, tree_{k+1,q−1}(ā b)) | i ∈ [ℓ], b ∈ V(G),
                 dist(aᵢ, b) ≤ ρ⁺(k+1, q−1)}.

The members of 𝓔_{k,q}(ā) are the *extensions*, and i is the *guard*
of the extension. The number ℓ is the *arity* and (k, q) is the *rank*
of the tree.

Type trees are represented on the RAM in a canonical form, with all sets
sorted and free of duplicates, so that two trees are equal exactly when
their representations are. The size ‖τ‖ of a tree is the size of its
representation, which includes k, q and ℓ.

For a type tree ν of arity one, [ν]^G is the set of vertices b with
tree_{k,q}(b) = ν, where (k, q) is the rank of ν.

# Formalization notes

A type tree is a Lean object of type `TypeTree`. It records its rank
(k, q), its arity ℓ and its root, an element of `Node q ℓ`. A root of
depth 0 is its root label, the finite set of its atoms. A root of depth
q + 1 is its root label together with the finite set of its extensions,
pairs of a guard and a root of depth q and arity ℓ + 1. The trees inside
a tree carry no rank and arity, since these are determined by the
enclosing tree. Equality of type trees in the paper is equality of
these objects.

The canonical representation of a type tree is its encoding, in the
sense of `Lax185574.Encoding`. It is the header k, q, ℓ, followed by the
encoding of the set of atoms of the root and, at depth at least one, the
encoding of the set of extensions. An atom is encoded as a formula of
`Lax185574.DistanceLogic`, and an extension (i, μ) by i followed by the
encoding of μ. Finite sets are encoded sorted and without repetitions,
so the encoding is determined by the tree. The size ‖τ‖ is the length of
the encoding, `wordLength τ`. The operations of the paper are computed
by word RAM programs on these encodings.

The algorithms of the model-checking procedure receive and return the
family (tree_{k,q}(a) : a ∈ V(G)) of the type trees of all vertices of a
partial graph on `Fin n`. It is `family G k q`, a function on `Fin n`,
encoded as the list of its members in the order of the vertices.

Sets are turned into finite sets by `finsetOf`. On an infinite set it
returns the empty set. This case does not occur for partial graphs on a
finite vertex type, where all the sets involved are finite. In
particular, only finitely many colors occur, and an atom with a color
that does not occur is false.
-/

namespace Lax185574.TypeTrees

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.Encoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax3.DistFO (rhoMinus rhoPlus)

/-- `Node q ℓ`: the roots of the type trees of depth `q` and arity `ℓ`.
A root of depth `0` is its set of atoms. A root of depth `q + 1` is its
set of atoms together with its set of extensions, pairs of a guard and
a root of depth `q` and arity `ℓ + 1`. -/
def Node : ℕ → ℕ → Type
  | 0, ℓ => Finset (DistFO ℓ)
  | q + 1, ℓ => Finset (DistFO ℓ) × Finset (Fin ℓ × Node q (ℓ + 1))

/-- A root of depth `0` is encoded by its set of atoms. A root of depth
`q + 1` is encoded by its set of atoms followed by its set of
extensions. `Node` is defined by recursion on the depth and is not an
inductive type, so its encoding is given by the same recursion. -/
@[instance_reducible] def Node.instEncode : (q ℓ : ℕ) → Encode (Node q ℓ)
  | 0, ℓ => inferInstanceAs (Encode (Finset (DistFO ℓ)))
  | q + 1, ℓ =>
      letI := Node.instEncode q (ℓ + 1)
      inferInstanceAs (Encode (Finset (DistFO ℓ) × Finset (Fin ℓ × Node q (ℓ + 1))))

instance {q ℓ : ℕ} : Encode (Node q ℓ) := Node.instEncode q ℓ

/-- A type tree: its rank `(k, q)`, its arity `ℓ` and its root. -/
structure TypeTree where
  /-- The first component of the rank. -/
  k : ℕ
  /-- The depth, the second component of the rank. -/
  q : ℕ
  /-- The arity. -/
  ℓ : ℕ
  /-- The root. -/
  root : Node q ℓ
  deriving Encode

variable {V : Type*}

/-- The finite set with the elements of `S`, and `∅` if `S` is
infinite. -/
noncomputable def finsetOf {α : Type*} (S : Set α) : Finset α :=
  open Classical in if h : S.Finite then h.toFinset else ∅

/-- `atp_{k,q}(a)`: the atoms of distance rank `(k, q)` satisfied by the
tuple `a`. -/
def atp (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) : Set (DistFO ℓ) :=
  {φ | IsAtom φ ∧ DRank k q φ ∧ Sat G a φ}

/-- The root of `tree_{k,q}(a)`: the atoms of `atp_{k,q}(a)` and, for
`q ≥ 1`, the extensions `(i, tree_{k+1,q−1}(a b))`. -/
noncomputable def node (G : PartialGraph V) : (k q : ℕ) → {ℓ : ℕ} → (Fin ℓ → V) → Node q ℓ
  | k, 0, _, a => finsetOf (atp G k 0 a)
  | k, q + 1, ℓ, a =>
      (finsetOf (atp G k (q + 1) a),
       finsetOf {e | ∃ (i : Fin ℓ) (b : V),
          WithinDist G.resolved (rhoPlus (k + 1) q) (a i) b ∧
          e = (i, node G (k + 1) q (Fin.snoc a b))})

/-- `tree_{k,q}(a)`. -/
noncomputable def tree (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) : TypeTree :=
  ⟨k, q, ℓ, node G k q a⟩

/-- `[ν]^G`: the vertices whose type tree is `ν`. The rank is read off
`ν`, which records it. -/
def realizations (G : PartialGraph V) (ν : TypeTree) : Set V :=
  {b | tree G ν.k ν.q ![b] = ν}

/-- The family `(tree_{k,q}(a) : a ∈ V(G))` of the type trees of all
vertices. -/
noncomputable def family {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) : Fin n → TypeTree :=
  fun a => tree G k q ![a]

/-- The largest size of a tree of the family. -/
noncomputable def maxTreeSize {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) : ℕ :=
  Finset.univ.sup fun a : Fin n => wordLength (family G k q a)

end Lax185574.TypeTrees
