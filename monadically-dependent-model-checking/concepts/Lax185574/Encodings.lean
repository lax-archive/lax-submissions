import Lax185574.Encoding
import Lax185574.FirstOrderLogic
import Lax3.FirstOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ENat.Basic

/-!
---
title: How inputs are given to algorithms
type: definition
---
The encodings of all values that algorithms in this submission read or
write. Except for lists, functions on `Fin n`, finite sets, graphs and
the values of ℕ∞, they are given by the rule of `Lax185574.Encoding`.
Encodings of further types, such as partial graphs and type trees, are
given next to their definitions.

| type | value | encoding |
| --- | --- | --- |
| `Bool` | `false`, `true` | `0`, `1` |
| `Fin n` | `i` | `i` |
| `α × β` | `(a, b)` | encoding of `a`, then of `b` |
| `α ⊕ β` | `inl a`, `inr b` | `0`, encoding of `a`, and `1`, encoding of `b` |
| `Option α` | `none`, `some a` | `0`, and `1`, encoding of `a` |
| `ℤ` | `m ≥ 0`, `-(m + 1)` | `0, m`, and `1, m` |
| `ℚ` | `p / q` in lowest terms, `q > 0` | `p` as an integer, then `q` |
| `ℕ∞` | `d`, `∞` | `d + 1`, and `0` |
| `Empty` | (no values) | |
| `List α` | `[a₁, …, aₘ]` | `m`, then the encodings of `a₁`, …, `aₘ` |
| `Fin n → α` | `f` | the list `[f 0, …, f (n - 1)]` |
| `Finset α` | `S` | the list of the encodings of the elements of `S`, in increasing order |

The encodings of the elements of a finite set are lists of numbers, and
they are compared lexicographically. As a list of lists, the encoding
of a set gives the length of each element's encoding in front of it.

A first-order formula is written in prefix (Polish) notation, with one
number per connective.

| formula | encoding |
| --- | --- |
| xᵢ adjacent to xⱼ | `0, i, j` |
| xᵢ = xⱼ | `1, i, j` |
| ¬φ | `2`, encoding of φ |
| φ ∧ ψ | `3`, encoding of φ, encoding of ψ |
| ∃xₙ φ | `4`, encoding of φ |
| xᵢ has color c | `5`, encoding of `c`, `i` |

The first-order formulas `Lax3.FirstOrder.FO` of the archive, which
have no colors, are encoded in the same way, `0, i, j` for adjacency,
`1, i, j` for equality, and `2`, `3`, `4` for negation, conjunction and
the quantifier.

A graph with n vertices is encoded by the family of the neighborhoods of
its vertices 0, 1, …, n − 1, each a finite set of vertices. So the
encoding starts with n, followed for each vertex by its degree and its
neighbors in increasing order, each neighbor preceded by `1`, the length
of its encoding. A graph with n vertices and m edges has an encoding of
length n + 4m + 1, whose numbers are at most n. A graph of mathlib on
the vertices 0, 1, …, n − 1, a `SimpleGraph (Fin n)`, is encoded in the
same way.

# Formalization notes

The tables are not part of the definition. They spell out what the
instances below and `deriving Encode` write for these declarations.

The adjacency of a graph is a relation, so the encoding of a graph is not
derived. A number or ∞ takes one entry, so that a matrix of distances
has entries of constant size. Its derived encoding, as an optional
number, would take two entries for a finite value. Every finite set has exactly one encoding, so every graph has
exactly one encoding. Its length is at least the number of vertices, so
an algorithm whose running time is measured in the number of vertices
can read its whole input.
-/

namespace Lax185574.Encodings

open Lax185574.Encoding Lax185574.Graphs Lax185574.FirstOrderLogic

universe u

deriving instance Encode for Bool, Fin, Prod, Sum, Option, Int, Rat, Empty, Formula,
  Lax3.FirstOrder.FO

/-- A list is encoded by its length, followed by the encodings of its
entries. -/
instance {α : Type u} [Encode α] : Encode (List α) where
  encode l := l.length :: (l.map encode).flatten

/-- A family indexed by `Fin n` is encoded as the list of its members. -/
instance {α : Type u} {n : ℕ} [Encode α] : Encode (Fin n → α) where
  encode f := encode (List.ofFn f)

/-- A finite set is encoded by the list of the encodings of its elements,
in increasing lexicographic order. -/
instance {α : Type u} [Encode α] : Encode (Finset α) where
  encode S := encode ((S.image encode).sort (· ≤ ·))

/-- A number `d` or `∞` is encoded as one number, `d + 1` for `d` and
`0` for `∞`. -/
instance : Encode ℕ∞ where
  encode d := [if d = ⊤ then 0 else d.toNat + 1]

open Classical in
/-- A graph of mathlib on `Fin n` is encoded by the family of the
neighborhoods of its vertices. -/
noncomputable instance {n : ℕ} : Encode (SimpleGraph (Fin n)) where
  encode H := encode fun v : Fin n => Finset.univ.filter (H.Adj v)

open Classical in
/-- A graph is encoded by the family of the neighborhoods of its
vertices. -/
noncomputable instance : Encode Graph where
  encode G := encode fun v : Fin G.n => ({u | G.Adj v u} : Finset (Fin G.n))

end Lax185574.Encodings
