import Mathlib.Data.List.Basic

/-!
---
title: Crossings along a finite membership sequence
type: definition
---
For a set and a listed order of vertices, write down whether each vertex
belongs to the set. Its crossing count is the number of changes between
consecutive entries. For two sequences of the same length, their Hamming
distance is the number of positions with different entries.

# Formalization notes

Boolean entries are the actual membership data manipulated by an algorithm.
These definitions do not assert that the vertex list is a permutation; that
is a separate invariant when this representation is used for an order.
The Hamming-distance recursion is used only on equal-length lists.
-/

namespace Lax235315.SequenceCrossings

/-- The number of changes between consecutive membership bits. -/
def crossings : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a = b then 0 else 1) + crossings (b :: rest)

/-- The number of disagreeing positions of two equal-length membership lists. -/
def hamming : List Bool → List Bool → ℕ
  | a :: rest, b :: rest' => (if a = b then 0 else 1) + hamming rest rest'
  | _, _ => 0

end Lax235315.SequenceCrossings
