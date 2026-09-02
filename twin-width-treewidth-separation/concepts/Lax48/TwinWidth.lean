import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice

/-!
---
title: Twin-width
type: definition
---
A partition sequence of a finite simple graph *G* is a sequence of partitions
of its vertex set that starts at the partition into singletons, merges two
parts into one at every step, and ends at the partition with a single part.
Two parts of a same partition are homogeneous if either every pair of
vertices across them is adjacent or none is; two non-homogeneous parts are
red-adjacent. The red degree of a part is the number of other parts of its
partition that are red-adjacent to it.

The twin-width of *G* is the least *d* such that *G* has a partition sequence
in which every part of every partition has red degree at most *d*.

# Formalization notes

The partitions are indexed by the number of merges performed so far, and
values of `partition` beyond `stepCount` are irrelevant. Because every state
is reached from the singleton partition by merges, each `partition i` with
`i ≤ stepCount` is automatically a partition of the vertex set. Merging in
any order gives a partition sequence whose red degrees are at most the number
of vertices, so the infimum in `twinWidth` ranges over a nonempty set.
-/

namespace Lax48.TwinWidth

/-- Two vertex sets are homogeneous in `G`: either every pair of vertices
across them is adjacent, or none is. -/
def Homogeneous {V : Type} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)

/-- The red degree of a part `A` in a family of parts `P`: the number of
other parts of `P` that are not homogeneous with `A`. -/
noncomputable def redDegree {V : Type} (G : SimpleGraph V)
    (P : Finset (Finset V)) (A : Finset V) : ℕ :=
  {B | B ∈ P ∧ B ≠ A ∧ ¬ Homogeneous G A B}.ncard

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

/-- A partition sequence of `G` in which every part has red degree at most
`d`: starting from the singleton partition, each step merges two parts into
one, until a single part remains. -/
structure PartitionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of merge steps. -/
  stepCount : ℕ
  /-- The partition after each number of merge steps. -/
  partition : ℕ → Finset (Finset V)
  /-- The sequence starts at the singleton partition. -/
  starts : partition 0 = singletonPartition V
  /-- The sequence ends with a single part. -/
  ends : (partition stepCount).card ≤ 1
  /-- Each step merges two distinct parts into one and keeps all other
  parts. -/
  step_merges :
    ∀ i, i < stepCount → ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = insert (A ∪ B) (((partition i).erase A).erase B)
  /-- Every part of every partition in the sequence has red degree at most
  `d`. -/
  redDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ partition i →
      redDegree G (partition i) A ≤ d

/-- `G` has a partition sequence in which every part has red degree at most
`d`. -/
def HasTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (PartitionSequence G d)

/-- The twin-width of a finite simple graph: the least `d` such that the
graph has a partition sequence in which every part has red degree at most
`d`. -/
noncomputable def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {d | HasTwinWidthAtMost G d}

end Lax48.TwinWidth
