import Lax48.TwinWidth

/-!
---
title: Oriented twin-width
type: definition
---
An oriented partition sequence of a finite simple graph *G* is a partition
sequence of *G* in which every red edge is replaced by a red arc leaving the
newly merged part: when two parts are merged, the merged part gets a red arc
to every other part it is not homogeneous with, and the red arcs between the
remaining parts stay as they were. An oriented *d*-sequence is one in which
every part of every partition has at most *d* out-going red arcs. The
oriented twin-width of *G* is the least *d* such that *G* admits an oriented
*d*-sequence.

# Formalization notes

Partitions, merges, and homogeneity are those of the twin-width concept of
the prerequisite submission; two parts of a partition are joined by a red
edge exactly when they are not homogeneous. The red arcs are carried as an
explicit relation between the parts of each partition: there are none at the
singleton partition, and each merge updates them by the rule above.
-/

namespace Lax65.OrientedTwinWidth

open Lax48.TwinWidth

/-- An oriented partition sequence of `G` in which every part has at most `d`
out-going red arcs: starting from the singleton partition with no red arcs,
each step merges two parts into one, gives the merged part a red arc to every
other part it is not homogeneous with, and keeps the red arcs between the
remaining parts, until a single part remains. -/
structure OrientedPartitionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of merge steps. -/
  stepCount : ℕ
  /-- The partition after each number of merge steps. -/
  partition : ℕ → Finset (Finset V)
  /-- The red arcs between parts after each number of merge steps. -/
  redArc : ℕ → Finset V → Finset V → Prop
  /-- The sequence starts at the singleton partition. -/
  starts : partition 0 = singletonPartition V
  /-- There are no red arcs at the start. -/
  redArc_zero : ∀ A B, ¬ redArc 0 A B
  /-- The sequence ends with a single part. -/
  ends : (partition stepCount).card ≤ 1
  /-- Each step merges two distinct parts into one and keeps all other parts;
  the merged part gets a red arc to every other part it is not homogeneous
  with, and the red arcs between the remaining parts are unchanged. -/
  step_merges :
    ∀ i, i < stepCount → ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = insert (A ∪ B) (((partition i).erase A).erase B) ∧
      ∀ C ∈ partition (i + 1), ∀ D ∈ partition (i + 1),
        (redArc (i + 1) C D ↔
          if C = A ∪ B then D ≠ C ∧ ¬ Homogeneous G C D
          else D ≠ A ∪ B ∧ redArc i C D)
  /-- Every part of every partition in the sequence has at most `d` out-going
  red arcs. -/
  outDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ partition i →
      {B | B ∈ partition i ∧ redArc i A B}.ncard ≤ d

/-- `G` admits an oriented `d`-sequence. -/
def HasOrientedTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (OrientedPartitionSequence G d)

/-- The oriented twin-width of a finite simple graph: the least `d` such that
the graph admits an oriented `d`-sequence. -/
noncomputable def orientedTwinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {d | HasOrientedTwinWidthAtMost G d}

end Lax65.OrientedTwinWidth
