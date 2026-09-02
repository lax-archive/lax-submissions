import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Grid number
type: definition
---
A *k*-division of a matrix partitions its rows into *k* sets of consecutive
rows and its columns into *k* sets of consecutive columns; its *k*² cells are
the intersections of a row set with a column set. A matrix has a *k*-grid
minor if it has a *k*-division with at least one 1-entry in each of its *k*²
cells. The grid number of a matrix is the largest *k* such that it has a
*k*-grid minor. The grid number of a graph *G*, denoted by gn(*G*), is the
minimum, taken among all the adjacency matrices *M* of *G*, of the grid
number of *M*.

# Formalization notes

An adjacency matrix of `G` is determined by an ordering of its vertices, a
bijection with `Fin n`; the 0/1 matrix is represented by the set of positions
of its 1-entries. A `k`-division is given by the `k + 1` boundaries
`0 = r₀ < r₁ < ⋯ < r_k = n` of its row sets and likewise of its column sets.
-/

namespace Lax65.GridNumber

/-- `M` has a `k`-grid minor: a division of the rows and of the columns into
`k` sets of consecutive indices such that every cell contains a 1-entry. -/
def HasGridMinor {n : ℕ} (M : Fin n → Fin n → Prop) (k : ℕ) : Prop :=
  ∃ r c : Fin (k + 1) → ℕ,
    StrictMono r ∧ r 0 = 0 ∧ r (Fin.last k) = n ∧
    StrictMono c ∧ c 0 = 0 ∧ c (Fin.last k) = n ∧
    ∀ i j : Fin k, ∃ a b : Fin n,
      r i.castSucc ≤ a.val ∧ a.val < r i.succ ∧
        c j.castSucc ≤ b.val ∧ b.val < c j.succ ∧ M a b

/-- The grid number of a 0/1 matrix: the largest `k` such that it has a
`k`-grid minor. -/
noncomputable def matrixGridNumber {n : ℕ} (M : Fin n → Fin n → Prop) : ℕ :=
  sSup {k | HasGridMinor M k}

/-- The adjacency matrix of `G` under the vertex ordering `σ`. -/
def adjacencyMatrix {V : Type} (G : SimpleGraph V) {n : ℕ} (σ : Fin n ≃ V) :
    Fin n → Fin n → Prop :=
  fun a b => G.Adj (σ a) (σ b)

/-- The grid number of a finite simple graph: the least grid number of one of
its adjacency matrices. -/
noncomputable def gridNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ σ : Fin (Fintype.card V) ≃ V,
    matrixGridNumber (adjacencyMatrix G σ) = k}

end Lax65.GridNumber
