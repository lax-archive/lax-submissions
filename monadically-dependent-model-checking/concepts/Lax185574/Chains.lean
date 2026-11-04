import Lax185574.Flips
import Mathlib.Order.Lattice.Nat

/-!
---
title: Chains and their radius-r width
type: definition
---
A *chain* in a graph G is a decreasing sequence
V(G) = S₁ ⊇ ⋯ ⊇ S_ℓ = ∅ of vertex sets. Its *radius-r width*, for
r ∈ ℕ, is

max_{2 ≤ i ≤ ℓ} max_{v ∈ V(G)} |ATypes^G(Ball_r^{S_i}(v)/S_{i−1})|
  = max_{2 ≤ i ≤ ℓ} max_{v ∈ V(G)} |Ball_r^{S_i}(v)/𝒫_{S_{i−1}}|,

where Ball_r^S(v) is the ball in the metric of S-flips and 𝒫_S is the
partition into atomic types over S.

# Formalization notes

The formalization lists a chain in the reverse order, as the increasing
sequence ∅ = S₁ ⊆ ⋯ ⊆ S_ℓ = V(G). A chain is a nonempty list of finite
vertex sets, the first empty, the last the whole vertex set, and each
contained in the next. Consecutive sets may be equal. Reversing the list
turns a chain of the paper into one of the formalization, and the
widths agree after the reversal. A term of the paper pairs a set with
its predecessor, which is the larger set: the ball is taken in the
metric of flips of the smaller set, and the partition into atomic types
over the larger one. In the formalization the term for consecutive sets
S_t ⊆ S_{t+1} takes the ball in the metric of S_t-flips and the
partition 𝒫_{S_{t+1}}, which is the same term.

The width is the second form of the paper: the number of parts of
the partition into atomic types that meet the ball. The vertices of the
ball with the same atomic type over a set S are exactly those in the
same part of 𝒫_S, so the two forms agree. The maximum is the supremum of a set of natural numbers,
finite on a finite vertex type. The empty maximum, for a chain of length
one, is 0.

The chain is the same object for every graph on the vertex set. The
graph enters only the width.
-/

namespace Lax185574.Chains

open Lax185574.Partitions Lax185574.Flips

universe z

variable {V : Type z}

/-- `S` is a chain: `∅ = S₁ ⊆ ⋯ ⊆ S_m = V`. -/
def IsChain [Fintype V] (S : List (Finset V)) : Prop :=
  ∃ h : S ≠ [], S.head h = ∅ ∧ S.getLast h = Finset.univ ∧
    ∀ (t : ℕ) (ht : t + 1 < S.length), S[t] ⊆ S[t + 1]

/-- The radius-`r` width of the chain `S` in `G`: the largest number of
parts of `𝒫_{S_{t+1}}` that meet a radius-`r` ball in the metric of
`S_t`-flips. -/
noncomputable def chainWidth (G : SimpleGraph V) (r : ℕ) (S : List (Finset V)) : ℕ :=
  sSup {K | ∃ (t : ℕ) (ht : t + 1 < S.length) (v : V),
    K = partCount (atomicTypes G (S[t + 1] : Set V))
      (flipBall G (atomicTypes G (S[t] : Set V)) r v)}

end Lax185574.Chains
