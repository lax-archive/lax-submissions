import Lax185574.AtomicTypes
import Lax185574.Flips
import Lax185574.Partitions

/-!
---
title: Definable flips
type: definition
---
For s ∈ ℕ, an s-tuple p̄ = (p₁, …, p_s) of vertices of a graph G and a
symmetric relation R ⊆ Π^s × Π^s, the graph G ⊕ (p̄, R) is the
{p₁, …, p_s}-flip H of G obtained by partitioning V(G) into atomic types
over p̄ and then flipping according to R. More precisely, for
uv ∈ (V choose 2),

uv ∈ E(H) △ E(G)  ⟺  (atp^G(u/p̄), atp^G(v/p̄)) ∈ R.

Such a flip is called *s-definable*. Equivalently, an s-definable flip
is an S-flip for some S ⊆ V(G) of size at most s. An s-definable flip is
also s'-definable for every s' ≥ s.

# Formalization notes

An S-flip of G is a flip for the partition into atomic types over S,
`Flips.IsFlip G (Partitions.atomicTypes G S) H`.

The graph G ⊕ (p̄, R) is `flipOver G p R`. It is built with
`SimpleGraph.fromRel`, which removes the diagonal and symmetrizes. For a
symmetric relation R the relation that is symmetrized is already
symmetric, so two distinct vertices are adjacent in `flipOver G p R`
exactly when their adjacency in G differs from membership of their
atomic types in R. Every statement about `flipOver` assumes R symmetric.

An s-definable flip, `IsDefinableFlip G s H`, is defined by the second,
equivalent formulation: an S-flip for a finite set S of at most s
vertices. The two formulations agree on every graph with at least one
vertex, by listing S with repetitions as an s-tuple, or, if S is empty
and s ≥ 1, by a constant tuple, since every ∅-flip is also a {v}-flip. On the empty graph
there is no s-tuple for s ≥ 1, while the empty set still works. The
formulation by sets makes "s-definable implies s'-definable for s' ≥ s"
hold without exception.
-/

namespace Lax185574.DefinableFlips

open Lax185574.AtomicTypes Lax185574.Flips Lax185574.Partitions

universe u

variable {V : Type u}

/-- `G ⊕ (p̄, R)`: two distinct vertices are adjacent if and only if
their adjacency in `G` differs from membership of the pair of their
atomic types over `p̄` in the symmetric relation `R`. -/
noncomputable def flipOver (G : SimpleGraph V) {s : ℕ} (p : Fin s → V)
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    Xor (G.Adj u v) (R (atomicTypeOver G p u) (atomicTypeOver G p v))

/-- `H` is an `s`-definable flip of `G`: an `S`-flip of `G` for some set
`S` of at most `s` vertices. -/
def IsDefinableFlip (G : SimpleGraph V) (s : ℕ) (H : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card ≤ s ∧ IsFlip G (atomicTypes G (S : Set V)) H

end Lax185574.DefinableFlips
