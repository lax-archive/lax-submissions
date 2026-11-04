import Lax185574.Partitions
import Lax185574.GaifmanGraph

/-!
---
title: Flips and flip metrics
type: definition
---
For a graph G and a partition 𝒫 of V ≔ V(G), a *𝒫-flip* of G is a graph
H with V(H) = V such that for every pair X, Y ∈ 𝒫 (possibly X = Y),
either H[X, Y] = G[X, Y] or H[X, Y] = Ḡ[X, Y]. If |𝒫| ≤ s, then H is
an *s-flip* of G. The associated *flip metric* and its balls are

dist_𝒫(u, v) ≔ max { dist^H(u, v) : H is a 𝒫-flip of G },
Ball^𝒫_r(v) ≔ { u : dist_𝒫(u, v) ≤ r } = ⋂ { Ball^H_r(v) : H is a 𝒫-flip of G }.

As a shorthand, for a graph G and a set S ⊆ V(G), a 𝒫_S-flip of G is
called an *S-flip*, and dist_S^G ≔ dist_{𝒫_S} and Ball^S_r ≔ Ball^{𝒫_S}_r.
Here 𝒫_S is the partition into atomic types over S, see
`Lax185574.AtomicTypes` and `Lax185574.Partitions`.

# Formalization notes

"H[X, Y] = G[X, Y] or H[X, Y] = Ḡ[X, Y]" says that on all pairs of
distinct vertices x ∈ X, y ∈ Y, adjacency in H agrees with adjacency in
G, or on all of them it agrees with non-adjacency in G. For X = Y this
reads H[X] = G[X] or H[X] = Ḡ[X], which is the intended meaning. The
parts X and Y are named by vertices a and b with X = 𝒫(a) and Y = 𝒫(b).

The bound dist_𝒫(u, v) ≤ r is `FlipWithinDist`: in every 𝒫-flip, some
walk from u to v has length at most r. Distances are measured by walks,
as in `Lax185574.GaifmanGraph`, so the maximum of the paper is never
needed as a number, and an infinite distance in some flip is allowed.
The ball is the set of vertices u with dist_𝒫(v, u) ≤ r, which is the
intersection form of the paper. The ball Ball^S_r(v) is
`flipBall G (atomicTypes G S) r v` and gets no separate name. An s-flip
is a 𝒫-flip with `Nat.card (Quotient 𝒫) ≤ s`, which is spelled out where
it is used.
-/

namespace Lax185574.Flips

open Lax185574.Partitions Lax185574.GaifmanGraph

universe z

variable {V : Type z}

/-- `H` is a `𝒫`-flip of `G`: for every pair of parts `𝒫(a)`, `𝒫(b)`,
adjacency in `H` between distinct vertices of these parts either agrees
with adjacency in `G` throughout, or with non-adjacency in `G`
throughout. -/
def IsFlip (G : SimpleGraph V) (P : Setoid V) (H : SimpleGraph V) : Prop :=
  ∀ a b : V,
    (∀ x y : V, P x a → P y b → x ≠ y → (H.Adj x y ↔ G.Adj x y)) ∨
      (∀ x y : V, P x a → P y b → x ≠ y → (H.Adj x y ↔ ¬ G.Adj x y))

/-- `dist_𝒫(u, v) ≤ r`: in every `𝒫`-flip of `G`, some walk from `u`
to `v` has length at most `r`. -/
def FlipWithinDist (G : SimpleGraph V) (P : Setoid V) (r : ℕ) (u v : V) : Prop :=
  ∀ H : SimpleGraph V, IsFlip G P H → WithinDist H r u v

/-- `Ball^𝒫_r(v)`: the vertices within distance `r` of `v` in every
`𝒫`-flip of `G`. -/
def flipBall (G : SimpleGraph V) (P : Setoid V) (r : ℕ) (v : V) : Set V :=
  {u | FlipWithinDist G P r v u}

end Lax185574.Flips
