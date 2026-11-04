import Lax185574.VCDimension

/-!
---
title: Bounded-VC duality
type: lemma
---
For a graph G and sets S, X ⊆ V(G), the set S *dominates* X if every
vertex of X ∖ S has a neighbor in S, and S *antidominates* X if every
vertex of X ∖ S has a nonneighbor in S.

For every d ∈ ℕ there is some k ∈ ℕ with the following property. Let G
be a graph of VC-dimension at most d, and let X, Y ⊆ V(G) be two
(possibly overlapping) sets with at least one of X, Y finite. Then there
exists a set sample(X, Y) of size at most k such that at least one of
the following holds:

1. sample(X, Y) is contained in Y and dominates X,
2. sample(X, Y) is contained in X and antidominates Y.

This is a corollary of the (p, q)-theorem for bounded VC-dimension.

# Formalization notes

The graph is finite, so the hypothesis that X or Y is finite always
holds and is omitted. The paper also allows infinite graphs. Every
application in the paper, through the ball-flip lemma inside the proof
of the closure theorem, is to a finite graph. The bound k is chosen
before the graph. VC-dimension is `VCDimension.vcDim`.
-/

namespace Lax185574.VCDuality

open Lax185574.VCDimension

universe u

variable {V : Type u}

/-- `S` dominates `X` in `G`: every vertex of `X ∖ S` has a neighbor in
`S`. -/
def Dominates (G : SimpleGraph V) (S X : Set V) : Prop :=
  ∀ x ∈ X \ S, ∃ y ∈ S, G.Adj x y

/-- `S` antidominates `X` in `G`: every vertex of `X ∖ S` has a
nonneighbor in `S`. -/
def Antidominates (G : SimpleGraph V) (S X : Set V) : Prop :=
  ∀ x ∈ X \ S, ∃ y ∈ S, ¬ G.Adj x y

/-- **Bounded-VC duality.** In a finite graph of VC-dimension at most
`d`, for any two vertex sets `X` and `Y`, some set of at most `k(d)`
vertices of `Y` dominates `X`, or some set of at most `k(d)` vertices of
`X` antidominates `Y`. -/
axiom vc_duality (d : ℕ) :
    ∃ k : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V), vcDim G ≤ d →
      ∀ X Y : Set V, ∃ S : Finset V, S.card ≤ k ∧
        (((S : Set V) ⊆ Y ∧ Dominates G S X) ∨
          ((S : Set V) ⊆ X ∧ Antidominates G S Y))

end Lax185574.VCDuality
