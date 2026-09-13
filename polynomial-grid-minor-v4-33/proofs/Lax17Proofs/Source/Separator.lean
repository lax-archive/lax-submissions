import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Lax17Proofs

universe u v w


/-!
# Balanced separators

This file contains the finite balanced-separator interface used in the
post-expander step of the polynomial grid-minor proof.  The separator theorem
used by Chuzhoy--Tan says that a graph with no small balanced separator
contains every sufficiently small target graph as a minor.  The crossbar-grid
assembly proves the no-small-separator hypothesis for the auxiliary expander
produced by the cut-matching game.
-/

namespace SimpleGraph

/-- A balanced separator witness in a finite simple graph, following
Definition 5.1 of `expander.pdf`.

The paper asks for a partition `V = A ∪ B ∪ S` with no edge from `A` to `B`
and with both sides of size at most `2n/3`.  This structure stores the same
condition in an oriented form: `A` is chosen as the smaller side, so it is
enough to record `|A| ≤ |B|` and `3 * |B| ≤ 2 * n`.  Empty sides are allowed,
as in Definition 5.1. -/
structure BalancedSeparator {X : Type u} [Fintype X] [DecidableEq X]
    (H : _root_.SimpleGraph X) (A B S : Finset X) : Prop where
  /-- The three parts cover all vertices. -/
  cover : A ∪ B ∪ S = Finset.univ
  /-- The two large sides are disjoint. -/
  disjoint_left_right : Disjoint A B
  /-- The left side is disjoint from the separator. -/
  disjoint_left_separator : Disjoint A S
  /-- The right side is disjoint from the separator. -/
  disjoint_right_separator : Disjoint B S
  /-- `A` is chosen as the smaller of the two large sides. -/
  left_card_le_right_card : A.card ≤ B.card
  /-- `B` has size at most `2/3` of the ambient vertex set. -/
  right_balanced : 3 * B.card ≤ 2 * Fintype.card X
  /-- There are no graph edges between the two large sides. -/
  no_edge_left_right : ∀ ⦃a b : X⦄, a ∈ A → b ∈ B → ¬ H.Adj a b

/-- A graph has no balanced separator smaller than scale `denom` if every
balanced separator `S` has `|V| <= denom * |S|`. -/
def NoSmallBalancedSeparator {X : Type u} [Fintype X] [DecidableEq X]
    (H : _root_.SimpleGraph X) (denom : ℕ) : Prop :=
  ∀ ⦃A B S : Finset X⦄, BalancedSeparator H A B S →
    Fintype.card X ≤ denom * S.card

namespace NoSmallBalancedSeparator

/-- Increasing the separator scale preserves the no-small-separator property. -/
theorem mono {X : Type u} [Fintype X] [DecidableEq X]
    {H : _root_.SimpleGraph X} {d e : ℕ}
    (hH : NoSmallBalancedSeparator H d) (hde : d ≤ e) :
    NoSmallBalancedSeparator H e := by
  intro A B S hSep
  exact (hH hSep).trans (Nat.mul_le_mul_right S.card hde)

end NoSmallBalancedSeparator

end SimpleGraph

end Lax17Proofs
