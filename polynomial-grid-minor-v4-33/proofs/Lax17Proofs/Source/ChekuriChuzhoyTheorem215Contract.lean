import Lax17Proofs.Source.ChekuriChuzhoyTheorem215

namespace Lax17Proofs

universe u v w

/-!
# Contract for Chekuri--Chuzhoy Theorem 2.15

This file states the structural content of Theorem 2.15 from
`chekuri-chuzhoy.pdf`, omitting the algorithmic strengthening: a sufficiently
large connected graph either has a spanning tree with many leaves or has a long
2-path.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract


/-- Chekuri--Chuzhoy Theorem 2.15, structural form.

The paper writes the size hypothesis as `n / (2L) >= p + 5`.  Since `L >= 1`,
the contract uses the equivalent multiplication-friendly condition
`2 * L * (p + 5) <= |V|`. -/
theorem theorem215_tree_with_many_leaves_or_long_twoPath :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (Z : _root_.SimpleGraph V) {L p : ℕ},
        Z.Connected →
          1 ≤ L →
            1 ≤ p →
              2 * L * (p + 5) ≤ Fintype.card V →
                ChekuriChuzhoy.HasSpanningTreeWithAtLeastLeaves Z L ∨
                  ChekuriChuzhoy.ContainsTwoPath Z p := by
  intro V _ _ Z L p hZ hL hp hcard
  exact ChekuriChuzhoy.theorem215_tree_with_many_leaves_or_long_twoPath
    (V := V) Z (L := L) (p := p) hZ hL hp hcard

end ChekuriChuzhoyContract
end SimpleGraph

end Lax17Proofs
