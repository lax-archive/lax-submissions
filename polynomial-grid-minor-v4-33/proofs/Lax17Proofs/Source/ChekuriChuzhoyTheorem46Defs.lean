import Lax17Proofs.Source.TreeOfSets

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 4.6: many-leaves interface

This file contains the small source-facing interface shared by the proof of
journal Theorem 4.6 and its top-down routing lemma, Theorem 4.7.  Keeping this
interface separate avoids importing the unrelated Section 5 development into
the many-leaves proof.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- The finite meta-tree data fixed at the beginning of the many-leaves branch
of Chekuri--Chuzhoy Theorem 4.6. -/
structure Theorem46LeafExtractionSetup
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W) (ell : ℕ) where
  /-- The DFS root, chosen to be a meta-tree leaf. -/
  root : Fin m
  /-- The unique child of the DFS root. -/
  child : Fin m
  /-- The `ell` selected leaf clusters used by the extraction. -/
  leaves : Finset (Fin m)
  /-- The root is a meta-tree leaf. -/
  root_leaf : DegreeEquals T.metaTree root 1
  /-- The exposed root-child meta-edge. -/
  root_child_adj : T.metaTree.Adj root child
  /-- The child is the unique neighbor of the root. -/
  root_child_unique : ∀ z : Fin m, T.metaTree.Adj root z → z = child
  /-- The DFS root is not one of the selected leaves. -/
  root_not_mem_leaves : root ∉ leaves
  /-- Exactly `ell` selected leaves are retained. -/
  leaves_card : leaves.card = ell
  /-- Every selected cluster is a meta-tree leaf. -/
  leaves_leaf : ∀ i ∈ leaves, DegreeEquals T.metaTree i 1

/-- The many-leaves/DFS branch of Chekuri--Chuzhoy journal Theorem 4.6. -/
def StrongPathOfSetsFromLeafyStrongTreeOfSets : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell w : ℕ}
    (T : StrongTreeOfSetsSystem G m W),
      1 < ell →
        1 < w →
          ell ^ 2 ≤ m →
            16 * w * ell ^ 2 + 1 < W →
              T.HasMetaLeavesAtLeast (ell + 1) →
                Nonempty (StrongPathOfSetsSystem G ell w)

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
