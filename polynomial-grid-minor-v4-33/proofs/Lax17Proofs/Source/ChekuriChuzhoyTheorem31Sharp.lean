import Lax17Proofs.Source.ChekuriChuzhoyTheorem31
import Lax17Proofs.Source.ChekuriChuzhoyTheorem215Sharp

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 3.1 with the printed constant

The proof of Theorem 3.1 in `chekuri-chuzhoy.pdf` applies the
tree-with-many-leaves argument with the exact width
`(16 * h + 10) * q`.  `ChekuriChuzhoyTheorem215Sharp` proves the corresponding
`p + 4` counting form of Theorem 2.15.  This file threads that sharp count
through the already formalized good-linkage descent and auxiliary-tree bridge
realization.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V} {h q : ℕ}

/-- A good linkage has a many-leaf auxiliary spanning tree under the sharp
`p + 4` cardinality bound used inside the proof of Theorem 3.1. -/
theorem aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_sharp
    (L : PerfectPathPacking G A B)
    (hgood : GoodLinkage L h)
    (haux : (linkageAuxGraph L).Connected)
    {leaves : ℕ}
    (hleaves : 1 ≤ leaves)
    (hlarge :
      2 * leaves * ((8 * h + 1) + 4) ≤ Fintype.card L.Index) :
    HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) leaves := by
  classical
  rcases theorem215_tree_with_many_leaves_or_long_twoPath_sharp
      (linkageAuxGraph L) (L := leaves) (p := 8 * h + 1)
      haux hleaves (by omega) hlarge with htree | htwoPath
  · exact htree
  · exact False.elim (hgood htwoPath)

/-- Connected-host version of the sharp auxiliary-tree extraction. -/
theorem aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_of_connected_sharp
    (L : PerfectPathPacking G A B)
    (hgood : GoodLinkage L h)
    (hnonempty : Nonempty L.Index)
    (hconn : G.Connected)
    {leaves : ℕ}
    (hleaves : 1 ≤ leaves)
    (hlarge :
      2 * leaves * ((8 * h + 1) + 4) ≤ Fintype.card L.Index) :
    HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) leaves := by
  classical
  have haux : (linkageAuxGraph L).Connected :=
    AppendixB1.IndexedAuxiliaryPrefix.auxiliaryConnectedObservation_of_connected
      (G := G) L hnonempty hconn
  exact aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_sharp
    (G := G) (A := A) (B := B) (h := h)
    L hgood haux hleaves hlarge

/-- Theorem 3.1, conditional only on its Appendix B.1 producer, with the
paper's exact `(16 * h + 10) * q` width. -/
theorem exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement_sharp
    (hB1 :
      ∀ L : PerfectPathPacking G A B,
        AppendixB1.TheoremB1Statement G h L)
    (hconn : G.Connected)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hcard : A.card = B.card)
    (hh : 1 < h)
    (hq : 1 < q)
    (hlarge : (16 * h + 10) * q ≤ A.card) :
    ContainsGridMinor G h ∨
      ∃ Q : PathPacking G A B,
        Q.card = q ∧ Q.StaysIn Finset.univ ∧
          Q.HasPairwiseBridgesIn Finset.univ := by
  classical
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq hlink hcard with
    ⟨L₀, _hL₀card, _hL₀stay⟩
  rcases exists_goodLinkage_or_gridMinor_of_theoremB1Statement
      (G := G) (A := A) (B := B) (h := h) hB1 hconn hlink hh L₀ with
    hgrid | ⟨Lgood, hgood⟩
  · exact Or.inl hgrid
  · have hnonempty : Nonempty Lgood.Index := by
      apply Fintype.card_pos_iff.mp
      change 0 < Lgood.card
      rw [Lgood.card_eq_left_card]
      have hpositive : 0 < (16 * h + 10) * q := by positivity
      exact lt_of_lt_of_le hpositive hlarge
    have hlargeL :
        2 * q * ((8 * h + 1) + 4) ≤ Fintype.card Lgood.Index := by
      change 2 * q * ((8 * h + 1) + 4) ≤ Lgood.card
      rw [Lgood.card_eq_left_card]
      nlinarith
    have htree :
        HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph Lgood) q :=
      aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_of_connected_sharp
        (G := G) (A := A) (B := B) (h := h)
        Lgood hgood hnonempty hconn (by omega) hlargeL
    rcases auxiliaryTreeExtractionInput G hh hq Lgood htree with
      ⟨Q, hQcard, hQbridges⟩
    refine Or.inr ⟨Q, hQcard, ?_, hQbridges⟩
    intro i v _hv
    exact Finset.mem_univ v

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
