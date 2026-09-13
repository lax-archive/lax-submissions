import Lax17Proofs.Source.ChekuriChuzhoyTheorem215
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# The sharp counting form of Chekuri--Chuzhoy Theorem 2.15

Theorem 3.1 of `chekuri-chuzhoy.pdf` uses Theorem 2.15 with
`2 * L * (p + 4)` vertices, although the separately displayed statement of
Theorem 2.15 uses the coarser `2 * L * (p + 5)` bound.  The proof of
Theorem 2.15 gives the sharper form when the degree-two components and the
non-degree-two skeleton are counted together instead of bounding both by
`2 * L` independently.

This module records that joint count.  It is the exact strengthening needed
to recover the printed `(16 * h + 10) * q` width in Theorem 3.1 at
`p = 8 * h + 1`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The degree-two induced forest has at most one more component than there
are vertices in the complementary leaf/branch skeleton. -/
theorem degreeTwoInducedGraph_component_count_le_skeleton_succ
    {T : _root_.SimpleGraph V} [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    Fintype.card (degreeTwoInducedGraph T).ConnectedComponent ≤
      (treeSkeletonVertexSet T).card + 1 := by
  classical
  let D := treeDegreeTwoVertexSet T
  let S := treeSkeletonVertexSet T
  let H : _root_.SimpleGraph {v : V // v ∈ D} := degreeTwoInducedGraph T
  have hacyc : H.IsAcyclic := by
    simpa [H, degreeTwoInducedGraph, D] using
      hT.isAcyclic.induce {v : V | v ∈ D}
  have hforest :=
    isAcyclic_connectedComponent_card_add_edgeFinset_card H hacyc
  have hDcard : Fintype.card {v : V // v ∈ D} = D.card := by
    simpa [D] using degreeTwoSubtype_card_eq T
  have hforestD :
      Fintype.card H.ConnectedComponent + H.edgeFinset.card = D.card := by
    simpa [H, hDcard] using hforest
  have hedgeH :
      H.edgeFinset.card = (T.edgeFinset ∩ D.sym2).card := by
    simpa [H, D] using degreeTwoInducedGraph_edgeFinset_card_eq_inter T
  have hsplit :
      (T.edgeFinset ∩ D.sym2).card + (T.edgeFinset \ D.sym2).card =
        T.edgeFinset.card := by
    simp [D]
  have hnonD :
      (T.edgeFinset \ D.sym2).card ≤ 2 * S.card := by
    have h₁ :=
      tree_edgeFinset_sdiff_degreeTwo_sym2_card_le_skeleton_degree_sum
        T hT hcard
    have h₂ := treeSkeletonVertexSet_degree_sum_le_two_mul_card T hT hcard
    simpa [D, S] using h₁.trans h₂
  have hpartition :
      D.card + S.card = Fintype.card V := by
    simpa [D, S] using
      treeDegreeTwoVertexSet_card_add_skeleton_card T hT hcard
  have hedgeTree : T.edgeFinset.card + 1 = Fintype.card V :=
    hT.card_edgeFinset
  simpa [H, S] using
    (show Fintype.card H.ConnectedComponent ≤ S.card + 1 by omega)

/-- Sharp finite-component pigeonhole: if the total number of vertices is
strictly larger than `componentCount * m`, some component has more than `m`
vertices. -/
theorem exists_component_card_gt_of_mul_lt
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj] {m : ℕ}
    (htotal :
      Fintype.card H.ConnectedComponent * m < Fintype.card V) :
    ∃ C : H.ConnectedComponent,
      m < (connectedComponentVertexFinset H C).card := by
  classical
  by_contra h
  have hall :
      ∀ C : H.ConnectedComponent,
        (connectedComponentVertexFinset H C).card ≤ m := by
    intro C
    by_contra hC
    exact h ⟨C, by omega⟩
  have :=
    card_le_components_mul_of_component_card_le H m hall
  omega

/-- Joint skeleton/component counting extracts the same `p + 4`-vertex tree
2-path as Appendix A.2 from the sharper hypothesis `2 * L * (p + 4) ≤ |V|`.
-/
theorem exists_long_degreeTwo_tree_path_sharp
    {T : _root_.SimpleGraph V} [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    {L p : ℕ}
    (hT : T.IsTree)
    (hL : 1 ≤ L)
    (hcard : 2 * L * (p + 4) ≤ Fintype.card V)
    (hleaves : leafCount T < L) :
    ∃ P : GraphPath T,
      p + 4 ≤ P.vertexSet.card ∧
        ∀ v ∈ P.vertexSet, DegreeEquals T v 2 := by
  classical
  have hVcard : 2 ≤ Fintype.card V := by
    nlinarith
  let D := treeDegreeTwoVertexSet T
  let S := treeSkeletonVertexSet T
  let H : _root_.SimpleGraph {v : V // v ∈ D} := degreeTwoInducedGraph T
  have hpartition :
      D.card + S.card = Fintype.card V := by
    simpa [D, S] using
      treeDegreeTwoVertexSet_card_add_skeleton_card T hT hVcard
  have hcomponents :
      Fintype.card H.ConnectedComponent ≤ S.card + 1 := by
    simpa [H, S] using
      degreeTwoInducedGraph_component_count_le_skeleton_succ
        (T := T) hT hVcard
  have hskeleton :
      S.card + 1 ≤ 2 * L := by
    simpa [S] using
      treeSkeletonVertexSet_card_succ_le_two_mul T hT hVcard hleaves
  have hbase :
      (S.card + 1) * (p + 3) + 1 ≤ D.card := by
    have hmul :
        (S.card + 1) * (p + 4) ≤ 2 * L * (p + 4) :=
      Nat.mul_le_mul_right (p + 4) hskeleton
    have hlarge :
        (S.card + 1) * (p + 4) ≤ D.card + S.card := by
      rw [hpartition]
      exact hmul.trans hcard
    nlinarith
  have hcomponentMul :
      Fintype.card H.ConnectedComponent * (p + 3) <
        Fintype.card {v : V // v ∈ D} := by
    have hmul :
        Fintype.card H.ConnectedComponent * (p + 3) ≤
          (S.card + 1) * (p + 3) :=
      Nat.mul_le_mul_right (p + 3) hcomponents
    rw [degreeTwoSubtype_card_eq T]
    simpa [D] using lt_of_le_of_lt hmul (by omega : (S.card + 1) * (p + 3) < D.card)
  rcases exists_component_card_gt_of_mul_lt H hcomponentMul with
    ⟨C, hC⟩
  rcases exists_tree_path_of_degreeTwo_component T C with
    ⟨P, hPcard, hPdeg⟩
  refine ⟨P, ?_, hPdeg⟩
  have hCbase :
      p + 3 <
        (connectedComponentVertexFinset (degreeTwoInducedGraph T) C).card := by
    simpa [H] using hC
  have hC' :
      p + 4 ≤
        (connectedComponentVertexFinset (degreeTwoInducedGraph T) C).card := by
    omega
  simpa [H, hPcard] using hC'

/-- Strengthened non-algorithmic form of Theorem 2.15.  This is obtained by
the paper's maximum-leaf spanning-tree proof with the joint count above. -/
theorem theorem215_tree_with_many_leaves_or_long_twoPath_sharp
    (Z : _root_.SimpleGraph V) {L p : ℕ}
    (hZ : Z.Connected) (hL : 1 ≤ L) (hp : 1 ≤ p)
    (hcard : 2 * L * (p + 4) ≤ Fintype.card V) :
    HasSpanningTreeWithAtLeastLeaves Z L ∨ ContainsTwoPath Z p := by
  classical
  by_cases hmany : L ≤ leafCount (maxLeafSpanningTree Z hZ)
  · exact theorem215_of_maxLeafSpanningTree_many_leaves hZ hmany
  · have hfew : leafCount (maxLeafSpanningTree Z hZ) < L := by
      omega
    let T : _root_.SimpleGraph V := maxLeafSpanningTree Z hZ
    have hMax : IsLeafMaximalSpanningTree Z T := by
      simpa [T] using maxLeafSpanningTree_isLeafMaximal hZ
    rcases exists_long_degreeTwo_tree_path_sharp
        (T := T) hMax.2.1 hL hcard (by simpa [T] using hfew) with
      ⟨P, hPcard, hPdeg⟩
    exact Or.inr <|
      containsTwoPath_of_leafMaximal_tree_path hMax hp P hPcard hPdeg

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
