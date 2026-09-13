import Lax17Proofs.Source.AppendixA3ClusterSplit

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7: terminal capacity

This file isolates the maximum-degree counting step used in Chuzhoy's
Section 7 Corollary 7.4.
-/

namespace SimpleGraph
namespace AppendixA3TerminalCapacity


open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

namespace EdgePathPacking

/-- Source role (Chuzhoy, Section 7, Corollary 7.4): Lemma 7.2 supplies an
edge-disjoint packing from the terminal set `T` to a cluster boundary
`Gamma`; this estimate rules out a packing larger than the total degree
capacity of `T`.

The endpoint sets are required to lie in the localization set `C` so that
`T` and `C \ T` form the relevant partition.  Disjointness of `T` and
`Gamma` is essential: without it, `EdgePathPacking` permits arbitrarily many
indexed zero-edge paths at a common vertex. -/
theorem card_le_maxDegree_mul_source_card_of_staysIn [Fintype V]
    {C T Gamma : Finset V} {d : ℕ}
    (P : EdgePathPacking G T Gamma)
    (hdegree : MaxDegreeAtMost G d)
    (hT : T ⊆ C) (hGamma : Gamma ⊆ C)
    (hdisjoint : Disjoint T Gamma)
    (hstay : P.StaysIn C) :
    P.card ≤ d * T.card := by
  classical
  let Y : Finset V := C \ T
  let Q : EdgePathPacking G (T ∩ (T ∪ Gamma)) (Y ∩ (T ∪ Gamma)) := {
    Index := P.Index
    path := P.path
    connects := by
      intro i
      rcases P.connects i with hconn | hconn
      · exact Or.inl
          ⟨mem_inter.mpr ⟨hconn.1, mem_union_left Gamma hconn.1⟩,
            mem_inter.mpr
              ⟨mem_sdiff.mpr
                  ⟨hGamma hconn.2,
                    fun htargetT =>
                      Finset.disjoint_left.mp hdisjoint htargetT hconn.2⟩,
                mem_union_right T hconn.2⟩⟩
      · exact Or.inr
          ⟨mem_inter.mpr
              ⟨mem_sdiff.mpr
                  ⟨hGamma hconn.1,
                    fun hsourceT =>
                      Finset.disjoint_left.mp hdisjoint hsourceT hconn.1⟩,
                mem_union_right T hconn.1⟩,
            mem_inter.mpr ⟨hconn.2, mem_union_left Gamma hconn.2⟩⟩
    edge_disjoint := P.edge_disjoint
  }
  have hQstay : Q.StaysIn C := by
    intro i
    exact hstay i
  have hcover : T ∪ Y = C := by
    apply Finset.Subset.antisymm
    · exact union_subset hT sdiff_subset
    · intro v hvC
      by_cases hvT : v ∈ T
      · exact mem_union_left Y hvT
      · exact mem_union_right T (mem_sdiff.mpr ⟨hvC, hvT⟩)
  have hcutDisjoint : Disjoint T Y := by
    exact Finset.disjoint_left.mpr fun _v hvT hvY =>
      (mem_sdiff.mp hvY).2 hvT
  have hQcut :
      Q.card ≤ (Section44.edgeBoundary G T Y).card :=
    Section46.EdgePathPacking.card_le_edgeBoundary_of_staysIn_partition
      (G := G) (C := C) (T := T ∪ Gamma) (X := T) (Y := Y)
      Q hQstay hcover hcutDisjoint
  have hcutSubset :
      Section44.edgeBoundary G T Y ⊆ Section44.clusterBoundary G T := by
    intro e he
    rcases (Section44.mem_edgeBoundary (G := G) T Y e).1 he with
      ⟨heG, x, hx, y, hy, rfl⟩
    change s(x, y) ∈
      Section44.edgeBoundary G T ((Finset.univ : Finset V) \ T)
    exact (Section44.mem_edgeBoundary (G := G) T
      ((Finset.univ : Finset V) \ T) s(x, y)).2
        ⟨heG, x, hx, y,
          mem_sdiff.mpr ⟨mem_univ y, (mem_sdiff.mp hy).2⟩, rfl⟩
  have hboundaryVerticesSubset :
      AppendixA3ClusterSplit.boundaryVertices G T ⊆ T := by
    intro v hv
    exact (AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1 hv |>.1
  calc
    P.card = Q.card := by
      simp [Q, EdgePathPacking.card]
    _ ≤ (Section44.edgeBoundary G T Y).card := hQcut
    _ ≤ (Section44.clusterBoundary G T).card :=
      Finset.card_le_card hcutSubset
    _ ≤ d * (AppendixA3ClusterSplit.boundaryVertices G T).card :=
      AppendixA3ClusterSplit.clusterBoundary_card_le_maxDegree_mul_boundaryVertices_card
        (G := G) hdegree
    _ ≤ d * T.card :=
      Nat.mul_le_mul_left d (Finset.card_le_card hboundaryVerticesSubset)

end EdgePathPacking
end AppendixA3TerminalCapacity
end SimpleGraph

end Lax17Proofs
