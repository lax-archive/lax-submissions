import Lax17Proofs.Source.ChekuriChuzhoySection5GoodClustering
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterProduction
import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthDecomposition

namespace Lax17Proofs

universe u v w

/-!
# Dense-block replacement in Chekuri--Chuzhoy Section 5.1

The nonconstructive proof of Chekuri--Chuzhoy, *Polynomial Bounds for the
Grid-Minor Theorem*, journal Section 5.1, replaces a selected family of
contracted nonterminal clusters by a bandwidth decomposition of their
uncontracted union.  If every new part were small, this would be another good
clustering.  The internal named edges of the selected contracted block are
exactly the old cross-block original edges internal to that union, while the
new internal crossing edges are exactly those of the bandwidth decomposition.
The strict crossing-edge saving therefore contradicts the choice of a minimum
good clustering.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5DenseBlockReplacement


open Finset
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5GoodClustering

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The original vertices represented by a finite set of contracted
clustering vertices. -/
def selectedUnion {P : VertexClustering V}
    (B : Finset (ContractedVertex P)) : Finset V :=
  B.biUnion Subtype.val

@[simp] theorem mem_selectedUnion_iff {P : VertexClustering V}
    (B : Finset (ContractedVertex P)) (v : V) :
    v ∈ selectedUnion B ↔ contractedVertex P v ∈ B := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨A, hAB, hvA⟩
    have heq : contractedVertex P v = A := by
      apply Subtype.ext
      exact P.block_eq_of_mem A.2 hvA
    exact heq.symm ▸ hAB
  · intro hv
    exact Finset.mem_biUnion.mpr
      ⟨contractedVertex P v, hv, P.mem_block v⟩

/-- Because `selectedUnion B` is a union of whole `P`-blocks, every original
edge leaving it is an old cross-block edge of `P`. -/
theorem clusterBoundary_selectedUnion_subset_crossBlockOriginalEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) :
    Section44.clusterBoundary G (selectedUnion B) ⊆
      crossBlockOriginalEdges G P := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      rcases (mk_mem_clusterBoundary_iff G (selectedUnion B) u v).1 he with
        ⟨huv, hends | hends⟩
      · apply (mk_mem_crossBlockOriginalEdges (G := G) P u v).2
        refine ⟨huv, ?_⟩
        intro hblocks
        have hcontracted :
            contractedVertex P u = contractedVertex P v := by
          exact Subtype.ext hblocks
        have huB := (mem_selectedUnion_iff B u).1 hends.1
        have hvB : contractedVertex P v ∈ B := hcontracted ▸ huB
        exact hends.2 ((mem_selectedUnion_iff B v).2 hvB)
      · apply (mk_mem_crossBlockOriginalEdges (G := G) P u v).2
        refine ⟨huv, ?_⟩
        intro hblocks
        have hcontracted :
            contractedVertex P u = contractedVertex P v := by
          exact Subtype.ext hblocks
        have hvB := (mem_selectedUnion_iff B v).1 hends.1
        have huB : contractedVertex P u ∈ B := hcontracted.symm ▸ hvB
        exact hends.2 ((mem_selectedUnion_iff B u).2 huB)

/-- The legal-contracted cut around `B` has exactly the original edge copies
leaving the corresponding uncontracted vertex union. -/
theorem image_legalContracted_boundary_eq_clusterBoundary
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) :
    ((legalContractedGraph G P).boundary B).image
        (legalContractedOrigin G P) =
      Section44.clusterBoundary G (selectedUnion B) := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hcross :=
      ((legalContractedGraph G P).mem_boundary B i).1 hi
    have hedge : G.Adj
        (chosenLeft (legalContractedOrigin G P i))
        (chosenRight (legalContractedOrigin G P i)) := by
      have hedge' := legalContractedOrigin_mem_edgeFinset G P i
      rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)] at hedge'
      simpa [_root_.SimpleGraph.mem_edgeFinset] using hedge'
    rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)]
    apply (mk_mem_clusterBoundary_iff G (selectedUnion B) _ _).2
    refine ⟨hedge, ?_⟩
    rcases hcross with hcross | hcross
    · left
      constructor
      · apply (mem_selectedUnion_iff B _).2
        simpa using hcross.1
      · intro hright
        apply hcross.2
        simpa using (mem_selectedUnion_iff B _).1 hright
    · right
      constructor
      · apply (mem_selectedUnion_iff B _).2
        simpa using hcross.1
      · intro hleft
        apply hcross.2
        simpa using (mem_selectedUnion_iff B _).1 hleft
  · intro he
    have hcross :=
      clusterBoundary_selectedUnion_subset_crossBlockOriginalEdges G P B he
    obtain ⟨i, hi⟩ :=
      indexedOriginalEdge_surjective_crossBlock G P hcross
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply ((legalContractedGraph G P).mem_boundary B i).2
    have he' :
        legalContractedOrigin G P i ∈
          Section44.clusterBoundary G (selectedUnion B) := by
      simpa [legalContractedOrigin, hi] using he
    rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)] at he'
    rcases (mk_mem_clusterBoundary_iff G (selectedUnion B) _ _).1 he' with
      ⟨_, hends | hends⟩
    · left
      constructor
      · rw [legalContracted_left]
        exact (mem_selectedUnion_iff B _).1 hends.1
      · rw [legalContracted_right]
        intro hright
        exact hends.2 ((mem_selectedUnion_iff B _).2 hright)
    · right
      constructor
      · rw [legalContracted_right]
        exact (mem_selectedUnion_iff B _).1 hends.1
      · rw [legalContracted_left]
        intro hleft
        exact hends.2 ((mem_selectedUnion_iff B _).2 hleft)

/-- Cardinality form of
`image_legalContracted_boundary_eq_clusterBoundary`. -/
theorem legalContracted_boundary_card_eq_clusterBoundary_card
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) :
    ((legalContractedGraph G P).boundary B).card =
      (Section44.clusterBoundary G (selectedUnion B)).card := by
  rw [← image_legalContracted_boundary_eq_clusterBoundary G P B]
  exact (Finset.card_image_of_injective _
    (legalContractedOrigin_injective G P)).symm

theorem oldBlock_subset_selectedUnion_iff
    {P : VertexClustering V} (B : Finset (ContractedVertex P))
    {A : Finset V} (hA : A ∈ P.parts) :
    A ⊆ selectedUnion B ↔ (⟨A, hA⟩ : ContractedVertex P) ∈ B := by
  classical
  constructor
  · intro hsub
    rcases P.nonempty_of_mem_parts hA with ⟨v, hvA⟩
    have hvB := (mem_selectedUnion_iff B v).1 (hsub hvA)
    have heq : contractedVertex P v = (⟨A, hA⟩ : ContractedVertex P) := by
      apply Subtype.ext
      exact P.block_eq_of_mem hA hvA
    exact heq ▸ hvB
  · intro hB v hvA
    apply (mem_selectedUnion_iff B v).2
    have heq : contractedVertex P v = (⟨A, hA⟩ : ContractedVertex P) := by
      apply Subtype.ext
      exact P.block_eq_of_mem hA hvA
    exact heq.symm ▸ hB

/-- Every old block is either selected in full or disjoint from the selected
union. -/
theorem oldBlock_subset_or_disjoint_selectedUnion
    {P : VertexClustering V} (B : Finset (ContractedVertex P))
    {A : Finset V} (hA : A ∈ P.parts) :
    A ⊆ selectedUnion B ∨ Disjoint A (selectedUnion B) := by
  classical
  by_cases hB : (⟨A, hA⟩ : ContractedVertex P) ∈ B
  · exact Or.inl ((oldBlock_subset_selectedUnion_iff B hA).2 hB)
  · right
    rw [Finset.disjoint_left]
    intro v hvA hvC
    apply hB
    have hvB := (mem_selectedUnion_iff B v).1 hvC
    have heq : contractedVertex P v = (⟨A, hA⟩ : ContractedVertex P) := by
      apply Subtype.ext
      exact P.block_eq_of_mem hA hvA
    exact heq ▸ hvB

/-- Avoiding a union of whole old blocks retains precisely the old blocks
disjoint from that union. -/
theorem mem_avoid_selectedUnion_iff
    {P : VertexClustering V} (B : Finset (ContractedVertex P))
    {A : Finset V} :
    A ∈ (P.avoid (selectedUnion B)).parts ↔
      A ∈ P.parts ∧ Disjoint A (selectedUnion B) := by
  classical
  rw [Finpartition.mem_avoid]
  constructor
  · rintro ⟨D, hD, hnot, rfl⟩
    rcases oldBlock_subset_or_disjoint_selectedUnion B hD with
      hsub | hdisjoint
    · exact (hnot hsub).elim
    · rw [Finset.sdiff_eq_self_of_disjoint hdisjoint]
      exact ⟨hD, hdisjoint⟩
  · rintro ⟨hA, hdisjoint⟩
    refine ⟨A, hA, ?_, Finset.sdiff_eq_self_of_disjoint hdisjoint⟩
    intro hsub
    rcases P.nonempty_of_mem_parts hA with ⟨v, hvA⟩
    exact Finset.disjoint_left.mp hdisjoint hvA (hsub hvA)

/-- Replace the vertices in `C` by the parts of `Qc`, retaining the restriction
of `P` to the complement.  For the theorem below `C` is `selectedUnion B`, so
the retained restrictions are exactly old blocks. -/
noncomputable def replacementClustering
    (P : VertexClustering V) (C : Finset V) (Qc : Finpartition C) :
    VertexClustering V :=
  Finpartition.ofExistsUnique
    ((P.avoid C).parts ∪ Qc.parts)
    (fun _ _ => Finset.subset_univ _)
    (by
      intro v _
      by_cases hvC : v ∈ C
      · rcases Qc.existsUnique_mem hvC with ⟨A, hA, hAunique⟩
        refine ⟨A, ⟨Finset.mem_union_right _ hA.1, hA.2⟩, ?_⟩
        intro D hD
        rcases Finset.mem_union.mp hD.1 with hDout | hDin
        · have hvout := (P.avoid C).subset hDout hD.2
          exact ((Finset.mem_sdiff.mp hvout).2 hvC).elim
        · exact hAunique D ⟨hDin, hD.2⟩
      · have hvout : v ∈ (Finset.univ : Finset V) \ C := by
          simp [hvC]
        rcases (P.avoid C).existsUnique_mem hvout with
          ⟨A, hA, hAunique⟩
        refine ⟨A, ⟨Finset.mem_union_left _ hA.1, hA.2⟩, ?_⟩
        intro D hD
        rcases Finset.mem_union.mp hD.1 with hDout | hDin
        · exact hAunique D ⟨hDout, hD.2⟩
        · exact (hvC (Qc.subset hDin hD.2)).elim)
    (by simp)

@[simp] theorem replacementClustering_parts
    (P : VertexClustering V) (C : Finset V) (Qc : Finpartition C) :
    (replacementClustering P C Qc).parts =
      (P.avoid C).parts ∪ Qc.parts := rfl

theorem replacementClustering_block_eq_qc_part
    (P : VertexClustering V) (C : Finset V) (Qc : Finpartition C)
    {v : V} (hvC : v ∈ C) :
    (replacementClustering P C Qc).block v = Qc.part v := by
  apply (replacementClustering P C Qc).block_eq_of_mem
  · rw [replacementClustering_parts]
    exact Finset.mem_union_right _ (Qc.part_mem.2 hvC)
  · exact Qc.mem_part hvC

theorem replacementClustering_block_eq_old_block
    {P : VertexClustering V} (B : Finset (ContractedVertex P))
    (Qc : Finpartition (selectedUnion B))
    {v : V} (hvC : v ∉ selectedUnion B) :
    (replacementClustering P (selectedUnion B) Qc).block v = P.block v := by
  have hdisjoint : Disjoint (P.block v) (selectedUnion B) := by
    rcases oldBlock_subset_or_disjoint_selectedUnion B
      (P.block_mem_parts v) with hsub | hdisjoint
    · exact (hvC (hsub (P.mem_block v))).elim
    · exact hdisjoint
  apply (replacementClustering P (selectedUnion B) Qc).block_eq_of_mem
  · rw [replacementClustering_parts]
    apply Finset.mem_union_left
    exact (mem_avoid_selectedUnion_iff B).2
      ⟨P.block_mem_parts v, hdisjoint⟩
  · exact P.mem_block v

/-- Old cross-block edges with both endpoints in the selected uncontracted
union. -/
noncomputable def oldInternalCrossBlockEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) : Finset (Sym2 V) :=
  crossBlockOriginalEdges G P ∩
    Section44.edgeBoundary G (selectedUnion B) (selectedUnion B)

/-- Legal-contracted internal named edges correspond exactly, via their
original-edge names, to old cross-block original edges internal to the
uncontracted selected union. -/
theorem image_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) :
    (internalEdges (legalContractedGraph G P) B).image
        (legalContractedOrigin G P) =
      oldInternalCrossBlockEdges G P B := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hends :=
      (mem_internalEdges (legalContractedGraph G P) B i).1 hi
    have hleftC :
        chosenLeft (legalContractedOrigin G P i) ∈ selectedUnion B := by
      apply (mem_selectedUnion_iff B _).2
      simpa using hends.1
    have hrightC :
        chosenRight (legalContractedOrigin G P i) ∈ selectedUnion B := by
      apply (mem_selectedUnion_iff B _).2
      simpa using hends.2
    apply Finset.mem_inter.mpr
    refine ⟨indexedOriginalEdge_mem_crossBlock G P i, ?_⟩
    rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)]
    apply (mk_mem_edgeBoundary_iff G _ _ _ _).2
    refine ⟨?_, Or.inl ⟨hleftC, hrightC⟩⟩
    have hedge := legalContractedOrigin_mem_edgeFinset G P i
    rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)] at hedge
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hedge
  · intro he
    rcases Finset.mem_inter.mp he with ⟨hcross, hinternal⟩
    obtain ⟨i, hi⟩ :=
      indexedOriginalEdge_surjective_crossBlock G P hcross
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply (mem_internalEdges (legalContractedGraph G P) B i).2
    have hinternal' :
        legalContractedOrigin G P i ∈
          Section44.edgeBoundary G (selectedUnion B) (selectedUnion B) := by
      simpa [legalContractedOrigin, hi] using hinternal
    rw [← sym2_mk_chosenEndpoints (legalContractedOrigin G P i)] at hinternal'
    rcases (mk_mem_edgeBoundary_iff G _ _ _ _).1 hinternal' with
      ⟨_, hends | hends⟩
    · constructor
      · simpa using (mem_selectedUnion_iff B _).1 hends.1
      · simpa using (mem_selectedUnion_iff B _).1 hends.2
    · constructor
      · simpa using (mem_selectedUnion_iff B _).1 hends.2
      · simpa using (mem_selectedUnion_iff B _).1 hends.1

theorem card_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P)) :
    (internalEdges (legalContractedGraph G P) B).card =
      (oldInternalCrossBlockEdges G P B).card := by
  rw [← image_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
    G P B]
  exact (Finset.card_image_of_injective _
    (legalContractedOrigin_injective G P)).symm

theorem crossingEdges_subset_internalEdgeBoundary
    (G : _root_.SimpleGraph V) (C : Finset V) (Qc : Finpartition C) :
    crossingEdges G C Qc ⊆ Section44.edgeBoundary G C C :=
  by
    classical
    exact Finset.filter_subset _ _

/-- The replacement changes only the old cross-block edges internal to the
selected union.  Those edges are removed and replaced by the crossing edges
of `Qc`, including edges that split one old block. -/
theorem crossBlockOriginalEdges_replacement
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P))
    (Qc : Finpartition (selectedUnion B)) :
    crossBlockOriginalEdges G
        (replacementClustering P (selectedUnion B) Qc) =
      (crossBlockOriginalEdges G P \
          Section44.edgeBoundary G (selectedUnion B) (selectedUnion B)) ∪
        crossingEdges G (selectedUnion B) Qc := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mk_mem_crossBlockOriginalEdges, Finset.mem_union,
        Finset.mem_sdiff, mk_mem_edgeBoundary_iff, mk_mem_crossingEdges]
      by_cases huC : u ∈ selectedUnion B
      · have hQu := replacementClustering_block_eq_qc_part
          P (selectedUnion B) Qc huC
        by_cases hvC : v ∈ selectedUnion B
        · have hQv := replacementClustering_block_eq_qc_part
            P (selectedUnion B) Qc hvC
          simp [huC, hvC, hQu, hQv]
          tauto
        · have hQv := replacementClustering_block_eq_old_block B Qc hvC
          have hPsub : P.block u ⊆ selectedUnion B := by
            apply (oldBlock_subset_selectedUnion_iff B
              (P.block_mem_parts u)).2
            exact (mem_selectedUnion_iff B u).1 huC
          have hPne : P.block u ≠ P.block v := by
            intro heq
            apply hvC
            apply hPsub
            rw [heq]
            exact P.mem_block v
          have hQne :
              (replacementClustering P (selectedUnion B) Qc).block u ≠
                (replacementClustering P (selectedUnion B) Qc).block v := by
            intro heq
            apply hvC
            apply Qc.part_subset u
            rw [← hQu, heq]
            exact (replacementClustering P (selectedUnion B) Qc).mem_block v
          simp [huC, hvC, hPne, hQne]
      · have hQu := replacementClustering_block_eq_old_block B Qc huC
        by_cases hvC : v ∈ selectedUnion B
        · have hQv := replacementClustering_block_eq_qc_part
            P (selectedUnion B) Qc hvC
          have hPsub : P.block v ⊆ selectedUnion B := by
            apply (oldBlock_subset_selectedUnion_iff B
              (P.block_mem_parts v)).2
            exact (mem_selectedUnion_iff B v).1 hvC
          have hPne : P.block u ≠ P.block v := by
            intro heq
            apply huC
            apply hPsub
            rw [← heq]
            exact P.mem_block u
          have hQne :
              (replacementClustering P (selectedUnion B) Qc).block u ≠
                (replacementClustering P (selectedUnion B) Qc).block v := by
            intro heq
            apply huC
            apply Qc.part_subset v
            rw [← hQv, ← heq]
            exact (replacementClustering P (selectedUnion B) Qc).mem_block u
          simp [huC, hvC, hPne, hQne]
        · have hQv := replacementClustering_block_eq_old_block B Qc hvC
          simp [huC, hvC, hQu, hQv]

/-- The strict local saving in the selected block is a strict saving in the
global number of cross-block original edges. -/
theorem crossBlockOriginalEdges_replacement_card_lt
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (B : Finset (ContractedVertex P))
    (Qc : Finpartition (selectedUnion B))
    (hsaving :
      (crossingEdges G (selectedUnion B) Qc).card <
        (internalEdges (legalContractedGraph G P) B).card) :
    (crossBlockOriginalEdges G
        (replacementClustering P (selectedUnion B) Qc)).card <
      (crossBlockOriginalEdges G P).card := by
  classical
  let inside :=
    Section44.edgeBoundary G (selectedUnion B) (selectedUnion B)
  let retained := crossBlockOriginalEdges G P \ inside
  have hcrossingInside :
      crossingEdges G (selectedUnion B) Qc ⊆ inside :=
    crossingEdges_subset_internalEdgeBoundary G (selectedUnion B) Qc
  have hretainedCrossing :
      Disjoint retained (crossingEdges G (selectedUnion B) Qc) := by
    rw [Finset.disjoint_left]
    intro e heRetained heCrossing
    have heRetained' :
        e ∈ crossBlockOriginalEdges G P \ inside := heRetained
    exact (Finset.mem_sdiff.mp heRetained').2
      (hcrossingInside heCrossing)
  have hretainedOld :
      Disjoint retained (oldInternalCrossBlockEdges G P B) := by
    rw [Finset.disjoint_left]
    intro e heRetained heOld
    have heRetained' :
        e ∈ crossBlockOriginalEdges G P \ inside := heRetained
    exact (Finset.mem_sdiff.mp heRetained').2
      (Finset.mem_inter.mp heOld).2
  have hPdecomp :
      retained ∪ oldInternalCrossBlockEdges G P B =
        crossBlockOriginalEdges G P := by
    ext e
    simp [retained, inside, oldInternalCrossBlockEdges]
    tauto
  have hsaving' :
      (crossingEdges G (selectedUnion B) Qc).card <
        (oldInternalCrossBlockEdges G P B).card := by
    rw [← card_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
      G P B]
    exact hsaving
  calc
    (crossBlockOriginalEdges G
        (replacementClustering P (selectedUnion B) Qc)).card =
        retained.card +
          (crossingEdges G (selectedUnion B) Qc).card := by
            rw [crossBlockOriginalEdges_replacement]
            exact Finset.card_union_of_disjoint hretainedCrossing
    _ < retained.card + (oldInternalCrossBlockEdges G P B).card :=
      Nat.add_lt_add_left hsaving' _
    _ = (crossBlockOriginalEdges G P).card := by
      rw [← Finset.card_union_of_disjoint hretainedOld, hPdecomp]

/-- If all replacement parts are small and have the target truncated
bandwidth, the explicit replacement is a good global clustering. -/
theorem replacementClustering_isGood_of_all_small
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : Nat)
    (P : VertexClustering V)
    (hminimum :
      IsMinimumGoodClustering G terminals
        threshold cap alphaNum alphaDen P)
    (B : Finset (ContractedVertex P))
    (hBterm : Disjoint B (contractedTerminals P terminals))
    (Qc : Finpartition (selectedUnion B))
    (hbandwidth :
      IsBandwidthDecomposition G (selectedUnion B)
        cap alphaNum alphaDen Qc)
    (hsmall :
      ∀ U ∈ Qc.parts, IsSmallCluster G threshold U) :
    IsGood G terminals threshold cap alphaNum alphaDen
      (replacementClustering P (selectedUnion B) Qc) := by
  classical
  let Q := replacementClustering P (selectedUnion B) Qc
  have hpartCases :
      ∀ U ∈ Q.parts,
        (U ∈ P.parts ∧ Disjoint U (selectedUnion B)) ∨
          U ∈ Qc.parts := by
    intro U hU
    change U ∈
      (replacementClustering P (selectedUnion B) Qc).parts at hU
    rw [replacementClustering_parts] at hU
    rcases Finset.mem_union.mp hU with hUout | hUin
    · exact Or.inl ((mem_avoid_selectedUnion_iff B).1 hUout)
    · exact Or.inr hUin
  have hallSmall :
      ∀ U ∈ Q.parts, IsSmallCluster G threshold U := by
    intro U hU
    rcases hpartCases U hU with hUold | hUnew
    · exact hminimum.good.2 U hUold.1
    · exact hsmall U hUnew
  have hallBandwidth :
      ∀ U ∈ Q.parts,
        TruncatedScaledBandwidth G U cap alphaNum alphaDen := by
    intro U hU
    rcases hpartCases U hU with hUold | hUnew
    · exact hminimum.good.all_bandwidth hUold.1
    · exact hbandwidth U hUnew
  refine ⟨?_, hallSmall⟩
  refine
    { terminal_singleton := ?_
      small_bandwidth := fun U hU _ => hallBandwidth U hU
      large_connected := ?_ }
  · intro t ht
    have hsingleP :
        ({t} : Finset V) ∈ P.parts :=
      hminimum.good.1.terminal_singleton t ht
    have hterminal :
        contractedVertex P t ∈ contractedTerminals P terminals := by
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have htC : t ∉ selectedUnion B := by
      intro htC
      have htB := (mem_selectedUnion_iff B t).1 htC
      exact Finset.disjoint_left.mp hBterm htB hterminal
    have hsingleDisjoint :
        Disjoint ({t} : Finset V) (selectedUnion B) := by
      simp [htC]
    change ({t} : Finset V) ∈
      (replacementClustering P (selectedUnion B) Qc).parts
    rw [replacementClustering_parts]
    apply Finset.mem_union_left
    exact (mem_avoid_selectedUnion_iff B).2
      ⟨hsingleP, hsingleDisjoint⟩
  · intro U hU hlarge
    exact ((smallCluster_iff_not_largeCluster G threshold U).1
      (hallSmall U hU) hlarge).elim

/-- Section 5.1 dense-block replacement contradiction.  A bandwidth
decomposition whose internal crossing edges are fewer than the selected
legal-contracted internal named edges must contain a large part; the returned
part retains both its decomposition membership and target bandwidth. -/
theorem exists_large_bandwidth_part_of_dense_block_replacement
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : Nat)
    (P : VertexClustering V)
    (hminimum :
      IsMinimumGoodClustering G terminals
        threshold cap alphaNum alphaDen P)
    (B : Finset (ContractedVertex P))
    (hBterm : Disjoint B (contractedTerminals P terminals))
    (Qc : Finpartition (selectedUnion B))
    (hbandwidth :
      IsBandwidthDecomposition G (selectedUnion B)
        cap alphaNum alphaDen Qc)
    (hsaving :
      (crossingEdges G (selectedUnion B) Qc).card <
        (internalEdges (legalContractedGraph G P) B).card) :
    ∃ U, U ∈ Qc.parts ∧
      IsLargeCluster G threshold U ∧
      TruncatedScaledBandwidth G U cap alphaNum alphaDen := by
  classical
  by_contra hnone
  have hsmall :
      ∀ U ∈ Qc.parts, IsSmallCluster G threshold U := by
    intro U hU
    apply (smallCluster_iff_not_largeCluster G threshold U).2
    intro hlarge
    apply hnone
    exact ⟨U, hU, hlarge, hbandwidth U hU⟩
  let Q := replacementClustering P (selectedUnion B) Qc
  have hQgood :
      IsGood G terminals threshold cap alphaNum alphaDen Q := by
    exact replacementClustering_isGood_of_all_small
      G terminals threshold cap alphaNum alphaDen P hminimum B hBterm
      Qc hbandwidth hsmall
  have hstrict :
      (crossBlockOriginalEdges G Q).card <
        (crossBlockOriginalEdges G P).card := by
    exact crossBlockOriginalEdges_replacement_card_lt G P B Qc hsaving
  have hminimal := hminimum.minimal Q hQgood
  omega

end ChekuriChuzhoySection5DenseBlockReplacement
end SimpleGraph

end Lax17Proofs
