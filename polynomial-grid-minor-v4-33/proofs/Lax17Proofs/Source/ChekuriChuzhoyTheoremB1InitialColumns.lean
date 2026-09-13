import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorTrace

namespace Lax17Proofs

universe u v w

/-!
# Initial full columns for both branches of Theorem B.1

The page-59 extraction already supplies `h` disjoint `Q*` paths in either the
type-one or type-two corridor.  This module converts both families to the
common full boundary-to-boundary column state.  Type-one paths are reversed so
that all columns are oriented from the lower to the upper boundary; type-two
paths already have that orientation.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1
namespace IndexedAuxiliaryPrefix


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {L : PerfectPathPacking G A B} {h : ℕ}

private theorem singleton_of_card_one_mem
    {α : Type*} [DecidableEq α] {S : Finset α} {x : α}
    (hcard : S.card = 1) (hx : x ∈ S) :
    S = {x} := by
  rcases Finset.card_eq_one.mp hcard with ⟨y, rfl⟩
  have hxy : x = y := by simpa using hx
  subst x
  rfl

/-- The linkage indices of the type-one corridor are exactly the paper's
type-one allowed set. -/
theorem typeOneAllowedIndexSet_eq_range_corridor
    (R : IndexedAuxiliaryPrefix L h) (hpos : 0 < h) :
    (typeOneAllowedIndexSet R hpos : Set L.Index) =
      Set.range (R.typeOneAuxiliaryCorridor hpos).index := by
  classical
  ext j
  constructor
  · intro hj
    have hj' :
        j = R.p0Index ∨
          j = R.pZPlusOneIndex hpos ∨ j ∈ R.block1IndexSet := by
      simpa [typeOneAllowedIndexSet] using hj
    rcases hj' with rfl | rfl | hjblock
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [AuxiliaryCorridor.lowerIndex,
        IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.p0Index, IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, p0Pos]
    · refine ⟨⟨z h + 1, by omega⟩, ?_⟩
      simp [IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.pZPlusOneIndex,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, pZPlusOnePos]
    · rw [R.mem_block1IndexSet_iff] at hjblock
      rcases hjblock with ⟨i, rfl⟩
      refine ⟨⟨i.1 + 1, by omega⟩, ?_⟩
      apply congrArg R.index
      apply Fin.ext
      simp [IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, windowPos]
      omega
  · rintro ⟨i, rfl⟩
    by_cases hi0 : i.1 = 0
    · have hi : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        exact hi0
      rw [hi]
      simpa [IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.p0Index, IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, p0Pos] using
        p0Index_mem_typeOneAllowedIndexSet R hpos
    · by_cases hilast : i.1 = z h + 1
      · have hi : i = ⟨z h + 1, by omega⟩ := by
          apply Fin.ext
          exact hilast
        rw [hi]
        simpa [IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
          IndexedAuxiliaryPrefix.pZPlusOneIndex,
          IndexedAuxiliaryPrefix.indexAt,
          IndexedAuxiliaryPrefix.posOfNat, pZPlusOnePos] using
          pZPlusOneIndex_mem_typeOneAllowedIndexSet R hpos
      · exact indexAt_mem_typeOneAllowedIndexSet_of_between_one_zPlusOne
          R hpos (by
            have hi := i.2
            dsimp [z] at hi ⊢
            omega) (by omega) (by omega)

/-- The linkage indices of the type-two corridor are exactly the paper's
type-two allowed set. -/
theorem typeTwoAllowedIndexSet_eq_range_corridor
    (R : IndexedAuxiliaryPrefix L h) (hpos : 0 < h) :
    (typeTwoAllowedIndexSet R hpos : Set L.Index) =
      Set.range (R.typeTwoAuxiliaryCorridor hpos).index := by
  classical
  ext j
  constructor
  · intro hj
    have hj' :
        j = R.pTwoZIndex hpos ∨
          j = R.pThreeZPlusOneIndex hpos ∨ j ∈ R.block3IndexSet := by
      simpa [typeTwoAllowedIndexSet] using hj
    rcases hj' with rfl | rfl | hjblock
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.pTwoZIndex,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, pTwoZPos]
    · refine ⟨⟨z h + 1, by omega⟩, ?_⟩
      apply congrArg R.index
      apply Fin.ext
      simp [IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.pThreeZPlusOneIndex,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, pThreeZPlusOnePos]
      omega
    · rw [R.mem_block3IndexSet_iff] at hjblock
      rcases hjblock with ⟨i, rfl⟩
      refine ⟨⟨i.1 + 1, by omega⟩, ?_⟩
      apply congrArg R.index
      apply Fin.ext
      simp [IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, windowPos]
      omega
  · rintro ⟨i, rfl⟩
    exact indexAt_mem_typeTwoAllowedIndexSet_of_between_twoZ_threeZPlusOne
      R hpos (by
        have hi := i.2
        dsimp [z] at hi ⊢
        omega) (by
          dsimp [z]
          omega) (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega)

/-- The selected type-one `Q*` paths, reversed into lower-to-upper
orientation, form a full boundary column family in the first corridor. -/
noncomputable def TypeOneQStarFamily.toFullBoundaryColumnFamily
    {R : IndexedAuxiliaryPrefix L h} {hpos : 0 < h}
    {Q : PerfectPathPacking G R.X R.Y}
    (F : TypeOneQStarFamily R hpos Q) :
    FullBoundaryColumnFamily L (z h) (Fin h)
      (R.typeOneAuxiliaryCorridor hpos) where
  column j :=
    (F.selectedData (F.selectedColumn j)
      (F.selectedColumn_mem_selectedIndexSet j)).qstar.reverse
  pairwise_nodeDisjoint := by
    intro j k hjk
    simpa [GraphPath.NodeDisjoint] using
      F.selectedColumn_qstar_nodeDisjoint hjk
  lower_contact := by
    intro j
    let D :=
      F.selectedData (F.selectedColumn j)
        (F.selectedColumn_mem_selectedIndexSet j)
    have hmem :
        D.qstar.target ∈
          D.qstar.vertexSet ∩ (L.path R.p0Index).vertexSet :=
      Finset.mem_inter.mpr
        ⟨GraphPath.target_mem_vertexSet D.qstar, D.qstar_target_mem_P0⟩
    have heq :
        D.qstar.vertexSet ∩ (L.path R.p0Index).vertexSet =
          {D.qstar.target} :=
      singleton_of_card_one_mem D.qstar_unique_P0 hmem
    simpa [D, AuxiliaryCorridor.rowPath,
      IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
      IndexedAuxiliaryPrefix.p0Index,
      IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat, p0Pos] using heq
  upper_contact := by
    intro j
    let D :=
      F.selectedData (F.selectedColumn j)
        (F.selectedColumn_mem_selectedIndexSet j)
    have hmem :
        D.qstar.source ∈
          D.qstar.vertexSet ∩
            (L.path (R.pZPlusOneIndex hpos)).vertexSet :=
      Finset.mem_inter.mpr
        ⟨GraphPath.source_mem_vertexSet D.qstar,
          D.qstar_source_mem_PzPlusOne⟩
    have heq :
        D.qstar.vertexSet ∩
            (L.path (R.pZPlusOneIndex hpos)).vertexSet =
          {D.qstar.source} :=
      singleton_of_card_one_mem D.qstar_unique_PzPlusOne hmem
    simpa [D, AuxiliaryCorridor.rowPath,
      IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor,
      IndexedAuxiliaryPrefix.pZPlusOneIndex,
      IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat, pZPlusOnePos] using heq
  avoidsOutside := by
    intro j l hl
    have hl' : l ∉ typeOneAllowedIndexSet R hpos := by
      intro hmem
      apply hl
      rw [← R.typeOneAllowedIndexSet_eq_range_corridor hpos]
      exact hmem
    simpa using
      F.selectedColumn_avoids_other_linkage F.initialCurrentRowsInvariant j l hl'

/-- The selected type-two `Q*` paths already have lower-to-upper orientation
and form a full boundary column family in the symmetric corridor. -/
noncomputable def TypeTwoQStarFamily.toFullBoundaryColumnFamily
    {R : IndexedAuxiliaryPrefix L h} {hpos : 0 < h}
    {Q : PerfectPathPacking G R.X R.Y}
    (F : TypeTwoQStarFamily R hpos Q) :
    FullBoundaryColumnFamily L (z h) (Fin h)
      (R.typeTwoAuxiliaryCorridor hpos) where
  column j :=
    (F.selectedData (F.selectedColumn j)
      (F.selectedColumn_mem_selectedIndexSet j)).qstar
  pairwise_nodeDisjoint := by
    intro j k hjk
    exact F.selectedColumn_qstar_nodeDisjoint hjk
  lower_contact := by
    intro j
    let D :=
      F.selectedData (F.selectedColumn j)
        (F.selectedColumn_mem_selectedIndexSet j)
    have hmem :
        D.qstar.source ∈
          D.qstar.vertexSet ∩
            (L.path (R.pTwoZIndex hpos)).vertexSet :=
      Finset.mem_inter.mpr
        ⟨GraphPath.source_mem_vertexSet D.qstar,
          D.qstar_source_mem_PtwoZ⟩
    have heq :
        D.qstar.vertexSet ∩
            (L.path (R.pTwoZIndex hpos)).vertexSet =
          {D.qstar.source} :=
      singleton_of_card_one_mem D.qstar_unique_PtwoZ hmem
    simpa [D, AuxiliaryCorridor.rowPath,
      IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor,
      IndexedAuxiliaryPrefix.pTwoZIndex,
      IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat, pTwoZPos] using heq
  upper_contact := by
    intro j
    let D :=
      F.selectedData (F.selectedColumn j)
        (F.selectedColumn_mem_selectedIndexSet j)
    have hmem :
        D.qstar.target ∈
          D.qstar.vertexSet ∩
            (L.path (R.pThreeZPlusOneIndex hpos)).vertexSet :=
      Finset.mem_inter.mpr
        ⟨GraphPath.target_mem_vertexSet D.qstar,
          D.qstar_target_mem_PthreeZPlusOne⟩
    have heq :
        D.qstar.vertexSet ∩
            (L.path (R.pThreeZPlusOneIndex hpos)).vertexSet =
          {D.qstar.target} :=
      singleton_of_card_one_mem D.qstar_unique_PthreeZPlusOne hmem
    have hindex :
        (R.typeTwoAuxiliaryCorridor hpos).index
            ⟨z h + 1, by omega⟩ =
          R.pThreeZPlusOneIndex hpos := by
      apply congrArg R.index
      apply Fin.ext
      simp [IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor,
        IndexedAuxiliaryPrefix.pThreeZPlusOneIndex,
        IndexedAuxiliaryPrefix.indexAt,
        IndexedAuxiliaryPrefix.posOfNat, pThreeZPlusOnePos]
      omega
    simpa [D, AuxiliaryCorridor.rowPath, hindex] using heq
  avoidsOutside := by
    intro j l hl
    have hl' : l ∉ typeTwoAllowedIndexSet R hpos := by
      intro hmem
      apply hl
      rw [← R.typeTwoAllowedIndexSet_eq_range_corridor hpos]
      exact hmem
    exact
      F.selectedColumn_avoids_other_linkage
        F.initialCurrentRowsInvariant j l hl'

end IndexedAuxiliaryPrefix
end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
