import Lax17Proofs.Source.Exponent8.ParentedClusterTable

namespace Lax17Proofs

/-!
# Section 5.1 large-slice exit through Theorem 4.15

This module generalizes the one-cluster-per-slice construction
`section45Input_of_slicedHappyCores` to the parent-ordered table of all happy
clusters.  Theorem 4.15 orders table entries.  Positive overlap and
same-parent row disjointness then force consecutive entries to have strictly
increasing *parent slice* indices, which are the indices used by
`rowGapPacking`.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset
open Section44

namespace ParentedHappyClusterTable

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width g C Dclass : ℕ}
    {L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4)}

/-- Chuzhoy--Tan Section 5.1, Case 1: the corrected dyadic happy-cluster
table supplies the complete proof-facing input to Theorem 4.15 and the
subsequent path-of-sets assembly. -/
theorem section45Input
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (hg : 0 < g)
    (hN : 3 * g ^ 2 ≤ Rbar.card)
    (hDsq : 4 * Rbar.card * g ^ 2 ≤ Dclass ^ 2) :
    Nonempty
      (Section45.Section45Input
        H Rbar.card C Dclass (g ^ 2)) := by
  classical
  have hw : 0 < g ^ 2 := by positivity
  have hrowCard :
      ∀ c : Fin C, Dclass ≤ (T.sliceRows c).card := by
    intro c
    rw [T.sliceRows_card]
    exact T.row_card c
  obtain
      ⟨firstRows, gapRows, hfirstSubset, hfirstCard,
        hgapLeft, hgapRight, hgapCard⟩ :=
    Section45.exists_paperRows T.sliceRows hw
      (by
        calc
          g ^ 2 ≤ g ^ 4 :=
            Nat.pow_le_pow_right hg (by omega)
          _ ≤ 16 * g ^ 4 :=
            Nat.le_mul_of_pos_left _ (by omega)
          _ ≤ Dclass := T.depth_base)
      hrowCard
  let leftRows :=
    fun (l : List (Fin C)) (hlen : l.length = g ^ 2)
      (hchain : l.IsChain
        (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
      (i : Fin (g ^ 2)) =>
      Section45.paperLeftRows firstRows gapRows l hlen hchain i
  let rightRows :=
    fun (l : List (Fin C)) (hlen : l.length = g ^ 2)
      (hchain : l.IsChain
        (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
      (i : Fin (g ^ 2)) =>
      Section45.paperRightRows firstRows gapRows l hlen hchain i
  have hleftSubset :
      ∀ (l : List (Fin C)) (hlen : l.length = g ^ 2)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
        (i : Fin (g ^ 2)),
        leftRows l hlen hchain i ⊆
          T.sliceRows (Section45.selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · have h0lt : 0 < g ^ 2 := by simpa [h0] using i.2
      have hi : i = ⟨0, h0lt⟩ := Fin.ext h0
      simpa [leftRows, Section45.paperLeftRows, h0, hi] using
        hfirstSubset l hlen hchain
    · let k : Fin (g ^ 2) := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < g ^ 2 := by
        dsimp [k]
        omega
      have hnext : (⟨k.1 + 1, hk⟩ : Fin (g ^ 2)) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa [leftRows, Section45.paperLeftRows, h0, k, hk, hnext] using
        hgapRight l hlen hchain k hk
  have hrightSubset :
      ∀ (l : List (Fin C)) (hlen : l.length = g ^ 2)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
        (i : Fin (g ^ 2)),
        rightRows l hlen hchain i ⊆
          T.sliceRows (Section45.selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < g ^ 2
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hgapLeft l hlen hchain i hi
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hleftSubset l hlen hchain i
  have hleftCard :
      ∀ (l : List (Fin C)) (hlen : l.length = g ^ 2)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
        (i : Fin (g ^ 2)),
        (leftRows l hlen hchain i).card = g ^ 2 := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · simpa [leftRows, Section45.paperLeftRows, h0] using
        hfirstCard l hlen hchain
    · let k : Fin (g ^ 2) := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < g ^ 2 := by
        dsimp [k]
        omega
      simpa [leftRows, Section45.paperLeftRows, h0, k, hk] using
        hgapCard l hlen hchain k hk
  have hrightCard :
      ∀ (l : List (Fin C)) (hlen : l.length = g ^ 2)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
        (i : Fin (g ^ 2)),
        (rightRows l hlen hchain i).card = g ^ 2 := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < g ^ 2
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hgapCard l hlen hchain i hi
    · simpa [rightRows, Section45.paperRightRows, hi] using
        hleftCard l hlen hchain i
  let connector :
      ∀ (l : List (Fin C)) (hlen : l.length = g ^ 2)
        (hchain : l.IsChain
          (Section45.LargeOverlapRel T.sliceRows (g ^ 2)))
        (i : Fin (g ^ 2)) (hi : i.1 + 1 < g ^ 2),
        PerfectPathPacking H
          ((rightRows l hlen hchain i).image
            (T.rightEndpoint (Section45.selectedIndex l hlen i)))
          ((leftRows l hlen hchain ⟨i.1 + 1, hi⟩).image
            (T.leftEndpoint
              (Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩))) :=
    fun l hlen hchain i hi =>
      let a := Section45.selectedIndex l hlen i
      let b := Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩
      let hrel : Section45.LargeOverlapRel
          T.sliceRows (g ^ 2) a b :=
        Section45.selectedIndex_chain_succ hlen hchain i hi
      let hlt : T.parent a < T.parent b :=
        T.parent_lt_of_largeOverlap hg hrel
      let IFin := gapRows l hlen hchain i hi
      let IBase : Finset Rbar.Index := IFin.image Rbar.finIndexEquiv
      let hne : ∀ r ∈ IBase,
          L.sigma.cut r (T.parent a).castSucc ≠
            L.sigma.cut r (T.parent a).succ := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨rfin, hrfin, rfl⟩
        apply L.sigma.cut_ne_of_mem_cleanedRows Qbar
          (T.parent a) (L.happyCleanup (T.parent a)).toOrdinary hw
        apply T.rows_subset_cleanup a
        apply (T.mem_sliceRows_iff a rfin).1
        exact hgapLeft l hlen hchain i hi hrfin
      (L.sigma.rowGapPacking hlt IBase hne).copyTerminals
        (by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨r, hr, hrx⟩
            rcases Finset.mem_image.mp hr with ⟨rfin, hrfin, rfl⟩
            have hrRight : rfin ∈ rightRows l hlen hchain i := by
              simpa [rightRows, Section45.paperRightRows, hi] using hrfin
            exact Finset.mem_image.2
              ⟨rfin, hrRight,
                by simpa [rightEndpoint] using hrx⟩
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨rfin, hrfin, hrx⟩
            have hrGap : rfin ∈ IFin := by
              simpa [rightRows, Section45.paperRightRows, hi] using hrfin
            exact Finset.mem_image.2
              ⟨Rbar.finIndexEquiv rfin,
                Finset.mem_image.2 ⟨rfin, hrGap, rfl⟩,
                by simpa [rightEndpoint] using hrx⟩)
        (by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨r, hr, hrx⟩
            rcases Finset.mem_image.mp hr with ⟨rfin, hrfin, rfl⟩
            have hrLeft :
                rfin ∈
                  leftRows l hlen hchain ⟨i.1 + 1, hi⟩ := by
              simp only [leftRows, Section45.paperLeftRows]
              simpa using hrfin
            exact Finset.mem_image.2
              ⟨rfin, hrLeft,
                by simpa [leftEndpoint] using hrx⟩
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨rfin, hrfin, hrx⟩
            have hrGap : rfin ∈ IFin := by
              simp only [leftRows, Section45.paperLeftRows] at hrfin
              simpa using hrfin
            exact Finset.mem_image.2
              ⟨Rbar.finIndexEquiv rfin,
                Finset.mem_image.2 ⟨rfin, hrGap, rfl⟩,
                by simpa [leftEndpoint] using hrx⟩)
  let _ := connector
  exact ⟨by
    refine {
      sliceRows := T.sliceRows
      width_pos := hw
      N_large := hN
      D_square := hDsq
      large := T.count_mass
      row_card := hrowCard
      cluster := fun l hlen hchain i =>
        T.cluster (Section45.selectedIndex l hlen i)
      cluster_connected := ?_
      cluster_disjoint := ?_
      left := fun l hlen hchain i =>
        (leftRows l hlen hchain i).image
          (T.leftEndpoint (Section45.selectedIndex l hlen i))
      right := fun l hlen hchain i =>
        (rightRows l hlen hchain i).image
          (T.rightEndpoint (Section45.selectedIndex l hlen i))
      left_subset_cluster := ?_
      right_subset_cluster := ?_
      left_right_disjoint := ?_
      left_card := ?_
      right_card := ?_
      connector := connector
      connector_card := ?_
      connector_internally_disjoint_clusters := ?_
      connector_mutually_nodeDisjoint := ?_
      nails_weakWellLinked := ?_
    }
    · intro l hlen hchain i
      exact T.cluster_connected _
    · intro l hlen hchain i j hij
      apply T.cluster_disjoint
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · exact ne_of_lt
          (Section45.selectedIndex_lt_of_lt hlen hchain hijlt)
      · exact fun heq =>
          (ne_of_lt
            (Section45.selectedIndex_lt_of_lt hlen hchain hjilt))
            heq.symm
    · intro l hlen hchain i x hx
      rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      exact T.leftEndpoint_mem _
        (hleftSubset l hlen hchain i hr)
    · intro l hlen hchain i x hx
      rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      exact T.rightEndpoint_mem _
        (hrightSubset l hlen hchain i hr)
    · intro l hlen hchain i
      rw [Finset.disjoint_left]
      intro x hxL hxR
      rcases Finset.mem_image.mp hxL with ⟨r, hr, hrx⟩
      rcases Finset.mem_image.mp hxR with ⟨s, hs, hsx⟩
      let a := Section45.selectedIndex l hlen i
      by_cases hrs : r = s
      · subst s
        have hne :=
          L.sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
            Qbar (T.parent a)
            (L.happyCleanup (T.parent a)).toOrdinary hw
            (T.rows_subset_cleanup a
              ((T.mem_sliceRows_iff a r).1
                (hleftSubset l hlen hchain i hr)))
        exact hne (hrx.trans hsx.symm)
      · have hbaseNe :
            Rbar.finIndexEquiv r ≠ Rbar.finIndexEquiv s :=
          fun h => hrs (Rbar.finIndexEquiv.injective h)
        have hxSource :
            x ∈
              ((L.sigma.sliceRowPacking (T.parent a)).path
                (Rbar.finIndexEquiv r)).vertexSet := by
          change
            ((L.sigma.sliceRowPacking (T.parent a)).path
              (Rbar.finIndexEquiv r)).source = x at hrx
          rw [← hrx]
          exact GraphPath.source_mem_vertexSet _
        have hxTarget :
            x ∈
              ((L.sigma.sliceRowPacking (T.parent a)).path
                (Rbar.finIndexEquiv s)).vertexSet := by
          change
            ((L.sigma.sliceRowPacking (T.parent a)).path
              (Rbar.finIndexEquiv s)).target = x at hsx
          rw [← hsx]
          exact GraphPath.target_mem_vertexSet _
        exact Finset.disjoint_left.mp
          ((L.sigma.sliceRowPacking
            (T.parent a)).node_disjoint hbaseNe)
          hxSource hxTarget
    · intro l hlen hchain i
      rw [Finset.card_image_of_injective]
      · exact hleftCard l hlen hchain i
      · exact T.leftEndpoint_injective _
    · intro l hlen hchain i
      rw [Finset.card_image_of_injective]
      · exact hrightCard l hlen hchain i
      · exact T.rightEndpoint_injective _
    · intro l hlen hchain i hi
      rw [(connector l hlen hchain i hi).card_eq_left_card]
      rw [Finset.card_image_of_injective]
      · exact hrightCard l hlen hchain i
      · exact T.rightEndpoint_injective _
    · intro l hlen hchain i hi j
      intro p x hxp hxC
      dsimp [connector] at p hxp
      let a := Section45.selectedIndex l hlen i
      let b :=
        Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩
      let k := Section45.selectedIndex l hlen j
      have habRel :
          Section45.LargeOverlapRel T.sliceRows (g ^ 2) a b :=
        Section45.selectedIndex_chain_succ hlen hchain i hi
      have hab : T.parent a < T.parent b :=
        T.parent_lt_of_largeOverlap hg habRel
      have houtside :
          T.parent k ≤ T.parent a ∨ T.parent b ≤ T.parent k := by
        by_cases hji : j ≤ i
        · apply Or.inl
          apply T.parent_monotone
          exact Section45.selectedIndex_le_of_le hlen hchain hji
        · apply Or.inr
          apply T.parent_monotone
          exact Section45.selectedIndex_le_of_le hlen hchain
            (show (⟨i.1 + 1, hi⟩ : Fin (g ^ 2)) ≤ j by
              have hij : i < j := lt_of_not_ge hji
              exact Fin.mk_le_mk.2 (Nat.succ_le_iff.2 hij))
      rcases Finset.mem_image.mp p.2 with ⟨pfin, hpfin, hpeq⟩
      have hpRowsFin :
          Rbar.finIndexEquiv pfin ∈ T.rows a :=
        (T.mem_sliceRows_iff a pfin).1
          (hgapLeft l hlen hchain i hi hpfin)
      have hpRows : p.1 ∈ T.rows a := by
        rw [← hpeq]
        exact hpRowsFin
      apply
        (L.sigma.rowGapPath_internallyDisjoint_cleanedSupport
          Qbar hab p.1
          (by
            apply L.sigma.cut_ne_of_mem_cleanedRows
              Qbar (T.parent a)
              (L.happyCleanup (T.parent a)).toOrdinary hw
            exact T.rows_subset_cleanup a hpRows)
          (T.parent k)
          (L.happyCleanup (T.parent k)).toOrdinary hw houtside)
      · simpa [connector, a, b] using hxp
      · exact T.cluster_subset_support k hxC
    · intro l hlen hchain i j hi hj hij
      intro p q
      dsimp [connector] at p q
      let ai := Section45.selectedIndex l hlen i
      let bi :=
        Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩
      let aj := Section45.selectedIndex l hlen j
      let bj :=
        Section45.selectedIndex l hlen ⟨j.1 + 1, hj⟩
      have hiRel :
          Section45.LargeOverlapRel T.sliceRows (g ^ 2) ai bi :=
        Section45.selectedIndex_chain_succ hlen hchain i hi
      have hjRel :
          Section45.LargeOverlapRel T.sliceRows (g ^ 2) aj bj :=
        Section45.selectedIndex_chain_succ hlen hchain j hj
      have hiParent : T.parent ai < T.parent bi :=
        T.parent_lt_of_largeOverlap hg hiRel
      have hjParent : T.parent aj < T.parent bj :=
        T.parent_lt_of_largeOverlap hg hjRel
      rcases Finset.mem_image.mp p.2 with ⟨pfin, hpfin, hpeq⟩
      rcases Finset.mem_image.mp q.2 with ⟨qfin, hqfin, hqeq⟩
      have hpRowsFin :
          Rbar.finIndexEquiv pfin ∈ T.rows ai :=
        (T.mem_sliceRows_iff ai pfin).1
          (hgapLeft l hlen hchain i hi hpfin)
      have hqRowsFin :
          Rbar.finIndexEquiv qfin ∈ T.rows aj :=
        (T.mem_sliceRows_iff aj qfin).1
          (hgapLeft l hlen hchain j hj hqfin)
      have hpRows : p.1 ∈ T.rows ai := by
        rw [← hpeq]
        exact hpRowsFin
      have hqRows : q.1 ∈ T.rows aj := by
        rw [← hqeq]
        exact hqRowsFin
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · apply L.sigma.rowGapPath_disjoint_of_ordered
          hiParent hjParent
          (by
            apply T.parent_monotone
            exact Section45.selectedIndex_le_of_le hlen hchain
              (Fin.mk_le_mk.2 (Nat.succ_le_iff.2 hijlt)))
          (by
            apply L.sigma.cut_ne_of_mem_cleanedRows
              Qbar (T.parent ai)
              (L.happyCleanup (T.parent ai)).toOrdinary hw
            exact T.rows_subset_cleanup ai hpRows)
          (by
            apply L.sigma.cut_ne_of_mem_cleanedRows
              Qbar (T.parent aj)
              (L.happyCleanup (T.parent aj)).toOrdinary hw
            exact T.rows_subset_cleanup aj hqRows)
          (by
            apply L.sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
              Qbar (T.parent aj)
              (L.happyCleanup (T.parent aj)).toOrdinary hw
            exact T.rows_subset_cleanup aj hqRows)
      · exact
          (L.sigma.rowGapPath_disjoint_of_ordered
            hjParent hiParent
            (by
              apply T.parent_monotone
              exact Section45.selectedIndex_le_of_le hlen hchain
                (Fin.mk_le_mk.2 (Nat.succ_le_iff.2 hjilt)))
            (by
              apply L.sigma.cut_ne_of_mem_cleanedRows
                Qbar (T.parent aj)
                (L.happyCleanup (T.parent aj)).toOrdinary hw
              exact T.rows_subset_cleanup aj hqRows)
            (by
              apply L.sigma.cut_ne_of_mem_cleanedRows
                Qbar (T.parent ai)
                (L.happyCleanup (T.parent ai)).toOrdinary hw
              exact T.rows_subset_cleanup ai hpRows)
            (by
              apply L.sigma.sliceRowPath_source_ne_target_of_mem_cleanedRows
                Qbar (T.parent ai)
                (L.happyCleanup (T.parent ai)).toOrdinary hw
              exact T.rows_subset_cleanup ai hpRows)).symm
    · intro l hlen hchain i
      exact T.endpoint_union_weak _ _ _
        (hleftSubset l hlen hchain i)
        (hrightSubset l hlen hchain i)
  ⟩

end ParentedHappyClusterTable

end Exponent8
end SimpleGraph

end Lax17Proofs
