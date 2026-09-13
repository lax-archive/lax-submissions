import Lax17Proofs.Source.FiniteSubtreeHelly
import Lax17Proofs.Source.FlowWellLinked
import Lax17Proofs.Source.TreewidthBrambleDuality

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: Theorem 3.3

This module proves the unit-numerator specialization of Theorem 3.3 from
`treewidth-sparsifier.pdf`.  This is the only specialization used in the proof
of Theorem 1.1.

The proof is the standard bramble argument.  Take all connected vertex sets
containing a strict majority of the terminals.  They form a bramble.  If a
small set met every member, the components left after deleting it could be
grouped into two terminal-rich sides.  Every edge between those sides is
incident with the deleted set, contradicting bounded degree and cut
well-linkedness.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


open TreewidthBramble

private theorem exists_subset_sum_gt_le_two_mul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (b : ℕ)
    (hsum : b < ∑ i ∈ s, f i)
    (hle : ∀ i ∈ s, f i ≤ b) :
    ∃ r : Finset ι, r ⊆ s ∧
      b < ∑ i ∈ r, f i ∧ ∑ i ∈ r, f i ≤ 2 * b := by
  induction s using Finset.induction_on with
  | empty => simp at hsum
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hsum
      by_cases hs : b < ∑ i ∈ s, f i
      · rcases ih hs (fun i hi => hle i (Finset.mem_insert_of_mem hi)) with
          ⟨r, hrs, hrb, hrle⟩
        exact ⟨r, hrs.trans (Finset.subset_insert a s), hrb, hrle⟩
      · refine ⟨insert a s, subset_rfl, ?_, ?_⟩
        · simpa [Finset.sum_insert ha] using hsum
        · rw [Finset.sum_insert ha]
          have hsle : (∑ i ∈ s, f i) ≤ b := Nat.le_of_not_gt hs
          have hale : f a ≤ b := hle a (by simp)
          omega

private theorem componentVertices_pairwiseDisjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (H : Finset V) :
    ((Finset.univ :
      Finset (G.induce {v : V | v ∉ H}).ConnectedComponent) : Set _).PairwiseDisjoint
        (TreewidthBrambleDuality.componentVertices G H) := by
  classical
  intro c _hc d _hd hcd
  change Disjoint
    (TreewidthBrambleDuality.componentVertices G H c)
    (TreewidthBrambleDuality.componentVertices G H d)
  rw [Finset.disjoint_left]
  intro v hvc hvd
  rcases TreewidthBrambleDuality.mem_componentVertices.mp hvc with
    ⟨hvo, hvc⟩
  rcases TreewidthBrambleDuality.mem_componentVertices.mp hvd with
    ⟨hvo', hvd⟩
  apply hcd
  exact hvc.symm.trans (by simpa using hvd)

private theorem componentWeight_sum
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T H : Finset V) :
    ∑ c : (G.induce {v : V | v ∉ H}).ConnectedComponent,
        ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card =
      (T \ H).card := by
  classical
  let K := G.induce {v : V | v ∉ H}
  let U : Finset {v : V // v ∉ H} :=
    Finset.univ.filter fun v => (v : V) ∈ T
  let f : {v : V // v ∉ H} → K.ConnectedComponent :=
    fun v => K.connectedComponentMk v
  have hmaps : ((U : Finset {v : V // v ∉ H}) : Set _).MapsTo
      f (Finset.univ : Finset K.ConnectedComponent) := by
    intro v _hv
    exact Finset.mem_univ _
  have hfiber :
      ∀ c : K.ConnectedComponent,
        ({v ∈ U | f v = c}.image
          fun v : {v : V // v ∉ H} => (v : V)).card =
          ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card := by
    intro c
    have himage :
        ({v ∈ U | f v = c}.image
          fun v : {v : V // v ∉ H} => (v : V)) =
            (TreewidthBrambleDuality.componentVertices G H c) ∩ T := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_image.mp hv with ⟨w, hw, hwv⟩
        rcases Finset.mem_filter.mp hw with ⟨hwU, hwc⟩
        subst v
        exact Finset.mem_inter.mpr
          ⟨TreewidthBrambleDuality.mem_componentVertices.mpr
            ⟨w.2, by simpa [K, f] using hwc⟩,
            (Finset.mem_filter.mp hwU).2⟩
      · intro hv
        rcases Finset.mem_inter.mp hv with ⟨hvC, hvT⟩
        rcases TreewidthBrambleDuality.mem_componentVertices.mp hvC with
          ⟨hvH, hvc⟩
        let w : {x : V // x ∉ H} := ⟨v, hvH⟩
        apply Finset.mem_image.mpr
        refine ⟨w, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨by simp, hvT⟩,
            by simpa [K, f, w] using hvc⟩
    exact congrArg Finset.card himage
  have hcardU : U.card = (T \ H).card := by
    have himage :
        U.image (fun v : {v : V // v ∉ H} => (v : V)) = T \ H := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_image.mp hv with ⟨w, hw, hwv⟩
        subst v
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hw).2, w.2⟩
      · intro hv
        apply Finset.mem_image.mpr
        refine ⟨⟨v, (Finset.mem_sdiff.mp hv).2⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨by simp, (Finset.mem_sdiff.mp hv).1⟩
    calc
      U.card =
          (U.image (fun v : {v : V // v ∉ H} => (v : V))).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = (T \ H).card := congrArg Finset.card himage
  have hfiberSum :=
    Finset.card_eq_sum_card_fiberwise
      (s := U) (t := (Finset.univ : Finset K.ConnectedComponent))
      (f := f) hmaps
  calc
    ∑ c : K.ConnectedComponent,
        ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card =
        ∑ c ∈ (Finset.univ : Finset K.ConnectedComponent),
          ({v ∈ U | f v = c}).card := by
            apply Finset.sum_congr rfl
            intro c _hc
            calc
              ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card =
                  ({v ∈ U | f v = c}.image
                    fun v : {v : V // v ∉ H} => (v : V)).card :=
                (hfiber c).symm
              _ = ({v ∈ U | f v = c}).card :=
                Finset.card_image_of_injective _ Subtype.val_injective
    _ = U.card := hfiberSum.symm
    _ = (T \ H).card := hcardU

private theorem componentUnion_terminal_card
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T H : Finset V)
    (S : Finset (G.induce {v : V | v ∉ H}).ConnectedComponent) :
    ((S.biUnion (TreewidthBrambleDuality.componentVertices G H)) ∩ T).card =
      ∑ c ∈ S,
        ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card := by
  classical
  have hsets :
      (S.biUnion (TreewidthBrambleDuality.componentVertices G H)) ∩ T =
        S.biUnion fun c =>
          (TreewidthBrambleDuality.componentVertices G H c) ∩ T := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [hsets]
  apply Finset.card_biUnion
  intro c hc d hd hcd
  exact (componentVertices_pairwiseDisjoint G H
      (Finset.mem_univ c) (Finset.mem_univ d) hcd).mono
        Finset.inter_subset_left Finset.inter_subset_left

private noncomputable def majorityFamily
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T : Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun A : Finset V =>
    IsConnectedSet G A ∧ T.card < 2 * (A ∩ T).card

private theorem majorityBramble
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T : Finset V) :
    IsBramble G (majorityFamily G T) := by
  classical
  constructor
  · intro A hA
    exact (Finset.mem_filter.mp hA).2.1
  · intro A hA C hC
    apply Or.inl
    by_contra hdisj
    have hAC : Disjoint A C := by
      rw [Finset.disjoint_left]
      intro v hvA hvC
      exact hdisj ⟨v, Finset.mem_inter.mpr ⟨hvA, hvC⟩⟩
    have hACT : Disjoint (A ∩ T) (C ∩ T) := by
      exact hAC.mono Finset.inter_subset_left Finset.inter_subset_left
    have hcard :
        (A ∩ T).card + (C ∩ T).card ≤ T.card := by
      rw [← Finset.card_union_of_disjoint hACT]
      apply Finset.card_le_card
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
    have hAmajor := (Finset.mem_filter.mp hA).2.2
    have hCmajor := (Finset.mem_filter.mp hC).2.2
    omega

/-- Theorem 3.3 in the unit-numerator form used by Theorem 5.1.

The explicit constant is `8`.  The conclusion is valid for disconnected
graphs and all natural-number target values; positivity is needed only for the
degree and denominator, exactly as at the degree-three call site. -/
theorem theorem33_unit_treewidth_of_scaledWellLinked :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) (T : Finset V)
      {Δ alphaDen t : ℕ},
        MaxDegreeAtMost G Δ →
          ScaledWellLinked G T 1 alphaDen →
            0 < Δ →
              0 < alphaDen →
                8 * Δ * alphaDen * t ≤ T.card →
                  t ≤ treewidth G := by
  intro V _ _ G T Δ alphaDen t hdegree hwell hΔ hden hlarge
  classical
  let B : Finset (Finset V) := majorityFamily G T
  have hB : IsBramble G B := by
    simpa [B] using majorityBramble G T
  have horder : HasOrderAtLeast G B (2 * t) := by
    refine ⟨hB, ?_⟩
    intro H hhit
    by_contra hH
    have hHlt : H.card < 2 * t := Nat.lt_of_not_ge hH
    let b := Δ * alphaDen * H.card
    have hb_lt : 4 * b < T.card := by
      have hcoef : 0 < 4 * (Δ * alphaDen) := by positivity
      have hmul := (Nat.mul_lt_mul_left hcoef).2 hHlt
      calc
        4 * b = 4 * (Δ * alphaDen) * H.card := by
          dsimp [b]
          ring
        _ < 4 * (Δ * alphaDen) * (2 * t) := hmul
        _ = 8 * Δ * alphaDen * t := by ring
        _ ≤ T.card := hlarge
    let K := G.induce {v : V | v ∉ H}
    let weight : K.ConnectedComponent → ℕ := fun c =>
      ((TreewidthBrambleDuality.componentVertices G H c) ∩ T).card
    have hweight_half : ∀ c : K.ConnectedComponent,
        2 * weight c ≤ T.card := by
      intro c
      by_contra hc
      have hcmajor : T.card < 2 * weight c := Nat.lt_of_not_ge hc
      let A := TreewidthBrambleDuality.componentVertices G H c
      have hAmem : A ∈ B := by
        change A ∈ majorityFamily G T
        apply Finset.mem_filter.mpr
        exact ⟨by simp,
          ⟨
            ⟨TreewidthBrambleDuality.componentVertices_nonempty c,
              TreewidthBrambleDuality.componentVertices_connected c⟩,
            by simpa [A, weight, K] using hcmajor⟩⟩
      rcases hhit A hAmem with ⟨v, hv⟩
      exact Finset.disjoint_left.mp
        (TreewidthBrambleDuality.componentVertices_disjoint c)
        (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hv).1
    have hsum :
        ∑ c : K.ConnectedComponent, weight c = (T \ H).card := by
      simpa [K, weight] using componentWeight_sum G T H
    have hHleB : H.card ≤ b := by
      dsimp [b]
      have hone : 1 ≤ Δ * alphaDen :=
        Nat.succ_le_iff.mpr (Nat.mul_pos hΔ hden)
      simpa [Nat.mul_assoc, Nat.mul_comm] using
        Nat.mul_le_mul_right H.card hone
    have houtside_gt : 3 * b < ∑ c : K.ConnectedComponent, weight c := by
      rw [hsum]
      have hparts :
          (T \ H).card + (T ∩ H).card = T.card :=
        Finset.card_sdiff_add_card_inter T H
      have hinter : (T ∩ H).card ≤ H.card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    have hselect :
        ∃ S : Finset K.ConnectedComponent,
          b < ∑ c ∈ S, weight c ∧
          b < ∑ c ∈ (Finset.univ \ S), weight c := by
      by_cases hbig : ∃ c : K.ConnectedComponent, b < weight c
      · rcases hbig with ⟨c, hc⟩
        refine ⟨{c}, by simpa, ?_⟩
        have hsplit :=
          Finset.sum_sdiff
            (s₁ := ({c} : Finset K.ConnectedComponent))
            (s₂ := Finset.univ)
            (Finset.singleton_subset_iff.mpr (Finset.mem_univ c))
            (f := weight)
        have hsingle :
            (∑ d ∈ ({c} : Finset K.ConnectedComponent), weight d) =
              weight c := by
          rw [Finset.sum_singleton]
        have hhalf := hweight_half c
        have hparts :
            (T \ H).card + (T ∩ H).card = T.card :=
          Finset.card_sdiff_add_card_inter T H
        have hinterB : (T ∩ H).card ≤ b :=
          (Finset.card_le_card Finset.inter_subset_right).trans hHleB
        omega
      · push Not at hbig
        have hgt : b < ∑ c ∈ (Finset.univ : Finset K.ConnectedComponent),
            weight c := by
          have hb3 : b ≤ 3 * b := by omega
          exact hb3.trans_lt houtside_gt
        rcases exists_subset_sum_gt_le_two_mul
            (Finset.univ : Finset K.ConnectedComponent) weight b hgt
            (fun c _hc => hbig c) with
          ⟨S, hSsub, hSgt, hSle⟩
        refine ⟨S, hSgt, ?_⟩
        have hsplit := Finset.sum_sdiff hSsub (f := weight)
        omega
    rcases hselect with ⟨S, hSleft, hSright⟩
    let X : Finset V :=
      S.biUnion (TreewidthBrambleDuality.componentVertices G H)
    have hXleft : b < (X ∩ T).card := by
      rw [componentUnion_terminal_card]
      simpa [X, K, weight] using hSleft
    let S' : Finset K.ConnectedComponent := Finset.univ \ S
    let Y : Finset V :=
      S'.biUnion (TreewidthBrambleDuality.componentVertices G H)
    have hYcard : b < (Y ∩ T).card := by
      rw [componentUnion_terminal_card]
      simpa [Y, S', K, weight] using hSright
    have hXY : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro v hvX hvY
      rcases Finset.mem_biUnion.mp hvX with ⟨c, hcS, hvc⟩
      rcases Finset.mem_biUnion.mp hvY with ⟨d, hdS, hvd⟩
      have hcd : c = d := by
        rcases TreewidthBrambleDuality.mem_componentVertices.mp hvc with
          ⟨hvo, hvc⟩
        rcases TreewidthBrambleDuality.mem_componentVertices.mp hvd with
          ⟨hvo', hvd⟩
        exact hvc.symm.trans (by simpa using hvd)
      subst d
      exact (Finset.mem_sdiff.mp hdS).2 hcS
    have hXright :
        b < (((Finset.univ : Finset V) \ X) ∩ T).card := by
      apply hYcard.trans_le
      apply Finset.card_le_card
      intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hvY, hvT⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨by simp,
          fun hvX => Finset.disjoint_left.mp hXY hvX hvY⟩, hvT⟩
    letI : DecidableRel G.Adj := Classical.decRel _
    have hsnd :
        ∀ d : G.Dart,
          d ∈ FlowWellLinked.crossingDarts (G := G) X
              ((Finset.univ : Finset V) \ X) →
            d.snd ∈ H := by
      intro d hd
      have hdmem :=
        (FlowWellLinked.mem_crossingDarts (G := G) X
          ((Finset.univ : Finset V) \ X) d).1 hd
      by_contra hnot
      have hfstH : d.fst ∉ H := by
        intro hfst
        rcases Finset.mem_biUnion.mp hdmem.1 with ⟨c, _hc, hdc⟩
        exact Finset.disjoint_left.mp
          (TreewidthBrambleDuality.componentVertices_disjoint c) hdc hfst
      rcases Finset.mem_biUnion.mp hdmem.1 with ⟨c, hcS, hdc⟩
      have hfstComp :
          K.connectedComponentMk ⟨d.fst, hfstH⟩ = c :=
        (TreewidthBrambleDuality.mem_componentVertices.mp hdc).2
      have hsndComp :
          K.connectedComponentMk ⟨d.snd, hnot⟩ = c := by
        exact (TreewidthBrambleDuality.component_eq_of_adj_outside
          hfstH hnot d.2).symm.trans hfstComp
      have hsndX : d.snd ∈ X := by
        apply Finset.mem_biUnion.mpr
        exact ⟨c, hcS,
          TreewidthBrambleDuality.mem_componentVertices.mpr
            ⟨hnot, hsndComp⟩⟩
      exact (Finset.mem_sdiff.mp hdmem.2).2 hsndX
    have hcut :
        (Section44.edgeBoundary G X
            ((Finset.univ : Finset V) \ X)).card ≤ Δ * H.card := by
      exact
        (FlowWellLinked.edgeBoundary_card_le_crossingDarts_card
          (G := G) X ((Finset.univ : Finset V) \ X)).trans
          (FlowWellLinked.crossingDarts_card_le_maxDegree_mul_of_snd_subset
            (G := G) hdegree hsnd)
    have hwl := hwell.2.2 X ((Finset.univ : Finset V) \ X)
      (by simp) Finset.disjoint_sdiff
    have hmin :
        b < min (X ∩ T).card
          (((Finset.univ : Finset V) \ X) ∩ T).card := by
      simp only [lt_min_iff]
      exact ⟨hXleft, hXright⟩
    have hupper :
        min (X ∩ T).card
            (((Finset.univ : Finset V) \ X) ∩ T).card ≤ b := by
      have := hwl
      simp only [one_mul] at this
      exact this.trans <| by
        simpa [b, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          Nat.mul_le_mul_left alphaDen hcut
    omega
  have htwplus :
      2 * t ≤ treewidth G + 1 :=
    bramble_order_le_treewidth_add_one_of_finiteSubtreeHelly horder
      (finiteSubtreeHelly _)
  omega

/-- Existential constant package matching the Theorem 3.3 input shape at the
unit-numerator call site. -/
theorem exists_theorem33_unit_treewidth_of_scaledWellLinked :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (T : Finset V)
        {Δ alphaDen t : ℕ},
          MaxDegreeAtMost G Δ →
            ScaledWellLinked G T 1 alphaDen →
              0 < Δ →
                0 < alphaDen →
                  c * Δ * alphaDen * t ≤ T.card →
                    t ≤ treewidth G :=
  ⟨8, by decide, theorem33_unit_treewidth_of_scaledWellLinked⟩

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
