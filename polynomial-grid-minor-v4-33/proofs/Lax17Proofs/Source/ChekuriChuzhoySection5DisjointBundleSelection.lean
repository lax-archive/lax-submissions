import Lax17Proofs.Source.ChekuriChuzhoyCorollary28
import Lax17Proofs.Source.ChekuriChuzhoySection5Selection

namespace Lax17Proofs

universe u v w

/-!
# Simultaneous selection from disjoint bundles

This file isolates the sharp finite counting argument used for simultaneous
group selection in Chekuri--Chuzhoy Section 5.  Pairwise-disjoint bundles do
not incur the extra factor equal to the number of bundles: the union of every
active subfamily has additive cardinality, while each group fiber accounts for
at most `maxGroupSize` items.

The proof verifies Hall's inequalities for one demand per retained item, uses
the proved colored-representatives theorem from
`ChekuriChuzhoyCorollary28.lean`, and then completes the partial selection to
an exact group transversal.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5DisjointBundleSelection


open Finset
open ChekuriChuzhoySection5Selection

variable {Item : Type u} {Group : Type v}

/-- A pairwise-disjoint family of bundles, each of size at least
`maxGroupSize * q`, admits one simultaneous exact group transversal retaining
at least `q` items from every bundle.

The positivity assumption is necessary: when `maxGroupSize = 0`, a family
containing the empty bundle satisfies the cardinality hypotheses for every
`q`, but cannot retain a positive number of items. -/
theorem exists_exactGroupTransversal_retaining_pairwiseDisjoint_bundles
    [Fintype Item] [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group)
    (bundles : Finset (Finset Item)) (maxGroupSize q : ℕ)
    (hmax : 0 < maxGroupSize)
    (hbundles : ∀ B ∈ bundles, B ⊆ items)
    (hdisjoint :
      (↑bundles : Set (Finset Item)).PairwiseDisjoint id)
    (hgroupSize : ∀ g ∈ items.image group,
      (items.filter fun x => group x = g).card ≤ maxGroupSize)
    (hbundleSize : ∀ B ∈ bundles,
      maxGroupSize * q ≤ B.card) :
    ∃ selected : Finset Item,
      IsExactGroupTransversal items group selected ∧
        ∀ B ∈ bundles, q ≤ (selected ∩ B).card := by
  classical
  let K := ULift.{u} {g : Group // g ∈ items.image group}
  let J := ULift.{v} {B : Finset Item // B ∈ bundles}
  let groupFiber : K → Finset Item := fun k =>
    items.filter fun x => group x = k.down.1
  let block : J → Finset Item := fun j => j.down.1

  have hgroupFiberDisjoint :
      Set.PairwiseDisjoint Set.univ groupFiber := by
    intro a _ha b _hb hab
    change Disjoint (groupFiber a) (groupFiber b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxaLabel : group x = a.down.1 :=
      (Finset.mem_filter.mp hxa).2
    have hxbLabel : group x = b.down.1 :=
      (Finset.mem_filter.mp hxb).2
    apply hab
    apply ULift.ext
    apply Subtype.ext
    exact hxaLabel.symm.trans hxbLabel

  have hblockDisjoint :
      Set.PairwiseDisjoint Set.univ block := by
    intro a _ha b _hb hab
    change Disjoint (block a) (block b)
    have habDown : a.down.1 ≠ b.down.1 := by
      intro h
      apply hab
      apply ULift.ext
      exact Subtype.ext h
    simpa [block] using
      hdisjoint a.down.2 b.down.2 habDown

  have hblockSubset : ∀ j, block j ⊆ items := by
    intro j
    exact hbundles j.down.1 j.down.2

  have hhall :
      ∀ s : Finset
          (ChekuriChuzhoyCorollary28.BlockDemand block maxGroupSize),
        s.card ≤
          (s.biUnion
            (ChekuriChuzhoyCorollary28.eligibleGroups
              groupFiber block maxGroupSize)).card := by
    intro s
    let A := s.image Sigma.fst
    let N := s.biUnion
      (ChekuriChuzhoyCorollary28.eligibleGroups
        groupFiber block maxGroupSize)
    have hsFiber :
        s.card = ∑ j ∈ A, (s.filter fun d => d.1 = j).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro d hd
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hdemandFiber : ∀ j,
        (s.filter fun d => d.1 = j).card ≤
          (block j).card / maxGroupSize := by
      intro j
      let f :
          {d // d ∈ s.filter fun d => d.1 = j} →
            Fin ((block j).card / maxGroupSize) := fun d => by
        have hdj : d.1.1 = j := (Finset.mem_filter.mp d.2).2
        exact ⟨d.1.2.val, by simpa [hdj] using d.1.2.isLt⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        have hfirst : a.1.1 = b.1.1 :=
          (Finset.mem_filter.mp a.2).2.trans
            (Finset.mem_filter.mp b.2).2.symm
        have hval :=
          congrArg
            (fun z : Fin ((block j).card / maxGroupSize) => z.val) hab
        simp only [f] at hval
        have hbound :
            (block a.1.1).card / maxGroupSize =
              (block b.1.1).card / maxGroupSize := by
          rw [hfirst]
        exact Sigma.ext hfirst <| (Fin.heq_ext_iff hbound).mpr hval
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        Fintype.card_le_of_injective f hf
    have hdemands :
        maxGroupSize * s.card ≤ (A.biUnion block).card := by
      rw [hsFiber, Finset.mul_sum]
      calc
        ∑ j ∈ A,
              maxGroupSize * (s.filter fun d => d.1 = j).card ≤
            ∑ j ∈ A, (block j).card := by
          apply Finset.sum_le_sum
          intro j _hj
          calc
            maxGroupSize * (s.filter fun d => d.1 = j).card ≤
                maxGroupSize * ((block j).card / maxGroupSize) :=
              Nat.mul_le_mul_left _ (hdemandFiber j)
            _ ≤ (block j).card := Nat.mul_div_le _ _
        _ = (A.biUnion block).card := by
          symm
          apply Finset.card_biUnion
          intro i _hi j _hj hij
          exact hblockDisjoint (by simp) (by simp) hij
    have hblocksToGroups :
        A.biUnion block ⊆ N.biUnion groupFiber := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hjA, hxj⟩
      rcases Finset.mem_image.mp hjA with ⟨d, hd, rfl⟩
      have hxItems : x ∈ items := hblockSubset d.1 hxj
      let k : K :=
        ULift.up ⟨group x, Finset.mem_image_of_mem group hxItems⟩
      refine Finset.mem_biUnion.mpr ⟨k, ?_, ?_⟩
      · refine Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩
        apply
          (ChekuriChuzhoyCorollary28.mem_eligibleGroups
            groupFiber block maxGroupSize d k).mpr
        exact ⟨x, Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨hxItems, rfl⟩, hxj⟩⟩
      · exact Finset.mem_filter.mpr ⟨hxItems, rfl⟩
    have hgroupFiberCard :
        ∀ k ∈ N, (groupFiber k).card ≤ maxGroupSize := by
      intro k _hk
      exact hgroupSize k.down.1 k.down.2
    have hmul :
        maxGroupSize * s.card ≤ maxGroupSize * N.card := by
      calc
        maxGroupSize * s.card ≤ (A.biUnion block).card := hdemands
        _ ≤ (N.biUnion groupFiber).card :=
          Finset.card_le_card hblocksToGroups
        _ ≤ N.card * maxGroupSize :=
          Finset.card_biUnion_le_card_mul
            N groupFiber maxGroupSize hgroupFiberCard
        _ = maxGroupSize * N.card := Nat.mul_comm _ _
    have hsN : s.card ≤ N.card :=
      Nat.le_of_mul_le_mul_left hmul hmax
    simpa [N] using hsN

  rcases
      ChekuriChuzhoyCorollary28.exists_injective_colored_representatives_of_hall
        groupFiber block maxGroupSize hgroupFiberDisjoint hhall with
    ⟨assign, representative, hassignInjective, _hrepresentativeInjective,
      hrepresentativeMem, hquota⟩

  let initial : Finset Item := Finset.univ.image representative
  have hinitial :
      IsPartialGroupTransversal items group initial := by
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨d, _hd, rfl⟩
      exact
        (Finset.mem_filter.mp
          (Finset.mem_inter.mp (hrepresentativeMem d)).1).1
    · intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, _hb, rfl⟩
      have haLabel :
          group (representative a) = (assign a).down.1 :=
        (Finset.mem_filter.mp
          (Finset.mem_inter.mp (hrepresentativeMem a)).1).2
      have hbLabel :
          group (representative b) = (assign b).down.1 :=
        (Finset.mem_filter.mp
          (Finset.mem_inter.mp (hrepresentativeMem b)).1).2
      have habAssign : assign a = assign b := by
        apply ULift.ext
        apply Subtype.ext
        exact haLabel.symm.trans (hxy.trans hbLabel)
      exact congrArg representative (hassignInjective habAssign)

  have hinitialQuota :
      ∀ B ∈ bundles, q ≤ (initial ∩ B).card := by
    intro B hB
    let j : J := ULift.up ⟨B, hB⟩
    have hqDiv : q ≤ (block j).card / maxGroupSize := by
      apply (Nat.le_div_iff_mul_le hmax).2
      simpa [block, j, Nat.mul_comm] using hbundleSize B hB
    have := hqDiv.trans (hquota j)
    simpa [initial, block, j, Finset.inter_comm] using this

  rcases hinitial.exists_exact_superset with
    ⟨selected, hselected, hinitialSubset⟩
  refine ⟨selected, hselected, ?_⟩
  intro B hB
  exact (hinitialQuota B hB).trans (Finset.card_le_card (by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxInitial, hxB⟩
    exact Finset.mem_inter.mpr ⟨hinitialSubset hxInitial, hxB⟩))

end ChekuriChuzhoySection5DisjointBundleSelection
end SimpleGraph

end Lax17Proofs
