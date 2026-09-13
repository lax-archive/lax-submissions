import Lax17Proofs.Source.ChekuriChuzhoyTheorem46Merge
import Lax17Proofs.Source.ChekuriChuzhoyTheorem35

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 4.6

This file completes the bottom-up DFS construction in journal Theorem 4.6.
The local two-child operation applies Lemma 2.19 only to the portions of the
Step 1 paths inside the branching cluster.  The leaf-to-first-entry prefixes
are left unchanged and are reattached after the two reroutings, exactly as in
the source proof.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical
open ChekuriChuzhoyRootedTreePruning
open ChekuriChuzhoyRootedTreeComponents

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

section InsideRerouting

/-- The branching output together with the mutual-disjointness facts needed
when its bridge is installed beside the two recursively built systems. -/
structure DisjointTwoChildReroutingData
    {X₁ A₁ X₂ A₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ)
    extends TwoChildReroutingData (K := K) P₁ P₂ w where
  retainedFirst_mutuallyNodeDisjoint_retainedSecond :
    retainedFirstInside.toPathPacking.MutuallyNodeDisjoint
      retainedSecondInside.toPathPacking
  retainedFirst_mutuallyNodeDisjoint_bridge :
    retainedFirstInside.toPathPacking.MutuallyNodeDisjoint
      bridge.toPathPacking
  retainedSecond_mutuallyNodeDisjoint_bridge :
    retainedSecondInside.toPathPacking.MutuallyNodeDisjoint
      bridge.toPathPacking

set_option maxHeartbeats 2000000 in
/-- The two Lemma 2.19 applications at a branching cluster, in the
source-faithful form needed by Theorem 4.6.  Here the source endpoints of the
two Step 1 portions lie in the current cluster; only their target interfaces
must be disjoint from the corresponding sources. -/
theorem exists_twoChildReroutingData_insideCluster
    {X₁ A₁ X₂ A₂ K : Finset V}
    (P₁ : PerfectPathPacking G X₁ A₁)
    (P₂ : PerfectPathPacking G X₂ A₂)
    (w : ℕ)
    (hPdisj :
      P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    (hlink : NodeLinkedIn G K A₁ A₂)
    (hP₁stay : P₁.toPathPacking.StaysIn K)
    (hP₂stay : P₂.toPathPacking.StaysIn K)
    (hP₁internal :
      P₁.toPathPacking.InternallyDisjointFromSet A₁)
    (hP₂internal :
      P₂.toPathPacking.InternallyDisjointFromSet A₂)
    (hX₁A₁ : Disjoint X₁ A₁)
    (hX₂A₂ : Disjoint X₂ A₂)
    (hfour₁ : 4 * w ≤ P₁.card)
    (hfour₂ : 4 * w ≤ P₂.card) :
    Nonempty (DisjointTwoChildReroutingData (K := K) P₁ P₂ w) := by
  classical
  have hX₁X₂ :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      P₁ P₂ hPdisj
  have hA₁A₂ :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      P₁ P₂ hPdisj
  have hX₁A₂ :
      Disjoint X₁ A₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases P₁.source_bijective.2 ⟨x, hx₁⟩ with ⟨i, hi⟩
    rcases P₂.target_bijective.2 ⟨x, hx₂⟩ with ⟨j, hj⟩
    have hxi : x ∈ (P₁.path i).vertexSet := by
      have hs : (P₁.path i).source = x := congrArg Subtype.val hi
      simpa [hs] using GraphPath.source_mem_vertexSet (P₁.path i)
    have hxj : x ∈ (P₂.path j).vertexSet := by
      have ht : (P₂.path j).target = x := congrArg Subtype.val hj
      simpa [ht] using GraphPath.target_mem_vertexSet (P₂.path j)
    exact Finset.disjoint_left.mp (hPdisj i j) hxi hxj
  have hX₂A₁ :
      Disjoint X₂ A₁ := by
    rw [Finset.disjoint_left]
    intro x hx₂ hx₁
    rcases P₂.source_bijective.2 ⟨x, hx₂⟩ with ⟨j, hj⟩
    rcases P₁.target_bijective.2 ⟨x, hx₁⟩ with ⟨i, hi⟩
    have hxj : x ∈ (P₂.path j).vertexSet := by
      have hs : (P₂.path j).source = x := congrArg Subtype.val hj
      simpa [hs] using GraphPath.source_mem_vertexSet (P₂.path j)
    have hxi : x ∈ (P₁.path i).vertexSet := by
      have ht : (P₁.path i).target = x := congrArg Subtype.val hi
      simpa [ht] using GraphPath.target_mem_vertexSet (P₁.path i)
    exact Finset.disjoint_left.mp (hPdisj i j) hxi hxj
  have hA₁card : A₁.card = P₁.card := P₁.card_eq_right_card.symm
  have hA₂card : A₂.card = P₂.card := P₂.card_eq_right_card.symm
  obtain ⟨A₄, hA₄, hA₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₁)
      (by simpa [hA₁card] using hfour₁)
  obtain ⟨B₄, hB₄, hB₄card⟩ :=
    Finset.exists_subset_card_eq (s := A₂)
      (by simpa [hA₂card] using hfour₂)
  obtain ⟨Q, hQcard, hQstay⟩ :=
    NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (hlink.mono_terminals hA₄ hB₄)
      (hA₄card.trans hB₄card.symm)
  let H₁ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₁) Q.reverse hA₄)
  have hH₁card : H₁.packing.card = 4 * w := by
    calc
      H₁.packing.card = Q.reverse.card := H₁.packing_card
      _ = Q.card := rfl
      _ = A₄.card := hQcard
      _ = 4 * w := hA₄card
  have hH₁stay :
      H₁.packing.toPathPacking.StaysIn K := by
    intro i x hx
    rcases H₁.path_vertexSet_subset i with ⟨j, hj⟩
    exact hQstay j (by simpa using hj hx)
  have hX₁B₄ : Disjoint X₁ B₄ :=
    hX₁A₂.mono_right hB₄
  have hB₄A₁ : Disjoint B₄ A₁ :=
    (hA₁A₂.mono_right hB₄).symm
  let D₁ := Classical.choice
    (exists_generalLemma219SplitData
      P₁ H₁.packing hX₁B₄
      Finset.Subset.rfl H₁.hit_subset
      hX₁A₁ hB₄A₁
      hP₁internal H₁.packing_internallyDisjoint
      hP₁stay hH₁stay
      (hH₁card.trans_le hfour₁))
  let R₁ := D₁.reroutedSmall.reverse
  let H₂ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₂) R₁ hB₄)
  have hH₂card : H₂.packing.card = 4 * w := by
    calc
      H₂.packing.card = R₁.card := H₂.packing_card
      _ = D₁.reroutedSmall.card := rfl
      _ = H₁.packing.card := D₁.reroutedSmall_card
      _ = 4 * w := hH₁card
  have hH₂stay :
      H₂.packing.toPathPacking.StaysIn K := by
    intro i x hx
    rcases H₂.path_vertexSet_subset i with ⟨j, hj⟩
    exact D₁.reroutedSmall_staysIn j (by simpa [R₁] using hj hx)
  have hX₂D₁ :
      Disjoint X₂ D₁.reroutedTargets :=
    hX₂A₁.mono_right D₁.reroutedTargets_subset
  have hD₁A₂ :
      Disjoint D₁.reroutedTargets A₂ :=
    hA₁A₂.mono_left D₁.reroutedTargets_subset
  let D₂ := Classical.choice
    (exists_generalLemma219SplitData
      P₂ H₂.packing hX₂D₁
      Finset.Subset.rfl H₂.hit_subset
      hX₂A₂ hD₁A₂
      hP₂internal H₂.packing_internallyDisjoint
      hP₂stay hH₂stay
      (hH₂card.trans_le hfour₂))
  refine ⟨{
    toTwoChildReroutingData := {
      retainedFirst := D₁.retainedSources
      retainedSecond := D₂.retainedSources
      retainedFirst_subset := D₁.retainedSources_subset
      retainedSecond_subset := D₂.retainedSources_subset
      retainedFirst_count := ?_
      retainedSecond_count := ?_
      retainedFirstTarget := D₁.retainedTargets
      retainedSecondTarget := D₂.retainedTargets
      retainedFirstTarget_subset := D₁.retainedTargets_subset
      retainedSecondTarget_subset := D₂.retainedTargets_subset
      retainedFirstInside := D₁.retainedInside
      retainedSecondInside := D₂.retainedInside
      retainedFirstInside_path_subset := D₁.retainedInside_path_subset
      retainedSecondInside_path_subset := D₂.retainedInside_path_subset
      bridgeSource := D₁.reroutedTargets
      bridgeTarget := D₂.reroutedTargets
      bridgeSource_subset := D₁.reroutedTargets_subset
      bridgeTarget_subset := D₂.reroutedTargets_subset
      bridge := D₂.reroutedSmall
      bridge_card := ?_
      bridgeSource_disjoint_retainedFirstTarget := D₁.target_disjoint
      bridgeTarget_disjoint_retainedSecondTarget := D₂.target_disjoint
      bridge_internallyDisjoint_firstTarget := ?_
      bridge_internallyDisjoint_secondTarget :=
        D₂.reroutedSmall_internallyDisjoint_targetRegion
      bridge_path_subset := ?_ }
    retainedFirst_mutuallyNodeDisjoint_retainedSecond := ?_
    retainedFirst_mutuallyNodeDisjoint_bridge := ?_
    retainedSecond_mutuallyNodeDisjoint_bridge :=
      D₂.retainedInside_mutuallyNodeDisjoint_reroutedSmall }⟩
  · rw [← hH₁card]
    exact D₁.retained_count
  · rw [← hH₂card]
    exact D₂.retained_count
  · calc
      D₂.reroutedSmall.card = H₂.packing.card :=
        D₂.reroutedSmall_card
      _ = R₁.card := H₂.packing_card
      _ = D₁.reroutedSmall.card := rfl
      _ = H₁.packing.card := D₁.reroutedSmall_card
      _ = Q.reverse.card := H₁.packing_card
      _ = Q.card := rfl
      _ = A₄.card := hQcard
      _ = 4 * w := hA₄card
  · intro i x hx hxA₁
    rcases Finset.mem_union.mp (D₂.reroutedSmall_path_subset i hx) with
      hxP₂ | hxH₂
    · rcases P₂.toPathPacking.mem_vertexSet.mp hxP₂ with ⟨j, hj⟩
      rcases P₁.target_bijective.2 ⟨x, hxA₁⟩ with ⟨k, hk⟩
      have hxP₁ : x ∈ (P₁.path k).vertexSet := by
        have ht : (P₁.path k).target = x := congrArg Subtype.val hk
        simpa [ht] using GraphPath.target_mem_vertexSet (P₁.path k)
      exact False.elim
        (Finset.disjoint_left.mp (hPdisj k j) hxP₁ hj)
    · rcases H₂.packing.toPathPacking.mem_vertexSet.mp hxH₂ with ⟨j, hj⟩
      have hH₂internalA₁ :
          H₂.packing.toPathPacking.InternallyDisjointFromSet A₁ := by
        intro k y hy hyA₁
        rcases H₂.path_vertexSet_subset k with ⟨a, ha⟩
        rcases D₁.reroutedSmall_internallyDisjoint_targetRegion
            a (by simpa [R₁] using ha hy) hyA₁ with hs | ht
        · have hyB₄ : y ∈ B₄ := by
            have hmem :
                (D₁.reroutedSmall.path a).source ∈ B₄ :=
              D₁.reroutedSmall.source_mem a
            simpa [hs] using hmem
          exact False.elim
            (Finset.disjoint_left.mp hB₄A₁ hyB₄ hyA₁)
        · have hySourceSet : y ∈ D₁.reroutedTargets := by
            have hmem :
                (D₁.reroutedSmall.path a).target ∈
                  D₁.reroutedTargets :=
              D₁.reroutedSmall.target_mem a
            simpa [ht] using hmem
          rcases H₂.packing.source_bijective.2
              ⟨y, hySourceSet⟩ with ⟨b, hb⟩
          have hyb : y ∈ (H₂.packing.path b).vertexSet := by
            have hs' : (H₂.packing.path b).source = y :=
              congrArg Subtype.val hb
            simpa [hs'] using
              GraphPath.source_mem_vertexSet (H₂.packing.path b)
          have hkb : k = b := by
            by_contra hne
            exact Finset.disjoint_left.mp
              (H₂.packing.node_disjoint hne) hy hyb
          exact Or.inl (by
            subst b
            exact (congrArg Subtype.val hb).symm)
      rcases hH₂internalA₁ j hj hxA₁ with hxSource | hxTarget
      · have hxSourceSet : x ∈ D₁.reroutedTargets := by
          have : (H₂.packing.path j).source ∈ D₁.reroutedTargets :=
            H₂.packing.source_mem j
          simpa [hxSource] using this
        rcases D₂.reroutedSmall.source_bijective.2
            ⟨x, hxSourceSet⟩ with ⟨k, hk⟩
        have hxk : x ∈ (D₂.reroutedSmall.path k).vertexSet := by
          have hs : (D₂.reroutedSmall.path k).source = x :=
            congrArg Subtype.val hk
          simpa [hs] using
            GraphPath.source_mem_vertexSet (D₂.reroutedSmall.path k)
        have hik : i = k := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (D₂.reroutedSmall.node_disjoint hne) hx hxk
        exact Or.inl (by
          subst k
          exact (congrArg Subtype.val hk).symm)
      · have hxA₂ : x ∈ A₂ := by
          have : (H₂.packing.path j).target ∈ H₂.hit :=
            H₂.packing.target_mem j
          exact H₂.hit_subset (by simpa [hxTarget] using this)
        exact False.elim
          (Finset.disjoint_left.mp hA₁A₂ hxA₁ hxA₂)
  · intro i x hx
    rcases Finset.mem_union.mp (D₂.reroutedSmall_path_subset i hx) with
      hxP₂ | hxH₂
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxP₂)
    · rcases H₂.packing.toPathPacking.mem_vertexSet.mp hxH₂ with ⟨j, hj⟩
      rcases H₂.path_vertexSet_subset j with ⟨a, ha⟩
      have hxD₁ :
          x ∈ (D₁.reroutedSmall.path a).vertexSet := by
        simpa [R₁] using ha hj
      rcases Finset.mem_union.mp
          (D₁.reroutedSmall_path_subset a hxD₁) with hxP₁ | hxH₁
      · exact Finset.mem_union_left _ hxP₁
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        rcases H₁.packing.toPathPacking.mem_vertexSet.mp hxH₁ with ⟨k, hk⟩
        rcases H₁.path_vertexSet_subset k with ⟨b, hb⟩
        exact hQstay b (by simpa using hb hk)
  · intro i j
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hx₁ hx₂
    have hxP₁ := D₁.retainedInside_path_subset i hx₁
    have hxP₂ := D₂.retainedInside_path_subset j hx₂
    rcases P₁.toPathPacking.mem_vertexSet.mp hxP₁ with ⟨a, ha⟩
    rcases P₂.toPathPacking.mem_vertexSet.mp hxP₂ with ⟨b, hb⟩
    exact Finset.disjoint_left.mp (hPdisj a b) ha hb
  · intro i j
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxR hxB
    rcases Finset.mem_union.mp
        (D₂.reroutedSmall_path_subset j hxB) with hxP₂ | hxH₂
    · have hxP₁ := D₁.retainedInside_path_subset i hxR
      rcases P₁.toPathPacking.mem_vertexSet.mp hxP₁ with ⟨a, ha⟩
      rcases P₂.toPathPacking.mem_vertexSet.mp hxP₂ with ⟨b, hb⟩
      exact Finset.disjoint_left.mp (hPdisj a b) ha hb
    · rcases H₂.packing.toPathPacking.mem_vertexSet.mp hxH₂ with ⟨a, ha⟩
      rcases H₂.path_vertexSet_subset a with ⟨b, hb⟩
      have hxD₁ :
          x ∈ (D₁.reroutedSmall.path b).vertexSet := by
        simpa [R₁] using hb ha
      exact Finset.disjoint_left.mp
        (D₁.retainedInside_mutuallyNodeDisjoint_reroutedSmall i b)
        hxR hxD₁

end InsideRerouting

section AttachedRerouting

/-- Disjoint target restrictions of one perfect packing remain mutually
node-disjoint. -/
theorem PerfectPathPacking.restrictTargetSet_mutuallyNodeDisjoint
    {S T T₁ T₂ : Finset V}
    (P : PerfectPathPacking G S T)
    (hT₁ : T₁ ⊆ T) (hT₂ : T₂ ⊆ T)
    (hdisj : Disjoint T₁ T₂) :
    (P.restrictTargetSet T₁ hT₁).toPathPacking.MutuallyNodeDisjoint
      (P.restrictTargetSet T₂ hT₂).toPathPacking := by
  intro i j
  apply P.node_disjoint
  intro hij
  have hi : (P.path i.1).target ∈ T₁ :=
    (P.mem_targetIndexSetOfSubset T₁ i.1).mp i.2
  have hj : (P.path j.1).target ∈ T₂ :=
    (P.mem_targetIndexSetOfSubset T₂ j.1).mp j.2
  exact Finset.disjoint_left.mp hdisj hi (by simpa [hij] using hj)

/-- A prefix internally avoiding a region is disjoint from a packing inside
that region when every possible prefix target is traced by a reference family
already disjoint from the inside packing. -/
theorem PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
    {S T X Y R₁ R₂ K : Finset V}
    (P : PerfectPathPacking G S T)
    (Q : PerfectPathPacking G X Y)
    (reference : PerfectPathPacking G R₁ R₂)
    (hPinternal : P.toPathPacking.InternallyDisjointFromSet K)
    (hSdisj : Disjoint S K)
    (hQstay : Q.toPathPacking.StaysIn K)
    (htrace :
      ∀ x ∈ T, ∃ i : reference.Index,
        x ∈ (reference.path i).vertexSet)
    (href :
      reference.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking := by
  intro i j
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hxP hxQ
  have hxK := hQstay j hxQ
  rcases hPinternal i hxP hxK with hs | ht
  · have hxS : x ∈ S := by
      have := P.source_mem i
      simpa [hs] using this
    exact Finset.disjoint_left.mp hSdisj hxS hxK
  · have hxT : x ∈ T := by
      have := P.target_mem i
      simpa [ht] using this
    rcases htrace x hxT with ⟨r, hxr⟩
    exact Finset.disjoint_left.mp (href r j) hxr hxQ

/-- A perfect packing has no internal occurrence of one of its source
terminals. -/
theorem PerfectPathPacking.internallyDisjointFromSet_left
    {S T : Finset V} (P : PerfectPathPacking G S T) :
    P.toPathPacking.InternallyDisjointFromSet S := by
  intro i x hx hxS
  rcases P.source_bijective.2 ⟨x, hxS⟩ with ⟨j, hj⟩
  have hs : (P.path j).source = x := congrArg Subtype.val hj
  by_cases hij : i = j
  · subst j
    exact Or.inl hs.symm
  · exact False.elim
      (Finset.disjoint_left.mp (P.node_disjoint hij) hx
        (by simpa [hs] using GraphPath.source_mem_vertexSet (P.path j)))

theorem PerfectPathPacking.left_subset_vertexSet
    {S T : Finset V} (P : PerfectPathPacking G S T) :
    S ⊆ P.toPathPacking.vertexSet := by
  intro x hx
  rcases P.source_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
  apply P.toPathPacking.mem_vertexSet.2
  refine ⟨i, ?_⟩
  have hs : (P.path i).source = x := congrArg Subtype.val hi
  simpa [hs] using GraphPath.source_mem_vertexSet (P.path i)

theorem PerfectPathPacking.right_subset_vertexSet
    {S T : Finset V} (P : PerfectPathPacking G S T) :
    T ⊆ P.toPathPacking.vertexSet := by
  intro x hx
  rcases P.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
  apply P.toPathPacking.mem_vertexSet.2
  refine ⟨i, ?_⟩
  have ht : (P.path i).target = x := congrArg Subtype.val hi
  simpa [ht] using GraphPath.target_mem_vertexSet (P.path i)

/-- The result of reattaching the untouched child-subtree prefixes to the
inside-cluster output of the two Lemma 2.19 applications. -/
structure AttachedTwoChildReroutingData
    {X₁ A₁ X₂ A₂ Y₁ Y₂ C₁ C₂ K : Finset V}
    (outside₁ : PerfectPathPacking G X₁ A₁)
    (outside₂ : PerfectPathPacking G X₂ A₂)
    (inside₁ : PerfectPathPacking G Y₁ A₁)
    (inside₂ : PerfectPathPacking G Y₂ A₂)
    (w : ℕ) where
  retainedFirstSources : Finset V
  retainedSecondSources : Finset V
  retainedFirstParents : Finset V
  retainedSecondParents : Finset V
  retainedFirstSources_subset : retainedFirstSources ⊆ X₁
  retainedSecondSources_subset : retainedSecondSources ⊆ X₂
  retainedFirstRoute :
    PerfectPathPacking G retainedFirstSources retainedFirstParents
  retainedSecondRoute :
    PerfectPathPacking G retainedSecondSources retainedSecondParents
  retainedFirstParents_subset : retainedFirstParents ⊆ Y₁
  retainedSecondParents_subset : retainedSecondParents ⊆ Y₂
  retainedFirst_count :
    retainedFirstSources.card + 4 * w = outside₁.card
  retainedSecond_count :
    retainedSecondSources.card + 4 * w = outside₂.card
  usedFirst : Finset V
  usedSecond : Finset V
  usedFirst_subset : usedFirst ⊆ X₁
  usedSecond_subset : usedSecond ⊆ X₂
  bridge : PerfectPathPacking G usedFirst usedSecond
  bridge_card : bridge.card = 4 * w
  retainedFirstRoute_staysIn :
    retainedFirstRoute.toPathPacking.StaysIn (C₁ ∪ K)
  retainedSecondRoute_staysIn :
    retainedSecondRoute.toPathPacking.StaysIn (C₂ ∪ K)
  retainedFirstRoute_internallyDisjointFromSet_of :
    ∀ (L : Finset V), Disjoint K L →
      outside₁.toPathPacking.InternallyDisjointFromSet L →
        retainedFirstRoute.toPathPacking.InternallyDisjointFromSet L
  retainedSecondRoute_internallyDisjointFromSet_of :
    ∀ (L : Finset V), Disjoint K L →
      outside₂.toPathPacking.InternallyDisjointFromSet L →
        retainedSecondRoute.toPathPacking.InternallyDisjointFromSet L
  retainedFirstRoute_path_subset :
    ∀ i : retainedFirstRoute.Index,
      (retainedFirstRoute.path i).vertexSet ⊆
        outside₁.toPathPacking.vertexSet ∪
          inside₁.toPathPacking.vertexSet
  retainedSecondRoute_path_subset :
    ∀ i : retainedSecondRoute.Index,
      (retainedSecondRoute.path i).vertexSet ⊆
        outside₂.toPathPacking.vertexSet ∪
          inside₂.toPathPacking.vertexSet
  bridge_staysIn :
    bridge.toPathPacking.StaysIn (C₁ ∪ (K ∪ C₂))
  bridge_internallyDisjointFromSet_of :
    ∀ (L : Finset V), Disjoint K L →
      outside₁.toPathPacking.InternallyDisjointFromSet L →
      outside₂.toPathPacking.InternallyDisjointFromSet L →
        bridge.toPathPacking.InternallyDisjointFromSet L
  bridge_path_subset :
    ∀ i : bridge.Index,
      (bridge.path i).vertexSet ⊆
        outside₁.toPathPacking.vertexSet ∪
          (inside₁.toPathPacking.vertexSet ∪
            (inside₂.toPathPacking.vertexSet ∪
              (outside₂.toPathPacking.vertexSet ∪ K)))
  retainedFirstRoute_mutuallyNodeDisjoint_retainedSecondRoute :
    retainedFirstRoute.toPathPacking.MutuallyNodeDisjoint
      retainedSecondRoute.toPathPacking
  retainedFirstRoute_mutuallyNodeDisjoint_bridge :
    retainedFirstRoute.toPathPacking.MutuallyNodeDisjoint
      bridge.toPathPacking
  retainedSecondRoute_mutuallyNodeDisjoint_bridge :
    retainedSecondRoute.toPathPacking.MutuallyNodeDisjoint
      bridge.toPathPacking

set_option maxHeartbeats 2000000 in
/-- Attach the two child prefixes to the source-faithful inside-cluster
rerouting. -/
theorem exists_attachedTwoChildReroutingData
    {X₁ A₁ X₂ A₂ Y₁ Y₂ C₁ C₂ K : Finset V}
    (outside₁ : PerfectPathPacking G X₁ A₁)
    (outside₂ : PerfectPathPacking G X₂ A₂)
    (inside₁ : PerfectPathPacking G Y₁ A₁)
    (inside₂ : PerfectPathPacking G Y₂ A₂)
    (w : ℕ)
    (hOutside₁ : outside₁.toPathPacking.StaysIn C₁)
    (hOutside₂ : outside₂.toPathPacking.StaysIn C₂)
    (hInside₁ : inside₁.toPathPacking.StaysIn K)
    (hInside₂ : inside₂.toPathPacking.StaysIn K)
    (hOutside₁InternalK :
      outside₁.toPathPacking.InternallyDisjointFromSet K)
    (hOutside₂InternalK :
      outside₂.toPathPacking.InternallyDisjointFromSet K)
    (hX₁K : Disjoint X₁ K) (hX₂K : Disjoint X₂ K)
    (hOutsideDisj :
      outside₁.toPathPacking.MutuallyNodeDisjoint
        outside₂.toPathPacking)
    (R : DisjointTwoChildReroutingData (K := K) inside₁ inside₂ w) :
    Nonempty
      (AttachedTwoChildReroutingData
        (C₁ := C₁) (C₂ := C₂) (K := K)
        outside₁ outside₂ inside₁ inside₂ w) := by
  classical
  let F₁ := outside₁.restrictTargetSet
    R.retainedFirstTarget R.retainedFirstTarget_subset
  let F₂ := outside₂.restrictTargetSet
    R.retainedSecondTarget R.retainedSecondTarget_subset
  have hF₁stay : F₁.toPathPacking.StaysIn C₁ :=
    outside₁.restrictTargetSet_staysIn
      R.retainedFirstTarget R.retainedFirstTarget_subset hOutside₁
  have hF₂stay : F₂.toPathPacking.StaysIn C₂ :=
    outside₂.restrictTargetSet_staysIn
      R.retainedSecondTarget R.retainedSecondTarget_subset hOutside₂
  have hInside₁Vertex :
      inside₁.toPathPacking.vertexSet ⊆ K := by
    intro x hx
    rcases inside₁.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
    exact hInside₁ i hi
  have hInside₂Vertex :
      inside₂.toPathPacking.vertexSet ⊆ K := by
    intro x hx
    rcases inside₂.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
    exact hInside₂ i hi
  have hRI₁stay :
      R.retainedFirstInside.toPathPacking.StaysIn K := by
    intro i x hx
    exact hInside₁Vertex (R.retainedFirstInside_path_subset i hx)
  have hRI₂stay :
      R.retainedSecondInside.toPathPacking.StaysIn K := by
    intro i x hx
    exact hInside₂Vertex (R.retainedSecondInside_path_subset i hx)
  have hF₁internalK :
      F₁.toPathPacking.InternallyDisjointFromSet K :=
    outside₁.restrictTargetSet_internallyDisjointFromSet
      R.retainedFirstTarget R.retainedFirstTarget_subset
      hOutside₁InternalK
  have hF₂internalK :
      F₂.toPathPacking.InternallyDisjointFromSet K :=
    outside₂.restrictTargetSet_internallyDisjointFromSet
      R.retainedSecondTarget R.retainedSecondTarget_subset
      hOutside₂InternalK
  have hF₁sourceK :
      Disjoint
        (outside₁.sourceSet
          (outside₁.targetIndexSetOfSubset R.retainedFirstTarget)) K :=
    Finset.disjoint_of_subset_left
      (outside₁.sourceSet_subset_left _) hX₁K
  have hF₂sourceK :
      Disjoint
        (outside₂.sourceSet
          (outside₂.targetIndexSetOfSubset R.retainedSecondTarget)) K :=
    Finset.disjoint_of_subset_left
      (outside₂.sourceSet_subset_left _) hX₂K
  let RF :=
    F₁.concatOfFirstInternallyDisjointSecondStaysIn
      R.retainedFirstInside.reverse hF₁internalK
        (PerfectPathPacking.reverse_staysIn
          R.retainedFirstInside hRI₁stay) hF₁sourceK
  let RS :=
    F₂.concatOfFirstInternallyDisjointSecondStaysIn
      R.retainedSecondInside.reverse hF₂internalK
        (PerfectPathPacking.reverse_staysIn
          R.retainedSecondInside hRI₂stay) hF₂sourceK
  have hRFstay :
      RF.toPathPacking.StaysIn (C₁ ∪ K) := by
    exact
      F₁.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        R.retainedFirstInside.reverse hF₁internalK
          (PerfectPathPacking.reverse_staysIn
            R.retainedFirstInside hRI₁stay) hF₁sourceK
        hF₁stay
  have hRSstay :
      RS.toPathPacking.StaysIn (C₂ ∪ K) := by
    exact
      F₂.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        R.retainedSecondInside.reverse hF₂internalK
          (PerfectPathPacking.reverse_staysIn
            R.retainedSecondInside hRI₂stay) hF₂sourceK
        hF₂stay
  let B₁ := outside₁.restrictTargetSet
    R.bridgeSource R.bridgeSource_subset
  let B₂ := outside₂.restrictTargetSet
    R.bridgeTarget R.bridgeTarget_subset
  have hB₁stay : B₁.toPathPacking.StaysIn C₁ :=
    outside₁.restrictTargetSet_staysIn
      R.bridgeSource R.bridgeSource_subset hOutside₁
  have hB₂stay : B₂.toPathPacking.StaysIn C₂ :=
    outside₂.restrictTargetSet_staysIn
      R.bridgeTarget R.bridgeTarget_subset hOutside₂
  have hBridgeStay :
      R.bridge.toPathPacking.StaysIn K := by
    intro i x hx
    rcases Finset.mem_union.mp (R.bridge_path_subset i hx) with hx₁ | hx₂
    · exact hInside₁Vertex hx₁
    · rcases Finset.mem_union.mp hx₂ with hx₂ | hxK
      · exact hInside₂Vertex hx₂
      · exact hxK
  have hB₁internalK :
      B₁.toPathPacking.InternallyDisjointFromSet K :=
    outside₁.restrictTargetSet_internallyDisjointFromSet
      R.bridgeSource R.bridgeSource_subset hOutside₁InternalK
  have hB₁sourceK :
      Disjoint
        (outside₁.sourceSet
          (outside₁.targetIndexSetOfSubset R.bridgeSource)) K :=
    Finset.disjoint_of_subset_left
      (outside₁.sourceSet_subset_left _) hX₁K
  let H₁ :=
    B₁.concatOfFirstInternallyDisjointSecondStaysIn
      R.bridge hB₁internalK hBridgeStay hB₁sourceK
  have hH₁stay :
      H₁.toPathPacking.StaysIn (C₁ ∪ K) := by
    apply
      B₁.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        R.bridge hB₁internalK hBridgeStay hB₁sourceK hB₁stay
  let Hregion := outside₁.toPathPacking.vertexSet ∪ K
  have hH₁stayRegion :
      H₁.toPathPacking.StaysIn Hregion := by
    intro i x hx
    have hsplit :=
      B₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
        R.bridge hB₁internalK hBridgeStay hB₁sourceK i hx
    rcases Finset.mem_union.mp hsplit with hxB₁ | hxBridge
    · exact Finset.mem_union_left _
        (outside₁.toPathPacking.path_vertexSet_subset_vertexSet
          i.1 (by simpa [B₁] using hxB₁))
    · exact Finset.mem_union_right _
        (hBridgeStay (B₁.indexOfSourceTarget R.bridge i) hxBridge)
  have hB₂revInternalRegion :
      B₂.reverse.toPathPacking.InternallyDisjointFromSet Hregion := by
    intro i x hx hxRegion
    rcases Finset.mem_union.mp hxRegion with hxOutside₁ | hxK
    · rcases outside₁.toPathPacking.mem_vertexSet.mp hxOutside₁ with ⟨j, hj⟩
      exact False.elim
        (Finset.disjoint_left.mp (hOutsideDisj j i.1) hj
          (by simpa [B₂] using hx))
    · exact
        PerfectPathPacking.reverse_internallyDisjointFromSet
          B₂
          (outside₂.restrictTargetSet_internallyDisjointFromSet
            R.bridgeTarget R.bridgeTarget_subset hOutside₂InternalK)
          i hx hxK
  have hB₂revTargetRegion :
      Disjoint
        (outside₂.sourceSet
          (outside₂.targetIndexSetOfSubset R.bridgeTarget)) Hregion := by
    rw [Finset.disjoint_left]
    intro x hxTarget hxRegion
    have hxX₂ : x ∈ X₂ :=
      outside₂.sourceSet_subset_left _ (by simpa [B₂] using hxTarget)
    rcases Finset.mem_union.mp hxRegion with hxOutside₁ | hxK
    · rcases outside₁.toPathPacking.mem_vertexSet.mp hxOutside₁ with ⟨j, hj⟩
      rcases outside₂.source_bijective.2 ⟨x, hxX₂⟩ with ⟨i, hi⟩
      have hxi : x ∈ (outside₂.path i).vertexSet := by
        have hs : (outside₂.path i).source = x := congrArg Subtype.val hi
        simpa [hs] using GraphPath.source_mem_vertexSet (outside₂.path i)
      exact Finset.disjoint_left.mp (hOutsideDisj j i) hj hxi
    · exact Finset.disjoint_left.mp hX₂K hxX₂ hxK
  let H :=
    H₁.concatOfFirstStaysInSecondInternallyDisjoint
      B₂.reverse hH₁stayRegion hB₂revInternalRegion hB₂revTargetRegion
  have hHstayRegion :
      H.toPathPacking.StaysIn (Hregion ∪ C₂) := by
    exact
      H₁.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        B₂.reverse hH₁stayRegion hB₂revInternalRegion hB₂revTargetRegion
        (PerfectPathPacking.reverse_staysIn B₂ hB₂stay)
  have hHstay :
      H.toPathPacking.StaysIn ((C₁ ∪ K) ∪ C₂) := by
    intro i x hx
    rcases Finset.mem_union.mp (hHstayRegion i hx) with hxRegion | hxC₂
    · rcases Finset.mem_union.mp hxRegion with hxOutside₁ | hxK
      · rcases outside₁.toPathPacking.mem_vertexSet.mp hxOutside₁ with
          ⟨j, hj⟩
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (hOutside₁ j hj))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxK)
    · exact Finset.mem_union_right _ hxC₂
  have hTraceRetainedFirst :
      ∀ x ∈ R.retainedFirstTarget,
        ∃ i : R.retainedFirstInside.Index,
          x ∈ (R.retainedFirstInside.path i).vertexSet := by
    intro x hx
    rcases R.retainedFirstInside.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have ht : (R.retainedFirstInside.path i).target = x :=
      congrArg Subtype.val hi
    simpa [ht] using
      GraphPath.target_mem_vertexSet (R.retainedFirstInside.path i)
  have hTraceRetainedSecond :
      ∀ x ∈ R.retainedSecondTarget,
        ∃ i : R.retainedSecondInside.Index,
          x ∈ (R.retainedSecondInside.path i).vertexSet := by
    intro x hx
    rcases R.retainedSecondInside.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have ht : (R.retainedSecondInside.path i).target = x :=
      congrArg Subtype.val hi
    simpa [ht] using
      GraphPath.target_mem_vertexSet (R.retainedSecondInside.path i)
  have hTraceBridgeSource :
      ∀ x ∈ R.bridgeSource,
        ∃ i : R.bridge.Index, x ∈ (R.bridge.path i).vertexSet := by
    intro x hx
    rcases R.bridge.source_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hs : (R.bridge.path i).source = x := congrArg Subtype.val hi
    simpa [hs] using GraphPath.source_mem_vertexSet (R.bridge.path i)
  have hTraceBridgeTarget :
      ∀ x ∈ R.bridgeTarget,
        ∃ i : R.bridge.Index, x ∈ (R.bridge.path i).vertexSet := by
    intro x hx
    rcases R.bridge.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have ht : (R.bridge.path i).target = x := congrArg Subtype.val hi
    simpa [ht] using GraphPath.target_mem_vertexSet (R.bridge.path i)
  have hF₁F₂ :
      F₁.toPathPacking.MutuallyNodeDisjoint F₂.toPathPacking := by
    intro i j
    exact hOutsideDisj i.1 j.1
  have hF₁B₁ :
      F₁.toPathPacking.MutuallyNodeDisjoint B₁.toPathPacking :=
    PerfectPathPacking.restrictTargetSet_mutuallyNodeDisjoint outside₁
      R.retainedFirstTarget_subset R.bridgeSource_subset
      R.bridgeSource_disjoint_retainedFirstTarget.symm
  have hF₂B₂ :
      F₂.toPathPacking.MutuallyNodeDisjoint B₂.toPathPacking :=
    PerfectPathPacking.restrictTargetSet_mutuallyNodeDisjoint outside₂
      R.retainedSecondTarget_subset R.bridgeTarget_subset
      R.bridgeTarget_disjoint_retainedSecondTarget.symm
  have hF₁R₂ :
      F₁.toPathPacking.MutuallyNodeDisjoint
        R.retainedSecondInside.reverse.toPathPacking := by
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      F₁
      R.retainedSecondInside.reverse R.retainedFirstInside
      hF₁internalK hF₁sourceK
      (PerfectPathPacking.reverse_staysIn
        R.retainedSecondInside hRI₂stay)
      hTraceRetainedFirst
    intro i j
    simpa [GraphPath.NodeDisjoint] using
      R.retainedFirst_mutuallyNodeDisjoint_retainedSecond i j
  have hR₁F₂ :
      R.retainedFirstInside.reverse.toPathPacking.MutuallyNodeDisjoint
        F₂.toPathPacking := by
    apply PathPacking.mutuallyNodeDisjoint_symm
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      F₂
      R.retainedFirstInside.reverse R.retainedSecondInside
      hF₂internalK hF₂sourceK
      (PerfectPathPacking.reverse_staysIn
        R.retainedFirstInside hRI₁stay)
      hTraceRetainedSecond
    intro i j
    exact GraphPath.nodeDisjoint_symm
      (by simpa [GraphPath.NodeDisjoint] using
        R.retainedFirst_mutuallyNodeDisjoint_retainedSecond j i)
  have hF₁Bridge :
      F₁.toPathPacking.MutuallyNodeDisjoint R.bridge.toPathPacking := by
    exact PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      F₁
      R.bridge R.retainedFirstInside hF₁internalK hF₁sourceK
      hBridgeStay hTraceRetainedFirst
      R.retainedFirst_mutuallyNodeDisjoint_bridge
  have hF₂Bridge :
      F₂.toPathPacking.MutuallyNodeDisjoint R.bridge.toPathPacking := by
    exact PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      F₂
      R.bridge R.retainedSecondInside hF₂internalK hF₂sourceK
      hBridgeStay hTraceRetainedSecond
      R.retainedSecond_mutuallyNodeDisjoint_bridge
  have hB₁R₁ :
      B₁.toPathPacking.MutuallyNodeDisjoint
        R.retainedFirstInside.reverse.toPathPacking := by
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      B₁
      R.retainedFirstInside.reverse R.bridge hB₁internalK hB₁sourceK
      (PerfectPathPacking.reverse_staysIn
        R.retainedFirstInside hRI₁stay)
      hTraceBridgeSource
    intro i j
    exact GraphPath.nodeDisjoint_symm
      (by simpa [GraphPath.NodeDisjoint] using
        R.retainedFirst_mutuallyNodeDisjoint_bridge j i)
  have hB₁R₂ :
      B₁.toPathPacking.MutuallyNodeDisjoint
        R.retainedSecondInside.reverse.toPathPacking := by
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      B₁
      R.retainedSecondInside.reverse R.bridge hB₁internalK hB₁sourceK
      (PerfectPathPacking.reverse_staysIn
        R.retainedSecondInside hRI₂stay)
      hTraceBridgeSource
    intro i j
    exact GraphPath.nodeDisjoint_symm
      (by simpa [GraphPath.NodeDisjoint] using
        R.retainedSecond_mutuallyNodeDisjoint_bridge j i)
  have hB₂R₁ :
      B₂.toPathPacking.MutuallyNodeDisjoint
        R.retainedFirstInside.reverse.toPathPacking := by
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      B₂
      R.retainedFirstInside.reverse R.bridge
      (outside₂.restrictTargetSet_internallyDisjointFromSet
        R.bridgeTarget R.bridgeTarget_subset hOutside₂InternalK)
      (Finset.disjoint_of_subset_left
        (outside₂.sourceSet_subset_left _) hX₂K)
      (PerfectPathPacking.reverse_staysIn
        R.retainedFirstInside hRI₁stay)
      hTraceBridgeTarget
    intro i j
    exact GraphPath.nodeDisjoint_symm
      (by simpa [GraphPath.NodeDisjoint] using
        R.retainedFirst_mutuallyNodeDisjoint_bridge j i)
  have hB₂R₂ :
      B₂.toPathPacking.MutuallyNodeDisjoint
        R.retainedSecondInside.reverse.toPathPacking := by
    apply PerfectPathPacking.mutuallyNodeDisjoint_of_internal_staysIn_of_target_trace
      B₂
      R.retainedSecondInside.reverse R.bridge
      (outside₂.restrictTargetSet_internallyDisjointFromSet
        R.bridgeTarget R.bridgeTarget_subset hOutside₂InternalK)
      (Finset.disjoint_of_subset_left
        (outside₂.sourceSet_subset_left _) hX₂K)
      (PerfectPathPacking.reverse_staysIn
        R.retainedSecondInside hRI₂stay)
      hTraceBridgeTarget
    intro i j
    exact GraphPath.nodeDisjoint_symm
      (by simpa [GraphPath.NodeDisjoint] using
        R.retainedSecond_mutuallyNodeDisjoint_bridge j i)
  exact ⟨{
    retainedFirstSources :=
      outside₁.sourceSet
        (outside₁.targetIndexSetOfSubset R.retainedFirstTarget)
    retainedSecondSources :=
      outside₂.sourceSet
        (outside₂.targetIndexSetOfSubset R.retainedSecondTarget)
    retainedFirstParents := R.retainedFirst
    retainedSecondParents := R.retainedSecond
    retainedFirstSources_subset := outside₁.sourceSet_subset_left _
    retainedSecondSources_subset := outside₂.sourceSet_subset_left _
    retainedFirstRoute := RF
    retainedSecondRoute := RS
    retainedFirstParents_subset := R.retainedFirst_subset
    retainedSecondParents_subset := R.retainedSecond_subset
    retainedFirst_count := by
      calc
        (outside₁.sourceSet
            (outside₁.targetIndexSetOfSubset R.retainedFirstTarget)).card +
              4 * w =
            F₁.card + 4 * w := by rw [F₁.card_eq_left_card]
        _ = R.retainedFirstTarget.card + 4 * w := by simp [F₁]
        _ = R.retainedFirstInside.card + 4 * w := by
          rw [R.retainedFirstInside.card_eq_right_card]
        _ = R.retainedFirst.card + 4 * w := by
          rw [R.retainedFirstInside.card_eq_left_card]
        _ = inside₁.card := R.retainedFirst_count
        _ = outside₁.card := by
          rw [outside₁.card_eq_right_card, inside₁.card_eq_right_card]
    retainedSecond_count := by
      calc
        (outside₂.sourceSet
            (outside₂.targetIndexSetOfSubset R.retainedSecondTarget)).card +
              4 * w =
            F₂.card + 4 * w := by rw [F₂.card_eq_left_card]
        _ = R.retainedSecondTarget.card + 4 * w := by simp [F₂]
        _ = R.retainedSecondInside.card + 4 * w := by
          rw [R.retainedSecondInside.card_eq_right_card]
        _ = R.retainedSecond.card + 4 * w := by
          rw [R.retainedSecondInside.card_eq_left_card]
        _ = inside₂.card := R.retainedSecond_count
        _ = outside₂.card := by
          rw [outside₂.card_eq_right_card, inside₂.card_eq_right_card]
    usedFirst :=
      outside₁.sourceSet
        (outside₁.targetIndexSetOfSubset R.bridgeSource)
    usedSecond :=
      outside₂.sourceSet
        (outside₂.targetIndexSetOfSubset R.bridgeTarget)
    usedFirst_subset := outside₁.sourceSet_subset_left _
    usedSecond_subset := outside₂.sourceSet_subset_left _
    bridge := H
    bridge_card := by
      calc
        H.card = H₁.card := by simp [H]
        _ = B₁.card := by simp [H₁]
        _ = R.bridgeSource.card := by simp [B₁]
        _ = R.bridge.card := R.bridge.card_eq_left_card.symm
        _ = 4 * w := R.bridge_card
    retainedFirstRoute_staysIn := hRFstay
    retainedSecondRoute_staysIn := hRSstay
    retainedFirstRoute_internallyDisjointFromSet_of := by
      intro L hKL hOutsideL
      have hF₁L :
          F₁.toPathPacking.InternallyDisjointFromSet L :=
        outside₁.restrictTargetSet_internallyDisjointFromSet
          R.retainedFirstTarget R.retainedFirstTarget_subset hOutsideL
      have hRetainedL :
          R.retainedFirstInside.reverse.toPathPacking
            |>.InternallyDisjointFromSet L := by
        apply PerfectPathPacking.reverse_internallyDisjointFromSet
        intro i x hx hxL
        exact False.elim
          (Finset.disjoint_left.mp hKL (hRI₁stay i hx) hxL)
      have hTargetK : R.retainedFirstTarget ⊆ K := by
        intro x hx
        rcases inside₁.target_bijective.2
            ⟨x, R.retainedFirstTarget_subset hx⟩ with ⟨i, hi⟩
        have ht : (inside₁.path i).target = x := congrArg Subtype.val hi
        exact hInside₁ i (by
          simpa [ht] using GraphPath.target_mem_vertexSet (inside₁.path i))
      exact
        F₁.concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
          R.retainedFirstInside.reverse hF₁internalK
          (PerfectPathPacking.reverse_staysIn
            R.retainedFirstInside hRI₁stay) hF₁sourceK
          hF₁L hRetainedL
          (Finset.disjoint_of_subset_left hTargetK hKL)
    retainedSecondRoute_internallyDisjointFromSet_of := by
      intro L hKL hOutsideL
      have hF₂L :
          F₂.toPathPacking.InternallyDisjointFromSet L :=
        outside₂.restrictTargetSet_internallyDisjointFromSet
          R.retainedSecondTarget R.retainedSecondTarget_subset hOutsideL
      have hRetainedL :
          R.retainedSecondInside.reverse.toPathPacking
            |>.InternallyDisjointFromSet L := by
        apply PerfectPathPacking.reverse_internallyDisjointFromSet
        intro i x hx hxL
        exact False.elim
          (Finset.disjoint_left.mp hKL (hRI₂stay i hx) hxL)
      have hTargetK : R.retainedSecondTarget ⊆ K := by
        intro x hx
        rcases inside₂.target_bijective.2
            ⟨x, R.retainedSecondTarget_subset hx⟩ with ⟨i, hi⟩
        have ht : (inside₂.path i).target = x := congrArg Subtype.val hi
        exact hInside₂ i (by
          simpa [ht] using GraphPath.target_mem_vertexSet (inside₂.path i))
      exact
        F₂.concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
          R.retainedSecondInside.reverse hF₂internalK
          (PerfectPathPacking.reverse_staysIn
            R.retainedSecondInside hRI₂stay) hF₂sourceK
          hF₂L hRetainedL
          (Finset.disjoint_of_subset_left hTargetK hKL)
    retainedFirstRoute_path_subset := by
      intro i x hx
      have hsplit :=
        F₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedFirstInside.reverse hF₁internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedFirstInside hRI₁stay)
            hF₁sourceK i hx
      rcases Finset.mem_union.mp hsplit with hxF | hxR
      · exact Finset.mem_union_left _
          (outside₁.toPathPacking.path_vertexSet_subset_vertexSet i.1
            (by simpa [F₁] using hxF))
      · exact Finset.mem_union_right _
          (R.retainedFirstInside_path_subset
            (F₁.indexOfSourceTarget R.retainedFirstInside.reverse i)
            (by simpa using hxR))
    retainedSecondRoute_path_subset := by
      intro i x hx
      have hsplit :=
        F₂.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedSecondInside.reverse hF₂internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedSecondInside hRI₂stay)
            hF₂sourceK i hx
      rcases Finset.mem_union.mp hsplit with hxF | hxR
      · exact Finset.mem_union_left _
          (outside₂.toPathPacking.path_vertexSet_subset_vertexSet i.1
            (by simpa [F₂] using hxF))
      · exact Finset.mem_union_right _
          (R.retainedSecondInside_path_subset
            (F₂.indexOfSourceTarget R.retainedSecondInside.reverse i)
            (by simpa using hxR))
    bridge_staysIn := by
      simpa [Finset.union_assoc] using hHstay
    bridge_internallyDisjointFromSet_of := by
      intro L hKL hOutside₁L hOutside₂L
      have hInside₁L :
          inside₁.toPathPacking.InternallyDisjointFromSet L := by
        intro i x hx hxL
        exact False.elim
          (Finset.disjoint_left.mp hKL (hInside₁ i hx) hxL)
      have hInside₂L :
          inside₂.toPathPacking.InternallyDisjointFromSet L := by
        intro i x hx hxL
        exact False.elim
          (Finset.disjoint_left.mp hKL (hInside₂ i hx) hxL)
      have hBridgeL :
          R.bridge.toPathPacking.InternallyDisjointFromSet L := by
        intro i x hx hxL
        exact False.elim
          (Finset.disjoint_left.mp hKL (hBridgeStay i hx) hxL)
      have hA₁K : A₁ ⊆ K := by
        intro x hx
        rcases inside₁.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
        have ht : (inside₁.path i).target = x := congrArg Subtype.val hi
        exact hInside₁ i (by
          simpa [ht] using GraphPath.target_mem_vertexSet (inside₁.path i))
      have hA₂K : A₂ ⊆ K := by
        intro x hx
        rcases inside₂.target_bijective.2 ⟨x, hx⟩ with ⟨i, hi⟩
        have ht : (inside₂.path i).target = x := congrArg Subtype.val hi
        exact hInside₂ i (by
          simpa [ht] using GraphPath.target_mem_vertexSet (inside₂.path i))
      have hB₁L :
          B₁.toPathPacking.InternallyDisjointFromSet L :=
        outside₁.restrictTargetSet_internallyDisjointFromSet
          R.bridgeSource R.bridgeSource_subset hOutside₁L
      have hBridgeSourceL : Disjoint R.bridgeSource L :=
        Finset.disjoint_of_subset_left
          (R.bridgeSource_subset.trans hA₁K) hKL
      have hH₁L :
          H₁.toPathPacking.InternallyDisjointFromSet L :=
        B₁.concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
          R.bridge hB₁internalK hBridgeStay hB₁sourceK
          hB₁L hBridgeL hBridgeSourceL
      have hB₂L :
          B₂.toPathPacking.InternallyDisjointFromSet L :=
        outside₂.restrictTargetSet_internallyDisjointFromSet
          R.bridgeTarget R.bridgeTarget_subset hOutside₂L
      have hB₂revL :
          B₂.reverse.toPathPacking.InternallyDisjointFromSet L :=
        PerfectPathPacking.reverse_internallyDisjointFromSet B₂ hB₂L
      have hBridgeTargetL : Disjoint R.bridgeTarget L :=
        Finset.disjoint_of_subset_left
          (R.bridgeTarget_subset.trans hA₂K) hKL
      exact
        H₁.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          B₂.reverse hH₁stayRegion hB₂revInternalRegion hB₂revTargetRegion
          hH₁L hB₂revL hBridgeTargetL
    bridge_path_subset := by
      intro i x hx
      have hsplit₂ :=
        H₁.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          B₂.reverse hH₁stayRegion hB₂revInternalRegion
            hB₂revTargetRegion i hx
      rcases Finset.mem_union.mp hsplit₂ with hxH₁ | hxB₂
      · have hsplit₁ :=
          B₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
            R.bridge hB₁internalK hBridgeStay hB₁sourceK i hxH₁
        rcases Finset.mem_union.mp hsplit₁ with hxB₁ | hxBridge
        · exact Finset.mem_union_left _
            (outside₁.toPathPacking.path_vertexSet_subset_vertexSet i.1
              (by simpa [B₁] using hxB₁))
        · rcases Finset.mem_union.mp
              (R.bridge_path_subset
                (B₁.indexOfSourceTarget R.bridge i) hxBridge) with
            hxInside₁ | hxRest
          · exact Finset.mem_union_right _
              (Finset.mem_union_left _ hxInside₁)
          · rcases Finset.mem_union.mp hxRest with hxInside₂ | hxK
            · exact Finset.mem_union_right _
                (Finset.mem_union_right _
                  (Finset.mem_union_left _ hxInside₂))
            · exact Finset.mem_union_right _
                (Finset.mem_union_right _
                  (Finset.mem_union_right _
                    (Finset.mem_union_right _ hxK)))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _
            (Finset.mem_union_right _
              (Finset.mem_union_left _
                (outside₂.toPathPacking.path_vertexSet_subset_vertexSet
                  (H₁.indexOfSourceTarget B₂.reverse i).1
                  (by simpa [B₂] using hxB₂)))))
    retainedFirstRoute_mutuallyNodeDisjoint_retainedSecondRoute := by
      intro i j
      rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro x hxRF hxRS
      have hxRF' :=
        F₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedFirstInside.reverse hF₁internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedFirstInside hRI₁stay)
            hF₁sourceK i hxRF
      have hxRS' :=
        F₂.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedSecondInside.reverse hF₂internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedSecondInside hRI₂stay)
            hF₂sourceK j hxRS
      rcases Finset.mem_union.mp hxRF' with hxF₁ | hxR₁
      · rcases Finset.mem_union.mp hxRS' with hxF₂ | hxR₂
        · exact Finset.disjoint_left.mp (hF₁F₂ i j) hxF₁ hxF₂
        · exact Finset.disjoint_left.mp
            (hF₁R₂ i (F₂.indexOfSourceTarget
              R.retainedSecondInside.reverse j)) hxF₁ hxR₂
      · rcases Finset.mem_union.mp hxRS' with hxF₂ | hxR₂
        · exact Finset.disjoint_left.mp
            (hR₁F₂
              (F₁.indexOfSourceTarget R.retainedFirstInside.reverse i) j)
            hxR₁ hxF₂
        · exact Finset.disjoint_left.mp
            (by
              simpa [GraphPath.NodeDisjoint] using
                R.retainedFirst_mutuallyNodeDisjoint_retainedSecond
                  (F₁.indexOfSourceTarget
                    R.retainedFirstInside.reverse i)
                  (F₂.indexOfSourceTarget
                    R.retainedSecondInside.reverse j))
            hxR₁ hxR₂
    retainedFirstRoute_mutuallyNodeDisjoint_bridge := by
      intro i j
      rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro x hxRF hxH
      have hxRF' :=
        F₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedFirstInside.reverse hF₁internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedFirstInside hRI₁stay)
            hF₁sourceK i hxRF
      have hxH' :=
        H₁.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          B₂.reverse hH₁stayRegion hB₂revInternalRegion
            hB₂revTargetRegion j hxH
      rcases Finset.mem_union.mp hxH' with hxH₁ | hxB₂
      · have hxH₁' :=
          B₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
            R.bridge hB₁internalK hBridgeStay hB₁sourceK j hxH₁
        rcases Finset.mem_union.mp hxRF' with hxF₁ | hxR₁
        · rcases Finset.mem_union.mp hxH₁' with hxB₁ | hxBridge
          · exact Finset.disjoint_left.mp (hF₁B₁ i j) hxF₁ hxB₁
          · exact Finset.disjoint_left.mp
              (hF₁Bridge i
                (B₁.indexOfSourceTarget R.bridge j)) hxF₁ hxBridge
        · rcases Finset.mem_union.mp hxH₁' with hxB₁ | hxBridge
          · exact Finset.disjoint_left.mp
              (PathPacking.mutuallyNodeDisjoint_symm hB₁R₁
                (F₁.indexOfSourceTarget
                  R.retainedFirstInside.reverse i) j) hxR₁ hxB₁
          · exact Finset.disjoint_left.mp
              (by
                simpa [GraphPath.NodeDisjoint] using
                  R.retainedFirst_mutuallyNodeDisjoint_bridge
                    (F₁.indexOfSourceTarget
                      R.retainedFirstInside.reverse i)
                    (B₁.indexOfSourceTarget R.bridge j))
              hxR₁ hxBridge
      · rcases Finset.mem_union.mp hxRF' with hxF₁ | hxR₁
        · exact Finset.disjoint_left.mp
            (hOutsideDisj i.1
              (H₁.indexOfSourceTarget B₂.reverse j).1)
            (by simpa [F₁] using hxF₁) (by simpa [B₂] using hxB₂)
        · exact Finset.disjoint_left.mp
            (PathPacking.mutuallyNodeDisjoint_symm hB₂R₁
              (F₁.indexOfSourceTarget
                R.retainedFirstInside.reverse i)
              (H₁.indexOfSourceTarget B₂.reverse j))
            hxR₁ (by simpa using hxB₂)
    retainedSecondRoute_mutuallyNodeDisjoint_bridge := by
      intro i j
      rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
      intro x hxRS hxH
      have hxRS' :=
        F₂.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          R.retainedSecondInside.reverse hF₂internalK
            (PerfectPathPacking.reverse_staysIn
              R.retainedSecondInside hRI₂stay)
            hF₂sourceK i hxRS
      have hxH' :=
        H₁.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          B₂.reverse hH₁stayRegion hB₂revInternalRegion
            hB₂revTargetRegion j hxH
      rcases Finset.mem_union.mp hxH' with hxH₁ | hxB₂
      · have hxH₁' :=
          B₁.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
            R.bridge hB₁internalK hBridgeStay hB₁sourceK j hxH₁
        rcases Finset.mem_union.mp hxRS' with hxF₂ | hxR₂
        · rcases Finset.mem_union.mp hxH₁' with hxB₁ | hxBridge
          · exact Finset.disjoint_left.mp
              (GraphPath.nodeDisjoint_symm
                (hOutsideDisj j.1 i.1))
              (by simpa [F₂] using hxF₂) (by simpa [B₁] using hxB₁)
          · exact Finset.disjoint_left.mp
              (hF₂Bridge i
                (B₁.indexOfSourceTarget R.bridge j)) hxF₂ hxBridge
        · rcases Finset.mem_union.mp hxH₁' with hxB₁ | hxBridge
          · exact Finset.disjoint_left.mp
              (PathPacking.mutuallyNodeDisjoint_symm hB₁R₂
                (F₂.indexOfSourceTarget
                  R.retainedSecondInside.reverse i) j) hxR₂ hxB₁
          · exact Finset.disjoint_left.mp
              (by
                simpa [GraphPath.NodeDisjoint] using
                  R.retainedSecond_mutuallyNodeDisjoint_bridge
                    (F₂.indexOfSourceTarget
                      R.retainedSecondInside.reverse i)
                    (B₁.indexOfSourceTarget R.bridge j))
              hxR₂ hxBridge
      · rcases Finset.mem_union.mp hxRS' with hxF₂ | hxR₂
        · exact Finset.disjoint_left.mp (hF₂B₂ i
            (H₁.indexOfSourceTarget B₂.reverse j)) hxF₂
            (by simpa using hxB₂)
        · exact Finset.disjoint_left.mp
            (PathPacking.mutuallyNodeDisjoint_symm hB₂R₂
              (F₂.indexOfSourceTarget
                R.retainedSecondInside.reverse i)
              (H₁.indexOfSourceTarget B₂.reverse j))
            hxR₂ (by simpa using hxB₂) }⟩

end AttachedRerouting

section FiniteReserveBookkeeping

theorem Theorem46RoutedDfsState.eight_width_le_leftReserve_card
    {m W ell w : ℕ} {Tsys : StrongTreeOfSetsSystem G m W}
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V}
    (C : Theorem46RoutedDfsState (w := w) S v A)
    (hell : 0 < ell) (hW : 16 * w * ell ^ 2 + 1 < W) :
    8 * w ≤ C.leftReserve.card := by
  have hk :
      (S.selectedBelow v).card ≤ ell := by
    have hsub := Finset.card_le_card (S.selectedBelow_subset_leaves v)
    simpa [S.leaves_card] using hsub
  have hkpos : 0 < (S.selectedBelow v).card := C.active.card_pos
  have hmul :
      8 * (S.selectedBelow v).card * w ≤ 8 * ell * w := by
    exact Nat.mul_le_mul_right w (Nat.mul_le_mul_left 8 hk)
  have hsplit :
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w =
        8 * (S.selectedBelow v).card * w := by
    have hs : (S.selectedBelow v).card - 1 + 1 =
        (S.selectedBelow v).card := by omega
    calc
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w =
          8 * ((S.selectedBelow v).card - 1 + 1) * w := by ring
      _ = 8 * (S.selectedBelow v).card * w := by rw [hs]
  have hhalf :
      8 * (S.selectedBelow v).card * w ≤ W / (2 * ell) :=
    hmul.trans
      (theorem46_halfWidth_reserve_le
        (W := W) (ell := ell) (w := w) hell hW)
  rw [← hsplit] at hhalf
  have hcancel :=
    hhalf.trans C.left_reserve_count
  have hcancel' :
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w ≤
        8 * ((S.selectedBelow v).card - 1) * w +
          C.leftReserve.card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcancel
  exact Nat.le_of_add_le_add_left hcancel'

theorem Theorem46RoutedDfsState.eight_width_le_rightReserve_card
    {m W ell w : ℕ} {Tsys : StrongTreeOfSetsSystem G m W}
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v : Fin m} {A : Finset V}
    (C : Theorem46RoutedDfsState (w := w) S v A)
    (hell : 0 < ell) (hW : 16 * w * ell ^ 2 + 1 < W) :
    8 * w ≤ C.rightReserve.card := by
  have hk :
      (S.selectedBelow v).card ≤ ell := by
    have hsub := Finset.card_le_card (S.selectedBelow_subset_leaves v)
    simpa [S.leaves_card] using hsub
  have hkpos : 0 < (S.selectedBelow v).card := C.active.card_pos
  have hmul :
      8 * (S.selectedBelow v).card * w ≤ 8 * ell * w := by
    exact Nat.mul_le_mul_right w (Nat.mul_le_mul_left 8 hk)
  have hsplit :
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w =
        8 * (S.selectedBelow v).card * w := by
    have hs : (S.selectedBelow v).card - 1 + 1 =
        (S.selectedBelow v).card := by omega
    calc
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w =
          8 * ((S.selectedBelow v).card - 1 + 1) * w := by ring
      _ = 8 * (S.selectedBelow v).card * w := by rw [hs]
  have hhalf :
      8 * (S.selectedBelow v).card * w ≤ W / (2 * ell) :=
    hmul.trans
      (theorem46_halfWidth_reserve_le
        (W := W) (ell := ell) (w := w) hell hW)
  rw [← hsplit] at hhalf
  have hcancel :=
    hhalf.trans C.right_reserve_count
  have hcancel' :
      8 * ((S.selectedBelow v).card - 1) * w + 8 * w ≤
        8 * ((S.selectedBelow v).card - 1) * w +
          C.rightReserve.card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcancel
  exact Nat.le_of_add_le_add_left hcancel'

/-- If `R` is obtained from `U` by discarding exactly `k` elements, then any
subfamily of `U` loses at most `k` elements when intersected with `R`. -/
theorem card_le_card_inter_add_of_subset_of_card_add
    {A R U : Finset V} {k : ℕ}
    (hA : A ⊆ U) (hR : R ⊆ U)
    (hcard : R.card + k = U.card) :
    A.card ≤ (A ∩ R).card + k := by
  classical
  have hAR : A \ R ⊆ U \ R := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hA (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hdiff : (A \ R).card ≤ k := by
    have hUR :
        (U \ R).card + R.card = U.card := by
      simpa [Finset.inter_eq_right.mpr hR] using
        Finset.card_sdiff_add_card_inter U R
    have := Finset.card_le_card hAR
    omega
  have hsplit := Finset.card_sdiff_add_card_inter A R
  omega

/-- One branching merge discards four widths from a child group.  The
eight-width-per-branch reserve allowance absorbs that loss when the sibling
subtree is nonempty. -/
theorem reserve_count_after_twoChild_merge
    {H old fresh kc kd kp w : ℕ}
    (hcount : H ≤ old + 8 * (kc - 1) * w)
    (hloss : old ≤ fresh + 4 * w)
    (hkc : 0 < kc) (hkd : 0 < kd)
    (hcard : kp = kc + kd) :
    H ≤ fresh + 8 * (kp - 1) * w := by
  have hsub : kp - 1 = (kc - 1) + kd := by omega
  have hexpand :
      8 * (kp - 1) * w =
        8 * (kc - 1) * w + 8 * kd * w := by
    rw [hsub]
    ring
  have hfour : 4 * w ≤ 8 * kd * w := by
    have : 1 ≤ kd := hkd
    calc
      4 * w ≤ 8 * w := by omega
      _ ≤ 8 * kd * w := by
        exact Nat.mul_le_mul_right w (Nat.mul_le_mul_left 8 this)
  rw [hexpand]
  omega

end FiniteReserveBookkeeping

section TwoChildPreparation

variable {m W ell w : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

/-- All source-faithful path families needed by one branching-cluster merge.
Keeping this as proof data lets the final DFS assembly use the exact retained
routes and bridge without reconstructing any of the two Lemma 2.19 calls. -/
structure Theorem46TwoChildAttachedData
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v p c d : Fin m}
    {hpv : Tsys.metaTree.Adj v p}
    {hvc : Tsys.metaTree.Adj v c}
    {hvd : Tsys.metaTree.Adj v d}
    {A : Finset V} {k₁ k₂ : ℕ}
    (D : Theorem47TwoChildTransitionData Tsys hpv hvc hvd A k₁ k₂)
    (C : Theorem46RoutedDfsState (w := w) S c D.leftIncoming)
    (E : Theorem46RoutedDfsState (w := w) S d D.rightIncoming) where
  firstPrefix :
    ChildGroupPrefixData
      (C := S.subtreeRegion c) (K := Tsys.cluster v)
      C.leftRoute C.rightRoute D.leftConnector
  secondPrefix :
    ChildGroupPrefixData
      (C := S.subtreeRegion d) (K := Tsys.cluster v)
      E.leftRoute E.rightRoute D.rightConnector
  firstParentTargets : Finset V
  secondParentTargets : Finset V
  firstParentTargets_subset_parent : firstParentTargets ⊆ A
  secondParentTargets_subset_parent : secondParentTargets ⊆ A
  firstInside :
    PerfectPathPacking G firstParentTargets firstPrefix.anchor
  secondInside :
    PerfectPathPacking G secondParentTargets secondPrefix.anchor
  firstInside_staysIn :
    firstInside.toPathPacking.StaysIn (Tsys.cluster v)
  secondInside_staysIn :
    secondInside.toPathPacking.StaysIn (Tsys.cluster v)
  firstInside_internal :
    firstInside.toPathPacking.InternallyDisjointFromSet firstPrefix.anchor
  secondInside_internal :
    secondInside.toPathPacking.InternallyDisjointFromSet secondPrefix.anchor
  firstPrefix_internal_leaf :
    ∀ x, x ∈ S.selectedBelow c →
      firstPrefix.route.toPathPacking.InternallyDisjointFromSet
        (Tsys.cluster x)
  secondPrefix_internal_leaf :
    ∀ x, x ∈ S.selectedBelow d →
      secondPrefix.route.toPathPacking.InternallyDisjointFromSet
        (Tsys.cluster x)
  inside_disjoint :
    firstInside.toPathPacking.MutuallyNodeDisjoint secondInside.toPathPacking
  attached :
    AttachedTwoChildReroutingData
      (C₁ := S.subtreeRegion c ∪ D.leftConnector.toPathPacking.vertexSet)
      (C₂ := S.subtreeRegion d ∪ D.rightConnector.toPathPacking.vertexSet)
      (K := Tsys.cluster v)
      firstPrefix.route secondPrefix.route firstInside secondInside w

set_option maxHeartbeats 3000000 in
/-- Prepare the two child-prefix families, isolate their portions in the
branching cluster, perform the two source-faithful Lemma 2.19 reroutings, and
reattach the prefixes. -/
theorem exists_theorem46TwoChildAttachedData
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v p c d : Fin m}
    {hpv : Tsys.metaTree.Adj v p}
    {hvc : Tsys.metaTree.Adj v c}
    {hvd : Tsys.metaTree.Adj v d}
    {A : Finset V} {k₁ k₂ : ℕ}
    (hc : IsChild Tsys.meta_isTree S.root v c)
    (hd : IsChild Tsys.meta_isTree S.root v d)
    (hcd : c ≠ d)
    (hA : A ⊆ Tsys.interface v p hpv)
    (D : Theorem47TwoChildTransitionData Tsys hpv hvc hvd A k₁ k₂)
    (C : Theorem46RoutedDfsState (w := w) S c D.leftIncoming)
    (E : Theorem46RoutedDfsState (w := w) S d D.rightIncoming)
    (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (Theorem46TwoChildAttachedData S D C E) := by
  classical
  have hvcEq : hvc = S.adj_child hc := Subsingleton.elim _ _
  have hvdEq : hvd = S.adj_child hd := Subsingleton.elim _ _
  have hLeftInternalSubtree :
      D.leftConnector.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion c) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hc D.leftConnector (Z := ∅)
    · intro i x hx
      exact Finset.mem_union_right _
        (Finset.mem_union_left _
          (by simpa [hvcEq] using D.leftConnector_staysIn i hx))
    · simpa [hvcEq] using D.leftConnector_internallyDisjoint_clusters c
    · exact Finset.disjoint_empty_left _
  have hRightInternalSubtree :
      D.rightConnector.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion d) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hd D.rightConnector (Z := ∅)
    · intro i x hx
      exact Finset.mem_union_right _
        (Finset.mem_union_left _
          (by simpa [hvdEq] using D.rightConnector_staysIn i hx))
    · simpa [hvdEq] using D.rightConnector_internallyDisjoint_clusters d
    · exact Finset.disjoint_empty_left _
  have hLeftParentSubtree :
      Disjoint D.leftParent (S.subtreeRegion c) :=
    Finset.disjoint_of_subset_left
      (D.leftParent_subset.trans
        (Tsys.interface_subset_cluster v c hvc))
      (by simpa [hvcEq] using S.cluster_disjoint_subtreeRegion hc)
  have hRightParentSubtree :
      Disjoint D.rightParent (S.subtreeRegion d) :=
    Finset.disjoint_of_subset_left
      (D.rightParent_subset.trans
        (Tsys.interface_subset_cluster v d hvd))
      (by simpa [hvdEq] using S.cluster_disjoint_subtreeRegion hd)
  have hSubtreeCCluster :
      Disjoint (S.subtreeRegion c) (Tsys.cluster v) :=
    (S.cluster_disjoint_subtreeRegion hc).symm
  have hSubtreeDCluster :
      Disjoint (S.subtreeRegion d) (Tsys.cluster v) :=
    (S.cluster_disjoint_subtreeRegion hd).symm
  have hLeftIncomingCluster :
      Disjoint D.leftIncoming (Tsys.cluster v) :=
    Finset.disjoint_of_subset_left
      (D.leftIncoming_subset.trans
        (Tsys.interface_subset_cluster c v hvc.symm))
      (Tsys.cluster_disjoint hvc.ne).symm
  have hRightIncomingCluster :
      Disjoint D.rightIncoming (Tsys.cluster v) :=
    Finset.disjoint_of_subset_left
      (D.rightIncoming_subset.trans
        (Tsys.interface_subset_cluster d v hvd.symm))
      (Tsys.cluster_disjoint hvd.ne).symm
  let G₁ := Classical.choice
    (exists_childGroupPrefixData
      C.leftRoute C.rightRoute D.leftConnector
      C.outerRoutes_disjoint C.leftRoute_staysIn C.rightRoute_staysIn
      (Finset.union_subset C.leftAnchor_subset C.rightAnchor_subset)
      hLeftInternalSubtree hLeftParentSubtree
      hSubtreeCCluster
      (D.leftConnector_internallyDisjoint_clusters v)
      hLeftIncomingCluster)
  let G₂ := Classical.choice
    (exists_childGroupPrefixData
      E.leftRoute E.rightRoute D.rightConnector
      E.outerRoutes_disjoint E.leftRoute_staysIn E.rightRoute_staysIn
      (Finset.union_subset E.leftAnchor_subset E.rightAnchor_subset)
      hRightInternalSubtree hRightParentSubtree
      hSubtreeDCluster
      (D.rightConnector_internallyDisjoint_clusters v)
      hRightIncomingCluster)
  have hLeftRightParent :
      Disjoint D.leftParent D.rightParent :=
    Finset.disjoint_of_subset_left D.leftParent_subset
      (Finset.disjoint_of_subset_right D.rightParent_subset
        (Tsys.interface_disjoint hvc hvd hcd))
  have hGanchors :
      Disjoint G₁.anchor G₂.anchor :=
    hLeftRightParent.mono G₁.anchor_subset G₂.anchor_subset
  have hG₁anchorUnion :
      G₁.anchor ⊆ D.leftParent ∪ D.rightParent :=
    G₁.anchor_subset.trans (Finset.subset_union_left)
  have hG₂anchorUnion :
      G₂.anchor ⊆ D.leftParent ∪ D.rightParent :=
    G₂.anchor_subset.trans (Finset.subset_union_right)
  let A₁ :=
    D.parentPacking.sourceSet
      (D.parentPacking.targetIndexSetOfSubset G₁.anchor)
  let A₂ :=
    D.parentPacking.sourceSet
      (D.parentPacking.targetIndexSetOfSubset G₂.anchor)
  let P₁ := D.parentPacking.restrictTargetSet G₁.anchor hG₁anchorUnion
  let P₂ := D.parentPacking.restrictTargetSet G₂.anchor hG₂anchorUnion
  let I₁ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₁) P₁.reverse
      (by exact Finset.Subset.rfl))
  let I₂ := Classical.choice
    (PerfectPathPacking.exists_firstHitData (C := A₂) P₂.reverse
      (by exact Finset.Subset.rfl))
  have hI₁stay :
      I₁.packing.toPathPacking.StaysIn (Tsys.cluster v) := by
    intro i x hx
    rcases I₁.path_vertexSet_subset i with ⟨j, hj⟩
    exact D.parentPacking_staysIn j.1 (by
      simpa [P₁] using hj hx)
  have hI₂stay :
      I₂.packing.toPathPacking.StaysIn (Tsys.cluster v) := by
    intro i x hx
    rcases I₂.path_vertexSet_subset i with ⟨j, hj⟩
    exact D.parentPacking_staysIn j.1 (by
      simpa [P₂] using hj hx)
  have hInsideDisj :
      I₁.packing.toPathPacking.MutuallyNodeDisjoint
        I₂.packing.toPathPacking := by
    intro i j
    rcases I₁.path_vertexSet_subset i with ⟨a, ha⟩
    rcases I₂.path_vertexSet_subset j with ⟨b, hb⟩
    rw [GraphPath.NodeDisjoint]
    apply (D.parentPacking.node_disjoint ?_).mono
      (by simpa [P₁] using ha)
      (by simpa [P₂] using hb)
    intro hab
    have haTarget :
        (D.parentPacking.path a.1).target ∈ G₁.anchor :=
      (D.parentPacking.mem_targetIndexSetOfSubset G₁.anchor a.1).mp a.2
    have hbTarget :
        (D.parentPacking.path b.1).target ∈ G₂.anchor :=
      (D.parentPacking.mem_targetIndexSetOfSubset G₂.anchor b.1).mp b.2
    exact Finset.disjoint_left.mp hGanchors haTarget
      (by simpa [hab] using hbTarget)
  have hHitDisj : Disjoint I₁.hit I₂.hit :=
    PerfectPathPacking.target_disjoint_of_mutuallyNodeDisjoint
      I₁.packing I₂.packing hInsideDisj
  have hHit₁A :
      I₁.hit ⊆ A := by
    intro x hx
    exact D.parentPacking.sourceSet_subset_left _
      (by simpa [A₁] using I₁.hit_subset hx)
  have hHit₂A :
      I₂.hit ⊆ A := by
    intro x hx
    exact D.parentPacking.sourceSet_subset_left _
      (by simpa [A₂] using I₂.hit_subset hx)
  have hAnchorLink :
      NodeLinkedIn G (Tsys.cluster v) G₁.anchor G₂.anchor :=
    (Tsys.interface_pair_nodeLinked hvc hvd hcd).mono_terminals
      (G₁.anchor_subset.trans D.leftParent_subset)
      (G₂.anchor_subset.trans D.rightParent_subset)
  have hSource₁Hit₁ :
      Disjoint G₁.anchor I₁.hit := by
    exact Finset.disjoint_of_subset_left
      (G₁.anchor_subset.trans D.leftParent_subset)
      (Finset.disjoint_of_subset_right
        (hHit₁A.trans hA)
        (Tsys.interface_disjoint hvc hpv D.parent_ne_left.symm))
  have hSource₂Hit₂ :
      Disjoint G₂.anchor I₂.hit := by
    exact Finset.disjoint_of_subset_left
      (G₂.anchor_subset.trans D.rightParent_subset)
      (Finset.disjoint_of_subset_right
        (hHit₂A.trans hA)
        (Tsys.interface_disjoint hvd hpv D.parent_ne_right.symm))
  have hCleftDisj :
      Disjoint C.leftReserve C.rightReserve :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      C.leftRoute C.rightRoute C.outerRoutes_disjoint
  have hEleftDisj :
      Disjoint E.leftReserve E.rightReserve :=
    PerfectPathPacking.source_disjoint_of_mutuallyNodeDisjoint
      E.leftRoute E.rightRoute E.outerRoutes_disjoint
  have hG₁four : 4 * w ≤ G₁.route.card := by
    have hL := C.eight_width_le_leftReserve_card S hell hW
    have hR := C.eight_width_le_rightReserve_card S hell hW
    rw [G₁.route.card_eq_left_card,
      Finset.card_union_of_disjoint hCleftDisj]
    omega
  have hG₂four : 4 * w ≤ G₂.route.card := by
    have hL := E.eight_width_le_leftReserve_card S hell hW
    have hR := E.eight_width_le_rightReserve_card S hell hW
    rw [G₂.route.card_eq_left_card,
      Finset.card_union_of_disjoint hEleftDisj]
    omega
  let R := Classical.choice
    (exists_twoChildReroutingData_insideCluster
      I₁.packing.reverse I₂.packing.reverse w
      (by
        intro i j
        simpa [GraphPath.NodeDisjoint] using hInsideDisj i j)
      hAnchorLink
      (PerfectPathPacking.reverse_staysIn I₁.packing hI₁stay)
      (PerfectPathPacking.reverse_staysIn I₂.packing hI₂stay)
      (PerfectPathPacking.reverse_internallyDisjointFromSet I₁.packing
        (PerfectPathPacking.internallyDisjointFromSet_left I₁.packing))
      (PerfectPathPacking.reverse_internallyDisjointFromSet I₂.packing
        (PerfectPathPacking.internallyDisjointFromSet_left I₂.packing))
      hSource₁Hit₁.symm hSource₂Hit₂.symm
      (by
        calc
          4 * w ≤ G₁.route.card := hG₁four
          _ = G₁.anchor.card := G₁.route.card_eq_right_card
          _ = P₁.reverse.card := by simp [P₁]
          _ = I₁.packing.reverse.card := I₁.packing_card.symm)
      (by
        calc
          4 * w ≤ G₂.route.card := hG₂four
          _ = G₂.anchor.card := G₂.route.card_eq_right_card
          _ = P₂.reverse.card := by simp [P₂]
          _ = I₂.packing.reverse.card := I₂.packing_card.symm))
  have hSupportDisj :
      Disjoint
        (S.subtreeRegion c ∪ D.leftConnector.toPathPacking.vertexSet)
        (S.subtreeRegion d ∪ D.rightConnector.toPathPacking.vertexSet) := by
    have hLeftVertex :
        D.leftConnector.toPathPacking.vertexSet ⊆
          (Tsys.connector v c hvc).toPathPacking.vertexSet := by
      intro x hx
      rcases D.leftConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      exact D.leftConnector_staysIn i hi
    have hRightVertex :
        D.rightConnector.toPathPacking.vertexSet ⊆
          (Tsys.connector v d hvd).toPathPacking.vertexSet := by
      intro x hx
      rcases D.rightConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      exact D.rightConnector_staysIn i hi
    apply Finset.disjoint_union_left.2
    constructor
    · apply Finset.disjoint_union_right.2
      exact ⟨S.subtreeRegion_disjoint hc hd hcd,
        Finset.disjoint_of_subset_right hRightVertex
          (by simpa [hvdEq] using
            (S.enteringConnector_disjoint_siblingRegion hc hd hcd).symm)⟩
    · apply Finset.disjoint_union_right.2
      constructor
      · exact Finset.disjoint_of_subset_left hLeftVertex
          (by simpa [hvcEq] using
            S.enteringConnector_disjoint_siblingRegion hd hc hcd.symm)
      · exact Finset.disjoint_of_subset_left hLeftVertex
          (Finset.disjoint_of_subset_right hRightVertex
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (Tsys.connector_mutually_nodeDisjoint v c hvc v d hvd (by
                intro he
                rw [Sym2.eq_iff] at he
                rcases he with he | he
                · exact hcd he.2
                · exact hvd.ne he.1))))
  have hOutsideDisj :
      G₁.route.toPathPacking.MutuallyNodeDisjoint
        G₂.route.toPathPacking := by
    intro i j
    rw [GraphPath.NodeDisjoint]
    exact hSupportDisj.mono (G₁.route_staysIn i) (G₂.route_staysIn j)
  have hG₁InternalLeaf :
      ∀ x, x ∈ S.selectedBelow c →
        G₁.route.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster x) := by
    intro x hx
    apply G₁.route_internal_of_trivial_glue
      (C.leftRoute_internallyDisjoint_leafCluster x hx)
      (C.rightRoute_internallyDisjoint_leafCluster x hx)
    · intro i hi
      by_cases hxc : x = c
      · subst x
        exact C.leftRoute_trivial_of_root_selected
          (S.selectedBelow_subset_leaves c hx) i
      · exact False.elim
          (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxc).symm
            (C.leftAnchor_subset (C.leftRoute.target_mem i) |>
              D.leftIncoming_subset |>
              Tsys.interface_subset_cluster c v hvc.symm)
            hi)
    · intro i hi
      by_cases hxc : x = c
      · subst x
        exact C.rightRoute_trivial_of_root_selected
          (S.selectedBelow_subset_leaves c hx) i
      · exact False.elim
          (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxc).symm
            (C.rightAnchor_subset (C.rightRoute.target_mem i) |>
              D.leftIncoming_subset |>
              Tsys.interface_subset_cluster c v hvc.symm)
            hi)
    · exact D.leftConnector_internallyDisjoint_clusters x
  have hG₂InternalLeaf :
      ∀ x, x ∈ S.selectedBelow d →
        G₂.route.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster x) := by
    intro x hx
    apply G₂.route_internal_of_trivial_glue
      (E.leftRoute_internallyDisjoint_leafCluster x hx)
      (E.rightRoute_internallyDisjoint_leafCluster x hx)
    · intro i hi
      by_cases hxd : x = d
      · subst x
        exact E.leftRoute_trivial_of_root_selected
          (S.selectedBelow_subset_leaves d hx) i
      · exact False.elim
          (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxd).symm
            (E.leftAnchor_subset (E.leftRoute.target_mem i) |>
              D.rightIncoming_subset |>
              Tsys.interface_subset_cluster d v hvd.symm)
            hi)
    · intro i hi
      by_cases hxd : x = d
      · subst x
        exact E.rightRoute_trivial_of_root_selected
          (S.selectedBelow_subset_leaves d hx) i
      · exact False.elim
          (Finset.disjoint_left.mp (Tsys.cluster_disjoint hxd).symm
            (E.rightAnchor_subset (E.rightRoute.target_mem i) |>
              D.rightIncoming_subset |>
              Tsys.interface_subset_cluster d v hvd.symm)
            hi)
    · exact D.rightConnector_internallyDisjoint_clusters x
  have hX₁K :
      Disjoint (C.leftReserve ∪ C.rightReserve) (Tsys.cluster v) := by
    apply Finset.disjoint_union_left.2
    constructor
    · apply Finset.disjoint_of_subset_left
        (C.leftReserve_subset_leaf.trans
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants c
              (C.leafOrder C.system.toPathOfSetsSystem.firstIndex).2)))
      exact hSubtreeCCluster
    · apply Finset.disjoint_of_subset_left
        (C.rightReserve_subset_leaf.trans
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants c
              (C.leafOrder C.system.toPathOfSetsSystem.lastIndex).2)))
      exact hSubtreeCCluster
  have hX₂K :
      Disjoint (E.leftReserve ∪ E.rightReserve) (Tsys.cluster v) := by
    apply Finset.disjoint_union_left.2
    constructor
    · apply Finset.disjoint_of_subset_left
        (E.leftReserve_subset_leaf.trans
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants d
              (E.leafOrder E.system.toPathOfSetsSystem.firstIndex).2)))
      exact hSubtreeDCluster
    · apply Finset.disjoint_of_subset_left
        (E.rightReserve_subset_leaf.trans
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants d
              (E.leafOrder E.system.toPathOfSetsSystem.lastIndex).2)))
      exact hSubtreeDCluster
  let B := Classical.choice
    (exists_attachedTwoChildReroutingData
      G₁.route G₂.route I₁.packing.reverse I₂.packing.reverse w
      G₁.route_staysIn G₂.route_staysIn
      (PerfectPathPacking.reverse_staysIn I₁.packing hI₁stay)
      (PerfectPathPacking.reverse_staysIn I₂.packing hI₂stay)
      G₁.route_internallyDisjoint_parent
      G₂.route_internallyDisjoint_parent
      hX₁K hX₂K hOutsideDisj R)
  exact ⟨{
    firstPrefix := G₁
    secondPrefix := G₂
    firstParentTargets := I₁.hit
    secondParentTargets := I₂.hit
    firstParentTargets_subset_parent := hHit₁A
    secondParentTargets_subset_parent := hHit₂A
    firstInside := I₁.packing.reverse
    secondInside := I₂.packing.reverse
    firstInside_staysIn :=
      PerfectPathPacking.reverse_staysIn I₁.packing hI₁stay
    secondInside_staysIn :=
      PerfectPathPacking.reverse_staysIn I₂.packing hI₂stay
    firstInside_internal :=
      PerfectPathPacking.reverse_internallyDisjointFromSet I₁.packing
        (PerfectPathPacking.internallyDisjointFromSet_left I₁.packing)
    secondInside_internal :=
      PerfectPathPacking.reverse_internallyDisjointFromSet I₂.packing
        (PerfectPathPacking.internallyDisjointFromSet_left I₂.packing)
    firstPrefix_internal_leaf := hG₁InternalLeaf
    secondPrefix_internal_leaf := hG₂InternalLeaf
    inside_disjoint := by
      intro i j
      simpa [GraphPath.NodeDisjoint] using hInsideDisj i j
    attached := B }⟩

end TwoChildPreparation

section ReplaceOuterNails

/-- Replace both unused outer nail sets.  The extra disjointness hypothesis is
needed only when the system has one cluster, in which case the first and last
clusters coincide. -/
noncomputable def StrongPathOfSetsSystem.replaceBothOuterNails
    {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (L R : Finset V)
    (hLcluster : L ⊆ P.cluster P.toPathOfSetsSystem.firstIndex)
    (hRcluster : R ⊆ P.cluster P.toPathOfSetsSystem.lastIndex)
    (hLold :
      Disjoint L (P.right P.toPathOfSetsSystem.firstIndex))
    (hOldR :
      Disjoint (P.left P.toPathOfSetsSystem.lastIndex) R)
    (hLR : Disjoint L R)
    (hLcard : L.card = w) (hRcard : R.card = w)
    (hLwl :
      NodeWellLinkedIn G
        (P.cluster P.toPathOfSetsSystem.firstIndex) L)
    (hRwl :
      NodeWellLinkedIn G
        (P.cluster P.toPathOfSetsSystem.lastIndex) R)
    (hLlinked :
      NodeLinkedIn G
        (P.cluster P.toPathOfSetsSystem.firstIndex) L
        (P.right P.toPathOfSetsSystem.firstIndex))
    (hRlinked :
      NodeLinkedIn G
        (P.cluster P.toPathOfSetsSystem.lastIndex)
        (P.left P.toPathOfSetsSystem.lastIndex) R)
    (hLRlinked :
      P.toPathOfSetsSystem.firstIndex =
          P.toPathOfSetsSystem.lastIndex →
        NodeLinkedIn G
          (P.cluster P.toPathOfSetsSystem.firstIndex) L R) :
    StrongPathOfSetsSystem G ell w := by
  let Q := P.replaceLeftFirst L hLcluster hLold hLcard hLwl hLlinked
  have hQlast :
      Q.toPathOfSetsSystem.lastIndex =
        P.toPathOfSetsSystem.lastIndex := rfl
  apply Q.replaceRightLast R
  · simpa [Q] using hRcluster
  · change
      Disjoint
        (if Q.toPathOfSetsSystem.lastIndex =
              P.toPathOfSetsSystem.firstIndex then L
          else P.left Q.toPathOfSetsSystem.lastIndex) R
    rw [hQlast]
    by_cases h :
        P.toPathOfSetsSystem.lastIndex =
          P.toPathOfSetsSystem.firstIndex
    · simp [h, hLR]
    · simp [h, hOldR]
  · exact hRcard
  · simpa [Q] using hRwl
  · change
      NodeLinkedIn G
        (P.cluster Q.toPathOfSetsSystem.lastIndex)
        (if Q.toPathOfSetsSystem.lastIndex =
              P.toPathOfSetsSystem.firstIndex then L
          else P.left Q.toPathOfSetsSystem.lastIndex) R
    rw [hQlast]
    by_cases h :
        P.toPathOfSetsSystem.lastIndex =
          P.toPathOfSetsSystem.firstIndex
    · have h' :
          P.toPathOfSetsSystem.firstIndex =
            P.toPathOfSetsSystem.lastIndex := h.symm
      simpa [h] using hLRlinked h'
    · simpa [h] using hRlinked

@[simp] theorem StrongPathOfSetsSystem.replaceBothOuterNails_cluster
    {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (L R : Finset V)
    (hLcluster hRcluster hLold hOldR hLR hLcard hRcard
      hLwl hRwl hLlinked hRlinked hLRlinked)
    (i : Fin ell) :
    (StrongPathOfSetsSystem.replaceBothOuterNails
      P L R hLcluster hRcluster hLold hOldR hLR
      hLcard hRcard hLwl hRwl hLlinked hRlinked hLRlinked).cluster i =
        P.cluster i := rfl

@[simp] theorem StrongPathOfSetsSystem.replaceBothOuterNails_left_first
    {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (L R : Finset V)
    (hLcluster hRcluster hLold hOldR hLR hLcard hRcard
      hLwl hRwl hLlinked hRlinked hLRlinked) :
    (StrongPathOfSetsSystem.replaceBothOuterNails
      P L R hLcluster hRcluster hLold hOldR hLR
      hLcard hRcard hLwl hRwl hLlinked hRlinked hLRlinked).left
        P.toPathOfSetsSystem.firstIndex = L := by
  unfold StrongPathOfSetsSystem.replaceBothOuterNails
  simp [StrongPathOfSetsSystem.replaceRightLast,
    StrongPathOfSetsSystem.replaceLeftFirst]

@[simp] theorem StrongPathOfSetsSystem.replaceBothOuterNails_right_last
    {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (L R : Finset V)
    (hLcluster hRcluster hLold hOldR hLR hLcard hRcard
      hLwl hRwl hLlinked hRlinked hLRlinked) :
    (StrongPathOfSetsSystem.replaceBothOuterNails
      P L R hLcluster hRcluster hLold hOldR hLR
      hLcard hRcard hLwl hRwl hLlinked hRlinked hLRlinked).right
        P.toPathOfSetsSystem.lastIndex = R := by
  have hlast :
      P.toPathOfSetsSystem.lastIndex =
        (P.replaceLeftFirst L hLcluster hLold hLcard hLwl hLlinked
          ).toPathOfSetsSystem.lastIndex := rfl
  unfold StrongPathOfSetsSystem.replaceBothOuterNails
  simp [StrongPathOfSetsSystem.replaceRightLast,
    StrongPathOfSetsSystem.replaceLeftFirst, hlast]

end ReplaceOuterNails

section TwoChildAssembly

variable {m W ell w : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

set_option maxHeartbeats 5000000 in
/-- The complete two-child DFS merge in journal Theorem 4.6. -/
theorem exists_theorem46RoutedDfsState_twoChildren
    (S : Theorem46LeafExtractionSetup Tsys ell)
    {v p c d : Fin m}
    {hpv : Tsys.metaTree.Adj v p}
    {hvc : Tsys.metaTree.Adj v c}
    {hvd : Tsys.metaTree.Adj v d}
    {A : Finset V} {k₁ k₂ : ℕ}
    (hc : IsChild Tsys.meta_isTree S.root v c)
    (hd : IsChild Tsys.meta_isTree S.root v d)
    (hcd : c ≠ d)
    (hbelow :
      S.selectedBelow v = S.selectedBelow c ∪ S.selectedBelow d)
    (hA : A ⊆ Tsys.interface v p hpv)
    (D : Theorem47TwoChildTransitionData Tsys hpv hvc hvd A k₁ k₂)
    (C : Theorem46RoutedDfsState (w := w) S c D.leftIncoming)
    (E : Theorem46RoutedDfsState (w := w) S d D.rightIncoming)
    (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (Theorem46RoutedDfsState (w := w) S v A) := by
  classical
  let F := Classical.choice
    (exists_theorem46TwoChildAttachedData
      S hc hd hcd hA D C E hell hW)
  obtain ⟨b₁, b₂, I, hIcard, hIclass⟩ :=
    exists_bridge_index_class
      C.leftReserve C.rightReserve E.leftReserve E.rightReserve
      (fun i => (F.attached.bridge.path i).source)
      (fun i => (F.attached.bridge.path i).target)
      (fun i => F.attached.usedFirst_subset
        (F.attached.bridge.source_mem i))
      (fun i => F.attached.usedSecond_subset
        (F.attached.bridge.target_mem i))
      (by
        change 4 * w ≤ F.attached.bridge.card
        rw [F.attached.bridge_card])
  let bridge := F.attached.bridge.restrictIndexSet I
  let bridgeLeft := F.attached.bridge.sourceSet I
  let bridgeRight := F.attached.bridge.targetSet I
  have hBridgeLeftClass :
      bridgeLeft ⊆ (if b₁ then C.leftReserve else C.rightReserve) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact (hIclass i hi).1
  have hBridgeRightClass :
      bridgeRight ⊆ (if b₂ then E.leftReserve else E.rightReserve) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact (hIclass i hi).2
  have hBridgeLeftCard : bridgeLeft.card = w := by
    simpa [bridgeLeft] using
      F.attached.bridge.sourceSet_card I |>.trans hIcard
  have hBridgeRightCard : bridgeRight.card = w := by
    simpa [bridgeRight] using
      F.attached.bridge.targetSet_card I |>.trans hIcard
  let firstOldOuter :=
    if b₁ then C.rightReserve else C.leftReserve
  let secondOldOuter :=
    if b₂ then E.rightReserve else E.leftReserve
  let firstReserve :=
    F.attached.retainedFirstSources ∩ firstOldOuter
  let secondReserve :=
    F.attached.retainedSecondSources ∩ secondOldOuter
  have hFirstOldSubset :
      firstOldOuter ⊆ C.leftReserve ∪ C.rightReserve := by
    cases b₁ <;> simp [firstOldOuter]
  have hSecondOldSubset :
      secondOldOuter ⊆ E.leftReserve ∪ E.rightReserve := by
    cases b₂ <;> simp [secondOldOuter]
  have hFirstLoss :
      firstOldOuter.card ≤ firstReserve.card + 4 * w := by
    simpa [firstReserve, Finset.inter_comm] using
      (card_le_card_inter_add_of_subset_of_card_add
        hFirstOldSubset F.attached.retainedFirstSources_subset (by
          calc
            F.attached.retainedFirstSources.card + 4 * w =
                F.firstPrefix.route.card := F.attached.retainedFirst_count
            _ = (C.leftReserve ∪ C.rightReserve).card :=
              F.firstPrefix.route.card_eq_left_card))
  have hSecondLoss :
      secondOldOuter.card ≤ secondReserve.card + 4 * w := by
    simpa [secondReserve, Finset.inter_comm] using
      (card_le_card_inter_add_of_subset_of_card_add
        hSecondOldSubset F.attached.retainedSecondSources_subset (by
          calc
            F.attached.retainedSecondSources.card + 4 * w =
                F.secondPrefix.route.card := F.attached.retainedSecond_count
            _ = (E.leftReserve ∪ E.rightReserve).card :=
              F.secondPrefix.route.card_eq_left_card))
  have hFirstOldEight : 8 * w ≤ firstOldOuter.card := by
    cases b₁
    · exact C.eight_width_le_leftReserve_card S hell hW
    · exact C.eight_width_le_rightReserve_card S hell hW
  have hSecondOldEight : 8 * w ≤ secondOldOuter.card := by
    cases b₂
    · exact E.eight_width_le_leftReserve_card S hell hW
    · exact E.eight_width_le_rightReserve_card S hell hW
  have hwFirst : w ≤ firstReserve.card := by omega
  have hwSecond : w ≤ secondReserve.card := by omega
  obtain ⟨firstNails, hFirstNails, hFirstNailsCard⟩ :=
    Finset.exists_subset_card_eq hwFirst
  obtain ⟨secondNails, hSecondNails, hSecondNailsCard⟩ :=
    Finset.exists_subset_card_eq hwSecond
  let firstRoute :=
    F.attached.retainedFirstRoute.restrictSourceSet
      firstReserve Finset.inter_subset_left
  let secondRoute :=
    F.attached.retainedSecondRoute.restrictSourceSet
      secondReserve Finset.inter_subset_left
  let firstAnchor :=
    F.attached.retainedFirstRoute.targetSet
      (F.attached.retainedFirstRoute.sourceIndexSetOfSubset firstReserve)
  let secondAnchor :=
    F.attached.retainedSecondRoute.targetSet
      (F.attached.retainedSecondRoute.sourceIndexSetOfSubset secondReserve)
  have hFirstAnchorA : firstAnchor ⊆ A := by
    exact F.attached.retainedFirstRoute.targetSet_subset_right _
      |>.trans F.attached.retainedFirstParents_subset
      |>.trans F.firstParentTargets_subset_parent
  have hSecondAnchorA : secondAnchor ⊆ A := by
    exact F.attached.retainedSecondRoute.targetSet_subset_right _
      |>.trans F.attached.retainedSecondParents_subset
      |>.trans F.secondParentTargets_subset_parent
  let Cn := if b₁ then C.reverse S else C
  let En := if b₂ then E else E.reverse S
  have hFirstNailsReserve :
      firstNails ⊆ Cn.leftReserve := by
    apply hFirstNails.trans
    apply Finset.inter_subset_right.trans
    cases b₁ <;> simp [firstOldOuter, Cn,
      Theorem46RoutedDfsState.reverse]
  have hSecondNailsReserve :
      secondNails ⊆ En.rightReserve := by
    apply hSecondNails.trans
    apply Finset.inter_subset_right.trans
    cases b₂ <;> simp [secondOldOuter, En,
      Theorem46RoutedDfsState.reverse]
  have hBridgeLeftReserve :
      bridgeLeft ⊆ Cn.rightReserve := by
    cases b₁ <;> simpa [Cn, Theorem46RoutedDfsState.reverse] using
      hBridgeLeftClass
  have hBridgeRightReserve :
      bridgeRight ⊆ En.leftReserve := by
    cases b₂ <;> simpa [En, Theorem46RoutedDfsState.reverse] using
      hBridgeRightClass
  have hFirstNailsAmbient :
      firstNails ⊆ Cn.leftAmbient := by
    exact hFirstNailsReserve.trans Cn.leftReserve_subset_ambient
  have hSecondNailsAmbient :
      secondNails ⊆ En.rightAmbient := by
    exact hSecondNailsReserve.trans En.rightReserve_subset_ambient
  have hBridgeLeftAmbient :
      bridgeLeft ⊆ Cn.rightAmbient := by
    exact hBridgeLeftReserve.trans Cn.rightReserve_subset_ambient
  have hBridgeRightAmbient :
      bridgeRight ⊆ En.leftAmbient := by
    exact hBridgeRightReserve.trans En.leftReserve_subset_ambient
  have hFirstNailsCluster :
      firstNails ⊆
        Cn.system.cluster Cn.system.toPathOfSetsSystem.firstIndex :=
    by
      rw [Cn.cluster_eq]
      exact hFirstNailsAmbient.trans Cn.leftAmbient_subset_leaf
  have hSecondNailsCluster :
      secondNails ⊆
        En.system.cluster En.system.toPathOfSetsSystem.lastIndex :=
    by
      rw [En.cluster_eq]
      exact hSecondNailsAmbient.trans En.rightAmbient_subset_leaf
  have hBridgeLeftCluster :
      bridgeLeft ⊆
        Cn.system.cluster Cn.system.toPathOfSetsSystem.lastIndex :=
    by
      rw [Cn.cluster_eq]
      exact hBridgeLeftAmbient.trans Cn.rightAmbient_subset_leaf
  have hBridgeRightCluster :
      bridgeRight ⊆
        En.system.cluster En.system.toPathOfSetsSystem.firstIndex :=
    by
      rw [En.cluster_eq]
      exact hBridgeRightAmbient.trans En.leftAmbient_subset_leaf
  have hFirstNailsOld :
      Disjoint firstNails
        (Cn.system.right Cn.system.toPathOfSetsSystem.firstIndex) :=
    Cn.leftReserve_disjoint_firstRight.mono_left hFirstNailsReserve
  have hOldBridgeLeft :
      Disjoint
        (Cn.system.left Cn.system.toPathOfSetsSystem.lastIndex)
        bridgeLeft :=
    Cn.rightReserve_disjoint_lastLeft.mono_right hBridgeLeftReserve
  have hBridgeRightOld :
      Disjoint bridgeRight
        (En.system.right En.system.toPathOfSetsSystem.firstIndex) :=
    En.leftReserve_disjoint_firstRight.mono_left hBridgeRightReserve
  have hOldSecondNails :
      Disjoint
        (En.system.left En.system.toPathOfSetsSystem.lastIndex)
        secondNails :=
    En.rightReserve_disjoint_lastLeft.mono_right hSecondNailsReserve
  have hFirstBridgeDisj : Disjoint firstNails bridgeLeft := by
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        F.attached.retainedFirstRoute_mutuallyNodeDisjoint_bridge).mono
        (hFirstNails.trans Finset.inter_subset_left |>.trans
          (PerfectPathPacking.left_subset_vertexSet
            F.attached.retainedFirstRoute))
        (F.attached.bridge.sourceSet_subset_left I |>.trans
          (PerfectPathPacking.left_subset_vertexSet F.attached.bridge))
  have hBridgeSecondDisj : Disjoint bridgeRight secondNails := by
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (PathPacking.mutuallyNodeDisjoint_symm
          F.attached.retainedSecondRoute_mutuallyNodeDisjoint_bridge)).mono
        (F.attached.bridge.targetSet_subset_right I |>.trans
          (PerfectPathPacking.right_subset_vertexSet F.attached.bridge))
        (hSecondNails.trans Finset.inter_subset_left |>.trans
          (PerfectPathPacking.left_subset_vertexSet
            F.attached.retainedSecondRoute))
  have hFirstNailsWL :
      NodeWellLinkedIn G
        (Cn.system.cluster Cn.system.toPathOfSetsSystem.firstIndex)
        firstNails :=
    by
      rw [Cn.cluster_eq]
      exact Cn.leftAmbient_nodeWellLinked.mono_terminals hFirstNailsAmbient
  have hBridgeLeftWL :
      NodeWellLinkedIn G
        (Cn.system.cluster Cn.system.toPathOfSetsSystem.lastIndex)
        bridgeLeft :=
    by
      rw [Cn.cluster_eq]
      exact Cn.rightAmbient_nodeWellLinked.mono_terminals hBridgeLeftAmbient
  have hBridgeRightWL :
      NodeWellLinkedIn G
        (En.system.cluster En.system.toPathOfSetsSystem.firstIndex)
        bridgeRight :=
    by
      rw [En.cluster_eq]
      exact En.leftAmbient_nodeWellLinked.mono_terminals hBridgeRightAmbient
  have hSecondNailsWL :
      NodeWellLinkedIn G
        (En.system.cluster En.system.toPathOfSetsSystem.lastIndex)
        secondNails :=
    by
      rw [En.cluster_eq]
      exact En.rightAmbient_nodeWellLinked.mono_terminals hSecondNailsAmbient
  have hFirstNailsLinked :
      NodeLinkedIn G
        (Cn.system.cluster Cn.system.toPathOfSetsSystem.firstIndex)
        firstNails
        (Cn.system.right Cn.system.toPathOfSetsSystem.firstIndex) := by
    rw [Cn.cluster_eq]
    exact Cn.leftAmbient_nodeWellLinked.nodeLinkedIn_between_disjoint_subsets
      hFirstNailsAmbient Cn.first_right_subset_ambient hFirstNailsOld
  have hBridgeLeftLinked :
      NodeLinkedIn G
        (Cn.system.cluster Cn.system.toPathOfSetsSystem.lastIndex)
        (Cn.system.left Cn.system.toPathOfSetsSystem.lastIndex)
        bridgeLeft := by
    rw [Cn.cluster_eq]
    exact Cn.rightAmbient_nodeWellLinked.nodeLinkedIn_between_disjoint_subsets
      Cn.last_left_subset_ambient hBridgeLeftAmbient hOldBridgeLeft
  have hFirstBridgeLinked :
      Cn.system.toPathOfSetsSystem.firstIndex =
          Cn.system.toPathOfSetsSystem.lastIndex →
        NodeLinkedIn G
          (Cn.system.cluster Cn.system.toPathOfSetsSystem.firstIndex)
          firstNails bridgeLeft := by
    intro h
    rw [Cn.cluster_eq]
    exact Cn.outerAmbient_linked_of_singleton h
      hFirstNailsAmbient hBridgeLeftAmbient hFirstBridgeDisj
  have hBridgeRightLinked :
      NodeLinkedIn G
        (En.system.cluster En.system.toPathOfSetsSystem.firstIndex)
        bridgeRight
        (En.system.right En.system.toPathOfSetsSystem.firstIndex) := by
    rw [En.cluster_eq]
    exact En.leftAmbient_nodeWellLinked.nodeLinkedIn_between_disjoint_subsets
      hBridgeRightAmbient En.first_right_subset_ambient hBridgeRightOld
  have hSecondNailsLinked :
      NodeLinkedIn G
        (En.system.cluster En.system.toPathOfSetsSystem.lastIndex)
        (En.system.left En.system.toPathOfSetsSystem.lastIndex)
        secondNails := by
    rw [En.cluster_eq]
    exact En.rightAmbient_nodeWellLinked.nodeLinkedIn_between_disjoint_subsets
      En.last_left_subset_ambient hSecondNailsAmbient hOldSecondNails
  have hBridgeSecondLinked :
      En.system.toPathOfSetsSystem.firstIndex =
          En.system.toPathOfSetsSystem.lastIndex →
        NodeLinkedIn G
          (En.system.cluster En.system.toPathOfSetsSystem.firstIndex)
          bridgeRight secondNails := by
    intro h
    rw [En.cluster_eq]
    exact En.outerAmbient_linked_of_singleton h
      hBridgeRightAmbient hSecondNailsAmbient hBridgeSecondDisj
  let P :=
    StrongPathOfSetsSystem.replaceBothOuterNails
      Cn.system firstNails bridgeLeft
      hFirstNailsCluster hBridgeLeftCluster hFirstNailsOld hOldBridgeLeft
      hFirstBridgeDisj hFirstNailsCard hBridgeLeftCard
      hFirstNailsWL hBridgeLeftWL
      hFirstNailsLinked hBridgeLeftLinked hFirstBridgeLinked
  let Q :=
    StrongPathOfSetsSystem.replaceBothOuterNails
      En.system bridgeRight secondNails
      hBridgeRightCluster hSecondNailsCluster hBridgeRightOld hOldSecondNails
      hBridgeSecondDisj hBridgeRightCard hSecondNailsCard
      hBridgeRightWL hSecondNailsWL
      hBridgeRightLinked hSecondNailsLinked hBridgeSecondLinked
  have hPright :
      P.right P.toPathOfSetsSystem.lastIndex = bridgeLeft := by
    simpa [P] using
      StrongPathOfSetsSystem.replaceBothOuterNails_right_last
        Cn.system firstNails bridgeLeft _ _ _ _ _ _ _ _ _ _ _ _
  have hQleft :
      Q.left Q.toPathOfSetsSystem.firstIndex = bridgeRight := by
    simpa [Q] using
      StrongPathOfSetsSystem.replaceBothOuterNails_left_first
        En.system bridgeRight secondNails _ _ _ _ _ _ _ _ _ _ _ _
  let bridge' : PerfectPathPacking G
      (P.right P.toPathOfSetsSystem.lastIndex)
      (Q.left Q.toPathOfSetsSystem.firstIndex) :=
    bridge.copyTerminals hPright.symm hQleft.symm
  have hvcEq : hvc = S.adj_child hc := Subsingleton.elim _ _
  have hvdEq : hvd = S.adj_child hd := Subsingleton.elim _ _
  have hBranchSupportDisj :
      Disjoint
        (S.subtreeRegion c ∪ D.leftConnector.toPathPacking.vertexSet)
        (S.subtreeRegion d ∪ D.rightConnector.toPathPacking.vertexSet) := by
    have hLeftVertex :
        D.leftConnector.toPathPacking.vertexSet ⊆
          (Tsys.connector v c hvc).toPathPacking.vertexSet := by
      intro x hx
      rcases D.leftConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      exact D.leftConnector_staysIn i hi
    have hRightVertex :
        D.rightConnector.toPathPacking.vertexSet ⊆
          (Tsys.connector v d hvd).toPathPacking.vertexSet := by
      intro x hx
      rcases D.rightConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      exact D.rightConnector_staysIn i hi
    apply Finset.disjoint_union_left.2
    constructor
    · apply Finset.disjoint_union_right.2
      exact ⟨S.subtreeRegion_disjoint hc hd hcd,
        Finset.disjoint_of_subset_right hRightVertex
          (by simpa [hvdEq] using
            (S.enteringConnector_disjoint_siblingRegion hc hd hcd).symm)⟩
    · apply Finset.disjoint_union_right.2
      constructor
      · exact Finset.disjoint_of_subset_left hLeftVertex
          (by simpa [hvcEq] using
            S.enteringConnector_disjoint_siblingRegion hd hc hcd.symm)
      · exact Finset.disjoint_of_subset_left hLeftVertex
          (Finset.disjoint_of_subset_right hRightVertex
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (Tsys.connector_mutually_nodeDisjoint v c hvc v d hvd (by
                intro he
                rw [Sym2.eq_iff] at he
                rcases he with he | he
                · exact hcd he.2
                · exact hvd.ne he.1))))
  have hCrossCluster :
      ∀ (i : Fin (S.selectedBelow c).card)
        (j : Fin (S.selectedBelow d).card),
        Disjoint (P.cluster i) (Q.cluster j) := by
    intro i j
    rw [StrongPathOfSetsSystem.replaceBothOuterNails_cluster,
      StrongPathOfSetsSystem.replaceBothOuterNails_cluster,
      Cn.cluster_eq, En.cluster_eq]
    apply Tsys.cluster_disjoint
    intro heq
    exact Finset.disjoint_left.mp
      (S.selectedBelow_children_disjoint
        ((mem_children Tsys.meta_isTree S.root v c).2 hc)
        ((mem_children Tsys.meta_isTree S.root v d).2 hd) hcd)
      (Cn.leafOrder i).2 (by simpa [heq] using (En.leafOrder j).2)
  have hPConnectorStay :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card),
        (P.connector i hi).toPathPacking.StaysIn (S.subtreeRegion c) := by
    intro i hi
    simpa [P, StrongPathOfSetsSystem.replaceBothOuterNails,
      StrongPathOfSetsSystem.replaceRightLast,
      StrongPathOfSetsSystem.replaceLeftFirst] using
      Cn.connectors_stayIn i hi
  have hQConnectorStay :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        (Q.connector j hj).toPathPacking.StaysIn (S.subtreeRegion d) := by
    intro j hj
    simpa [Q, StrongPathOfSetsSystem.replaceBothOuterNails,
      StrongPathOfSetsSystem.replaceRightLast,
      StrongPathOfSetsSystem.replaceLeftFirst] using
      En.connectors_stayIn j hj
  have hCrossConnector :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card)
        (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        (P.connector i hi).toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking := by
    intro i hi j hj
    exact PathPacking.mutuallyNodeDisjoint_of_staysIn_disjoint
      _ _ (hPConnectorStay i hi) (hQConnectorStay j hj)
      (S.subtreeRegion_disjoint hc hd hcd)
  have hPConnectorInternalQ :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card)
        (j : Fin (S.selectedBelow d).card),
        (P.connector i hi).toPathPacking
          |>.InternallyDisjointFromSet (Q.cluster j) := by
    intro i hi j a x hx hxQ
    have hxC := hPConnectorStay i hi a hx
    have hxD :
        x ∈ S.subtreeRegion d := by
      apply S.cluster_subset_subtreeRegion_of_mem
        (S.selectedBelow_subset_descendants d (En.leafOrder j).2)
      rw [← En.cluster_eq]
      simpa [Q] using hxQ
    exact False.elim
      (Finset.disjoint_left.mp (S.subtreeRegion_disjoint hc hd hcd) hxC hxD)
  have hQConnectorInternalP :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card)
        (i : Fin (S.selectedBelow c).card),
        (Q.connector j hj).toPathPacking
          |>.InternallyDisjointFromSet (P.cluster i) := by
    intro j hj i a x hx hxP
    have hxD := hQConnectorStay j hj a hx
    have hxC :
        x ∈ S.subtreeRegion c := by
      apply S.cluster_subset_subtreeRegion_of_mem
        (S.selectedBelow_subset_descendants c (Cn.leafOrder i).2)
      rw [← Cn.cluster_eq]
      simpa [P] using hxP
    exact False.elim
      (Finset.disjoint_left.mp
        (S.subtreeRegion_disjoint hc hd hcd).symm hxD hxC)
  have hBridgeInternalP :
      ∀ i : Fin (S.selectedBelow c).card,
        bridge'.toPathPacking.InternallyDisjointFromSet (P.cluster i) := by
    intro i
    have hLeafSub :
        Tsys.cluster (Cn.leafOrder i).1 ⊆ S.subtreeRegion c :=
      S.cluster_subset_subtreeRegion_of_mem
        (S.selectedBelow_subset_descendants c (Cn.leafOrder i).2)
    have hKL :
        Disjoint (Tsys.cluster v) (Tsys.cluster (Cn.leafOrder i).1) :=
      Finset.disjoint_of_subset_right hLeafSub
        (S.cluster_disjoint_subtreeRegion hc)
    have hSecondInternal :
        F.secondPrefix.route.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster (Cn.leafOrder i).1) := by
      intro a x hx hxLeaf
      exact False.elim
        (Finset.disjoint_left.mp hBranchSupportDisj
          (Finset.mem_union_left _
            (hLeafSub hxLeaf))
          (F.secondPrefix.route_staysIn a hx))
    have hFull :=
      F.attached.bridge_internallyDisjointFromSet_of
        (Tsys.cluster (Cn.leafOrder i).1) hKL
        (F.firstPrefix_internal_leaf (Cn.leafOrder i).1
          (Cn.leafOrder i).2)
        hSecondInternal
    intro a x hx hxCluster
    apply hFull a.1
    · simpa [bridge', bridge] using hx
    · rw [← Cn.cluster_eq]
      simpa [P] using hxCluster
  have hBridgeInternalQ :
      ∀ j : Fin (S.selectedBelow d).card,
        bridge'.toPathPacking.InternallyDisjointFromSet (Q.cluster j) := by
    intro j
    have hLeafSub :
        Tsys.cluster (En.leafOrder j).1 ⊆ S.subtreeRegion d :=
      S.cluster_subset_subtreeRegion_of_mem
        (S.selectedBelow_subset_descendants d (En.leafOrder j).2)
    have hKL :
        Disjoint (Tsys.cluster v) (Tsys.cluster (En.leafOrder j).1) :=
      Finset.disjoint_of_subset_right hLeafSub
        (S.cluster_disjoint_subtreeRegion hd)
    have hFirstInternal :
        F.firstPrefix.route.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster (En.leafOrder j).1) := by
      intro a x hx hxLeaf
      exact False.elim
        (Finset.disjoint_left.mp hBranchSupportDisj
          (F.firstPrefix.route_staysIn a hx)
          (Finset.mem_union_left _ (hLeafSub hxLeaf)))
    have hFull :=
      F.attached.bridge_internallyDisjointFromSet_of
        (Tsys.cluster (En.leafOrder j).1) hKL
        hFirstInternal
        (F.secondPrefix_internal_leaf (En.leafOrder j).1
          (En.leafOrder j).2)
    intro a x hx hxCluster
    apply hFull a.1
    · simpa [bridge', bridge] using hx
    · rw [← En.cluster_eq]
      simpa [Q] using hxCluster
  have hPConnectorFirstPrefix :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card),
        (P.connector i hi).toPathPacking.MutuallyNodeDisjoint
          F.firstPrefix.route.toPathPacking := by
    intro i hi
    apply PathPacking.mutuallyNodeDisjoint_symm
    apply F.firstPrefix.route_disjoint_old
    · exact hPConnectorStay i hi
    · cases b₁
      · simpa [P, Cn, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          C.leftRoute_disjoint_connectors i hi
      · simpa [P, Cn, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          Cn.rightRoute_disjoint_connectors i hi
    · cases b₁
      · simpa [P, Cn, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          C.rightRoute_disjoint_connectors i hi
      · simpa [P, Cn, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          Cn.leftRoute_disjoint_connectors i hi
  have hQConnectorSecondPrefix :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        F.secondPrefix.route.toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking := by
    intro j hj
    apply F.secondPrefix.route_disjoint_old
    · exact hQConnectorStay j hj
    · cases b₂
      · have hh := En.rightRoute_disjoint_connectors j hj
        change E.leftRoute.toPathPacking.MutuallyNodeDisjoint
          (En.system.connector j hj).toPathPacking at hh
        simpa [Q, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          hh
      · have hh := En.leftRoute_disjoint_connectors j hj
        change E.leftRoute.toPathPacking.MutuallyNodeDisjoint
          (En.system.connector j hj).toPathPacking at hh
        simpa [Q, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          hh
    · cases b₂
      · have hh := En.leftRoute_disjoint_connectors j hj
        change E.rightRoute.toPathPacking.MutuallyNodeDisjoint
          (En.system.connector j hj).toPathPacking at hh
        simpa [Q, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          hh
      · have hh := En.rightRoute_disjoint_connectors j hj
        change E.rightRoute.toPathPacking.MutuallyNodeDisjoint
          (En.system.connector j hj).toPathPacking at hh
        simpa [Q, StrongPathOfSetsSystem.replaceBothOuterNails,
          StrongPathOfSetsSystem.replaceRightLast,
          StrongPathOfSetsSystem.replaceLeftFirst] using
          hh
  have hPBridge :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card),
        (P.connector i hi).toPathPacking.MutuallyNodeDisjoint
          bridge'.toPathPacking := by
    intro i hi a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxP hxBridge
    have hxFull :
        x ∈ (F.attached.bridge.path b.1).vertexSet := by
      simpa [bridge', bridge] using hxBridge
    rcases Finset.mem_union.mp
      (F.attached.bridge_path_subset b.1 hxFull) with
      hxFirst | hxRest
    · rcases F.firstPrefix.route.toPathPacking.mem_vertexSet.mp hxFirst with
        ⟨j, hxj⟩
      exact Finset.disjoint_left.mp
        (hPConnectorFirstPrefix i hi a j) hxP hxj
    · rcases Finset.mem_union.mp hxRest with hxInsideFirst | hxRest
      · rcases F.firstInside.toPathPacking.mem_vertexSet.mp hxInsideFirst with
          ⟨j, hxj⟩
        have hxK := F.firstInside_staysIn j hxj
        exact Finset.disjoint_left.mp
          (S.cluster_disjoint_subtreeRegion hc)
          hxK (hPConnectorStay i hi a hxP)
      · rcases Finset.mem_union.mp hxRest with hxInsideSecond | hxRest
        · rcases F.secondInside.toPathPacking.mem_vertexSet.mp hxInsideSecond with
            ⟨j, hxj⟩
          have hxK := F.secondInside_staysIn j hxj
          exact Finset.disjoint_left.mp
            (S.cluster_disjoint_subtreeRegion hc)
            hxK (hPConnectorStay i hi a hxP)
        · rcases Finset.mem_union.mp hxRest with hxSecond | hxK
          · rcases F.secondPrefix.route.toPathPacking.mem_vertexSet.mp hxSecond with
              ⟨j, hxj⟩
            exact Finset.disjoint_left.mp hBranchSupportDisj
                (Finset.mem_union_left _ (hPConnectorStay i hi a hxP))
                (F.secondPrefix.route_staysIn j hxj)
          · exact Finset.disjoint_left.mp
              (S.cluster_disjoint_subtreeRegion hc)
              hxK (hPConnectorStay i hi a hxP)
  have hBridgeQ :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        bridge'.toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking := by
    intro j hj a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxBridge hxQ
    have hxFull :
        x ∈ (F.attached.bridge.path a.1).vertexSet := by
      simpa [bridge', bridge] using hxBridge
    rcases Finset.mem_union.mp
      (F.attached.bridge_path_subset a.1 hxFull) with
      hxFirst | hxRest
    · rcases F.firstPrefix.route.toPathPacking.mem_vertexSet.mp hxFirst with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp hBranchSupportDisj
        (F.firstPrefix.route_staysIn k hxk)
        (Finset.mem_union_left _ (hQConnectorStay j hj b hxQ))
    · rcases Finset.mem_union.mp hxRest with hxInsideFirst | hxRest
      · rcases F.firstInside.toPathPacking.mem_vertexSet.mp hxInsideFirst with
          ⟨k, hxk⟩
        have hxK := F.firstInside_staysIn k hxk
        exact Finset.disjoint_left.mp
          (S.cluster_disjoint_subtreeRegion hd)
          hxK (hQConnectorStay j hj b hxQ)
      · rcases Finset.mem_union.mp hxRest with hxInsideSecond | hxRest
        · rcases F.secondInside.toPathPacking.mem_vertexSet.mp hxInsideSecond with
            ⟨k, hxk⟩
          have hxK := F.secondInside_staysIn k hxk
          exact Finset.disjoint_left.mp
            (S.cluster_disjoint_subtreeRegion hd)
            hxK (hQConnectorStay j hj b hxQ)
        · rcases Finset.mem_union.mp hxRest with hxSecond | hxK
          · rcases F.secondPrefix.route.toPathPacking.mem_vertexSet.mp hxSecond with
              ⟨k, hxk⟩
            exact Finset.disjoint_left.mp
              (hQConnectorSecondPrefix j hj k b) hxk hxQ
          · exact Finset.disjoint_left.mp
              (S.cluster_disjoint_subtreeRegion hd)
              hxK (hQConnectorStay j hj b hxQ)
  let J :=
    StrongPathOfSetsSystem.joinOfCompatible
      P Q bridge' hCrossCluster (by
        simpa [bridge', bridge] using hIcard)
      hBridgeInternalP hBridgeInternalQ
      hPConnectorInternalQ hQConnectorInternalP
      hCrossConnector hPBridge hBridgeQ
  have hSelectedDisj :
      Disjoint (S.selectedBelow c) (S.selectedBelow d) :=
    S.selectedBelow_children_disjoint
      ((mem_children Tsys.meta_isTree S.root v c).2 hc)
      ((mem_children Tsys.meta_isTree S.root v d).2 hd) hcd
  have hcard :
      (S.selectedBelow v).card =
        (S.selectedBelow c).card + (S.selectedBelow d).card := by
    rw [hbelow, Finset.card_union_of_disjoint hSelectedDisj]
  let Sys : StrongPathOfSetsSystem G (S.selectedBelow v).card w :=
    J.castLength hcard.symm
  let Ojoin :
      Fin ((S.selectedBelow c).card + (S.selectedBelow d).card) →
        {x : Fin m // x ∈ S.selectedBelow v} :=
    Fin.addCases
      (fun i => ⟨(Cn.leafOrder i).1, by
        rw [hbelow]
        exact Finset.mem_union_left _ (Cn.leafOrder i).2⟩)
      (fun j => ⟨(En.leafOrder j).1, by
        rw [hbelow]
        exact Finset.mem_union_right _ (En.leafOrder j).2⟩)
  let O :
      Fin (S.selectedBelow v).card →
        {x : Fin m // x ∈ S.selectedBelow v} :=
    fun i => Ojoin (Fin.cast hcard i)
  have hOjoinBijective : Function.Bijective Ojoin := by
    constructor
    · intro i j hij
      obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective i
      · obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective j
        · have hab' : Cn.leafOrder a = Cn.leafOrder b := by
            apply Subtype.ext
            simpa [Ojoin] using congrArg Subtype.val hij
          simpa [Cn.leafOrder_bijective.1 hab']
        · exfalso
          have heq :
              (Cn.leafOrder a).1 = (En.leafOrder b).1 := by
            simpa [Ojoin] using congrArg Subtype.val hij
          exact Finset.disjoint_left.mp hSelectedDisj
            (Cn.leafOrder a).2 (by simpa [heq] using (En.leafOrder b).2)
      · obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective j
        · exfalso
          have heq :
              (En.leafOrder a).1 = (Cn.leafOrder b).1 := by
            simpa [Ojoin] using congrArg Subtype.val hij
          exact Finset.disjoint_left.mp hSelectedDisj
            (Cn.leafOrder b).2 (by simpa [heq] using (En.leafOrder a).2)
        · have hab' : En.leafOrder a = En.leafOrder b := by
            apply Subtype.ext
            simpa [Ojoin] using congrArg Subtype.val hij
          simpa [En.leafOrder_bijective.1 hab']
    · intro x
      have hx : x.1 ∈ S.selectedBelow c ∪ S.selectedBelow d := by
        simpa [hbelow] using x.2
      rcases Finset.mem_union.mp hx with hxC | hxD
      · rcases Cn.leafOrder_bijective.2 ⟨x.1, hxC⟩ with ⟨i, hi⟩
        refine ⟨Fin.castAdd _ i, ?_⟩
        apply Subtype.ext
        simpa [Ojoin] using congrArg Subtype.val hi
      · rcases En.leafOrder_bijective.2 ⟨x.1, hxD⟩ with ⟨j, hj⟩
        refine ⟨Fin.natAdd _ j, ?_⟩
        apply Subtype.ext
        simpa [Ojoin] using congrArg Subtype.val hj
  have hOBijective : Function.Bijective O :=
    hOjoinBijective.comp (finCongr hcard).bijective
  have hClusterEq :
      ∀ i, Sys.cluster i = Tsys.cluster (O i).1 := by
    intro i
    let k := Fin.cast hcard i
    change J.cluster k = Tsys.cluster (Ojoin k).1
    refine Fin.addCases (motive := fun k =>
      J.cluster k = Tsys.cluster (Ojoin k).1)
      (fun a => ?_) (fun b => ?_) k
    · simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
        StrongPathOfSetsSystem.join, Ojoin, P] using Cn.cluster_eq a
    · simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
        StrongPathOfSetsSystem.join, Ojoin, Q] using En.cluster_eq b
  have hFirstOuterEq : firstOldOuter = Cn.leftReserve := by
    cases b₁ <;> rfl
  have hSecondOuterEq : secondOldOuter = En.rightReserve := by
    cases b₂ <;> rfl
  have hFirstCount :
      W / (2 * ell) ≤ firstReserve.card +
        8 * ((S.selectedBelow v).card - 1) * w := by
    apply reserve_count_after_twoChild_merge
      Cn.left_reserve_count
      (by simpa [hFirstOuterEq] using hFirstLoss)
      Cn.active.card_pos En.active.card_pos hcard
  have hSecondCount :
      W / (2 * ell) ≤ secondReserve.card +
        8 * ((S.selectedBelow v).card - 1) * w := by
    apply reserve_count_after_twoChild_merge
      En.right_reserve_count
      (by simpa [hSecondOuterEq] using hSecondLoss)
      En.active.card_pos Cn.active.card_pos (by omega)
  have hLeftSupportParent :
      S.subtreeRegion c ∪ D.leftConnector.toPathPacking.vertexSet ⊆
        S.subtreeRegion v := by
    apply Finset.union_subset
    · exact S.subtreeRegion_mono_child hc
    · intro x hx
      rcases D.leftConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      apply S.childConnector_subset_subtreeRegion hc
      simpa [hvcEq] using D.leftConnector_staysIn i hi
  have hRightSupportParent :
      S.subtreeRegion d ∪ D.rightConnector.toPathPacking.vertexSet ⊆
        S.subtreeRegion v := by
    apply Finset.union_subset
    · exact S.subtreeRegion_mono_child hd
    · intro x hx
      rcases D.rightConnector.toPathPacking.mem_vertexSet.mp hx with ⟨i, hi⟩
      apply S.childConnector_subset_subtreeRegion hd
      simpa [hvdEq] using D.rightConnector_staysIn i hi
  have hParentCluster :
      Tsys.cluster v ⊆ S.subtreeRegion v :=
    S.cluster_subset_subtreeRegion v
  have hFirstRouteStay :
      firstRoute.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i x hx
    have hx' :
        x ∈ (F.attached.retainedFirstRoute.path i.1).vertexSet := by
      simpa [firstRoute] using hx
    rcases Finset.mem_union.mp
        (F.attached.retainedFirstRoute_staysIn i.1 hx') with hxLeft | hxK
    · exact hLeftSupportParent hxLeft
    · exact hParentCluster hxK
  have hSecondRouteStay :
      secondRoute.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i x hx
    have hx' :
        x ∈ (F.attached.retainedSecondRoute.path i.1).vertexSet := by
      simpa [secondRoute] using hx
    rcases Finset.mem_union.mp
        (F.attached.retainedSecondRoute_staysIn i.1 hx') with hxRight | hxK
    · exact hRightSupportParent hxRight
    · exact hParentCluster hxK
  have hFirstRouteInternal :
      ∀ x, x ∈ S.selectedBelow v →
        firstRoute.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster x) := by
    intro x hx
    have hxUnion : x ∈ S.selectedBelow c ∪ S.selectedBelow d := by
      simpa [hbelow] using hx
    rcases Finset.mem_union.mp hxUnion with hxC | hxD
    · have hLeafSub :
          Tsys.cluster x ⊆ S.subtreeRegion c :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants c hxC)
      have hKL : Disjoint (Tsys.cluster v) (Tsys.cluster x) :=
        Finset.disjoint_of_subset_right hLeafSub
          (S.cluster_disjoint_subtreeRegion hc)
      have hFull :=
        F.attached.retainedFirstRoute_internallyDisjointFromSet_of
          (Tsys.cluster x) hKL (F.firstPrefix_internal_leaf x hxC)
      intro i z hz hzCluster
      exact hFull i.1 (by simpa [firstRoute] using hz) hzCluster
    · have hLeafSub :
          Tsys.cluster x ⊆ S.subtreeRegion d :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants d hxD)
      have hKL : Disjoint (Tsys.cluster v) (Tsys.cluster x) :=
        Finset.disjoint_of_subset_right hLeafSub
          (S.cluster_disjoint_subtreeRegion hd)
      have hOutside :
          F.firstPrefix.route.toPathPacking.InternallyDisjointFromSet
            (Tsys.cluster x) := by
        intro i z hz hzCluster
        exact False.elim
          (Finset.disjoint_left.mp hBranchSupportDisj
            (F.firstPrefix.route_staysIn i hz)
            (Finset.mem_union_left _ (hLeafSub hzCluster)))
      have hFull :=
        F.attached.retainedFirstRoute_internallyDisjointFromSet_of
          (Tsys.cluster x) hKL hOutside
      intro i z hz hzCluster
      exact hFull i.1 (by simpa [firstRoute] using hz) hzCluster
  have hSecondRouteInternal :
      ∀ x, x ∈ S.selectedBelow v →
        secondRoute.toPathPacking.InternallyDisjointFromSet
          (Tsys.cluster x) := by
    intro x hx
    have hxUnion : x ∈ S.selectedBelow c ∪ S.selectedBelow d := by
      simpa [hbelow] using hx
    rcases Finset.mem_union.mp hxUnion with hxC | hxD
    · have hLeafSub :
          Tsys.cluster x ⊆ S.subtreeRegion c :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants c hxC)
      have hKL : Disjoint (Tsys.cluster v) (Tsys.cluster x) :=
        Finset.disjoint_of_subset_right hLeafSub
          (S.cluster_disjoint_subtreeRegion hc)
      have hOutside :
          F.secondPrefix.route.toPathPacking.InternallyDisjointFromSet
            (Tsys.cluster x) := by
        intro i z hz hzCluster
        exact False.elim
          (Finset.disjoint_left.mp hBranchSupportDisj
            (Finset.mem_union_left _ (hLeafSub hzCluster))
            (F.secondPrefix.route_staysIn i hz))
      have hFull :=
        F.attached.retainedSecondRoute_internallyDisjointFromSet_of
          (Tsys.cluster x) hKL hOutside
      intro i z hz hzCluster
      exact hFull i.1 (by simpa [secondRoute] using hz) hzCluster
    · have hLeafSub :
          Tsys.cluster x ⊆ S.subtreeRegion d :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants d hxD)
      have hKL : Disjoint (Tsys.cluster v) (Tsys.cluster x) :=
        Finset.disjoint_of_subset_right hLeafSub
          (S.cluster_disjoint_subtreeRegion hd)
      have hFull :=
        F.attached.retainedSecondRoute_internallyDisjointFromSet_of
          (Tsys.cluster x) hKL (F.secondPrefix_internal_leaf x hxD)
      intro i z hz hzCluster
      exact hFull i.1 (by simpa [secondRoute] using hz) hzCluster
  have hOuterRoutes :
      firstRoute.toPathPacking.MutuallyNodeDisjoint
        secondRoute.toPathPacking := by
    intro i j
    simpa [firstRoute, secondRoute, GraphPath.NodeDisjoint] using
      F.attached.retainedFirstRoute_mutuallyNodeDisjoint_retainedSecondRoute
        i.1 j.1
  have hFirstP :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card),
        firstRoute.toPathPacking.MutuallyNodeDisjoint
          (P.connector i hi).toPathPacking := by
    intro i hi a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxRoute hxP
    have hxFull :
        x ∈ (F.attached.retainedFirstRoute.path a.1).vertexSet := by
      simpa [firstRoute] using hxRoute
    rcases Finset.mem_union.mp
        (F.attached.retainedFirstRoute_path_subset a.1 hxFull) with
      hxPrefix | hxInside
    · rcases F.firstPrefix.route.toPathPacking.mem_vertexSet.mp hxPrefix with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (GraphPath.nodeDisjoint_symm (hPConnectorFirstPrefix i hi b k))
        hxk hxP
    · rcases F.firstInside.toPathPacking.mem_vertexSet.mp hxInside with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hc)
        (F.firstInside_staysIn k hxk) (hPConnectorStay i hi b hxP)
  have hFirstQ :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        firstRoute.toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking := by
    intro j hj a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxRoute hxQ
    have hxFull :
        x ∈ (F.attached.retainedFirstRoute.path a.1).vertexSet := by
      simpa [firstRoute] using hxRoute
    rcases Finset.mem_union.mp
        (F.attached.retainedFirstRoute_path_subset a.1 hxFull) with
      hxPrefix | hxInside
    · rcases F.firstPrefix.route.toPathPacking.mem_vertexSet.mp hxPrefix with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp hBranchSupportDisj
        (F.firstPrefix.route_staysIn k hxk)
        (Finset.mem_union_left _ (hQConnectorStay j hj b hxQ))
    · rcases F.firstInside.toPathPacking.mem_vertexSet.mp hxInside with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hd)
        (F.firstInside_staysIn k hxk) (hQConnectorStay j hj b hxQ)
  have hFirstBridge :
      firstRoute.toPathPacking.MutuallyNodeDisjoint bridge'.toPathPacking := by
    intro i j
    simpa [firstRoute, bridge', bridge, GraphPath.NodeDisjoint] using
      F.attached.retainedFirstRoute_mutuallyNodeDisjoint_bridge i.1 j.1
  have hSecondP :
      ∀ (i : Fin (S.selectedBelow c).card)
        (hi : i.1 + 1 < (S.selectedBelow c).card),
        secondRoute.toPathPacking.MutuallyNodeDisjoint
          (P.connector i hi).toPathPacking := by
    intro i hi a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxRoute hxP
    have hxFull :
        x ∈ (F.attached.retainedSecondRoute.path a.1).vertexSet := by
      simpa [secondRoute] using hxRoute
    rcases Finset.mem_union.mp
        (F.attached.retainedSecondRoute_path_subset a.1 hxFull) with
      hxPrefix | hxInside
    · rcases F.secondPrefix.route.toPathPacking.mem_vertexSet.mp hxPrefix with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp hBranchSupportDisj
        (Finset.mem_union_left _ (hPConnectorStay i hi b hxP))
        (F.secondPrefix.route_staysIn k hxk)
    · rcases F.secondInside.toPathPacking.mem_vertexSet.mp hxInside with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hc)
        (F.secondInside_staysIn k hxk) (hPConnectorStay i hi b hxP)
  have hSecondQ :
      ∀ (j : Fin (S.selectedBelow d).card)
        (hj : j.1 + 1 < (S.selectedBelow d).card),
        secondRoute.toPathPacking.MutuallyNodeDisjoint
          (Q.connector j hj).toPathPacking := by
    intro j hj a b
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro x hxRoute hxQ
    have hxFull :
        x ∈ (F.attached.retainedSecondRoute.path a.1).vertexSet := by
      simpa [secondRoute] using hxRoute
    rcases Finset.mem_union.mp
        (F.attached.retainedSecondRoute_path_subset a.1 hxFull) with
      hxPrefix | hxInside
    · rcases F.secondPrefix.route.toPathPacking.mem_vertexSet.mp hxPrefix with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (hQConnectorSecondPrefix j hj k b) hxk hxQ
    · rcases F.secondInside.toPathPacking.mem_vertexSet.mp hxInside with
        ⟨k, hxk⟩
      exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hd)
        (F.secondInside_staysIn k hxk) (hQConnectorStay j hj b hxQ)
  have hSecondBridge :
      secondRoute.toPathPacking.MutuallyNodeDisjoint bridge'.toPathPacking := by
    intro i j
    simpa [secondRoute, bridge', bridge, GraphPath.NodeDisjoint] using
      F.attached.retainedSecondRoute_mutuallyNodeDisjoint_bridge i.1 j.1
  have hBridgeStayParent :
      bridge'.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i x hx
    have hxFull : x ∈ (F.attached.bridge.path i.1).vertexSet := by
      simpa [bridge', bridge] using hx
    rcases Finset.mem_union.mp
        (F.attached.bridge_staysIn i.1 hxFull) with hxLeft | hxRest
    · exact hLeftSupportParent hxLeft
    · rcases Finset.mem_union.mp hxRest with hxK | hxRight
      · exact hParentCluster hxK
      · exact hRightSupportParent hxRight
  have hJConnectorStay :
      ∀ (i : Fin ((S.selectedBelow c).card +
          (S.selectedBelow d).card))
        (hi : i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card),
        (J.connector i hi).toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i hi
    simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join] using
      StrongPathOfSetsSystem.joinConnector_staysIn P Q bridge'
        (fun i hi a x hx =>
          S.subtreeRegion_mono_child hc (hPConnectorStay i hi a hx))
        hBridgeStayParent
        (fun j hj a x hx =>
          S.subtreeRegion_mono_child hd (hQConnectorStay j hj a hx))
        i hi
  have hFirstJ :
      ∀ (i : Fin ((S.selectedBelow c).card +
          (S.selectedBelow d).card))
        (hi : i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card),
        firstRoute.toPathPacking.MutuallyNodeDisjoint
          (J.connector i hi).toPathPacking := by
    intro i hi
    simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join] using
      StrongPathOfSetsSystem.mutuallyNodeDisjoint_joinConnector
        firstRoute.toPathPacking P Q bridge'
        hFirstP hFirstBridge hFirstQ i hi
  have hSecondJ :
      ∀ (i : Fin ((S.selectedBelow c).card +
          (S.selectedBelow d).card))
        (hi : i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card),
        secondRoute.toPathPacking.MutuallyNodeDisjoint
          (J.connector i hi).toPathPacking := by
    intro i hi
    simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join] using
      StrongPathOfSetsSystem.mutuallyNodeDisjoint_joinConnector
        secondRoute.toPathPacking P Q bridge'
        hSecondP hSecondBridge hSecondQ i hi
  have hFirstReserveBridge :
      Disjoint firstReserve bridgeLeft := by
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        F.attached.retainedFirstRoute_mutuallyNodeDisjoint_bridge).mono
        (Finset.inter_subset_left.trans
          (PerfectPathPacking.left_subset_vertexSet
            F.attached.retainedFirstRoute))
        (F.attached.bridge.sourceSet_subset_left I |>.trans
          (PerfectPathPacking.left_subset_vertexSet F.attached.bridge))
  have hBridgeSecondReserve :
      Disjoint bridgeRight secondReserve := by
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (PathPacking.mutuallyNodeDisjoint_symm
          F.attached.retainedSecondRoute_mutuallyNodeDisjoint_bridge)).mono
        (F.attached.bridge.targetSet_subset_right I |>.trans
          (PerfectPathPacking.right_subset_vertexSet F.attached.bridge))
        (Finset.inter_subset_left.trans
          (PerfectPathPacking.left_subset_vertexSet
            F.attached.retainedSecondRoute))
  have hJfirst :
      J.toPathOfSetsSystem.firstIndex =
        Fin.castAdd (S.selectedBelow d).card
          P.toPathOfSetsSystem.firstIndex := by
    apply Fin.ext
    rfl
  have hJlast :
      J.toPathOfSetsSystem.lastIndex =
        Fin.natAdd (S.selectedBelow c).card
          Q.toPathOfSetsSystem.lastIndex := by
    apply Fin.ext
    have hQpos : 0 < (S.selectedBelow d).card :=
      En.active.card_pos
    simp only [PathOfSetsSystem.lastIndex_val, Fin.val_natAdd]
    omega
  have hOrderFirst :
      (O Sys.toPathOfSetsSystem.firstIndex).1 =
        (Cn.leafOrder Cn.system.toPathOfSetsSystem.firstIndex).1 := by
    change
      (Ojoin (Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex)).1 =
        (Cn.leafOrder Cn.system.toPathOfSetsSystem.firstIndex).1
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex =
          J.toPathOfSetsSystem.firstIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_firstIndex_cast J hcard.symm]
    rw [hJfirst]
    simp [Ojoin]
    apply congrArg Cn.leafOrder
    apply Fin.ext
    rfl
  have hOrderLast :
      (O Sys.toPathOfSetsSystem.lastIndex).1 =
        (En.leafOrder En.system.toPathOfSetsSystem.lastIndex).1 := by
    change
      (Ojoin (Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex)).1 =
        (En.leafOrder En.system.toPathOfSetsSystem.lastIndex).1
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex =
          J.toPathOfSetsSystem.lastIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_lastIndex_cast J hcard.symm]
    rw [hJlast]
    simp [Ojoin]
    apply congrArg En.leafOrder
    apply Fin.ext
    rfl
  have hSysLeftFirst :
      Sys.left Sys.toPathOfSetsSystem.firstIndex = firstNails := by
    change
      J.left (Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex) =
        firstNails
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex =
          J.toPathOfSetsSystem.firstIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_firstIndex_cast J hcard.symm]
    rw [hJfirst]
    simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join] using
      StrongPathOfSetsSystem.replaceBothOuterNails_left_first
        Cn.system firstNails bridgeLeft _ _ _ _ _ _ _ _ _ _ _ _
  have hSysRightLast :
      Sys.right Sys.toPathOfSetsSystem.lastIndex = secondNails := by
    change
      J.right (Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex) =
        secondNails
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex =
          J.toPathOfSetsSystem.lastIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_lastIndex_cast J hcard.symm]
    rw [hJlast]
    simpa [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join] using
      StrongPathOfSetsSystem.replaceBothOuterNails_right_last
        En.system bridgeRight secondNails _ _ _ _ _ _ _ _ _ _ _ _
  have hSysRightFirst_singleton
      (hsingle :
        Cn.system.toPathOfSetsSystem.firstIndex =
          Cn.system.toPathOfSetsSystem.lastIndex) :
      Sys.right Sys.toPathOfSetsSystem.firstIndex = bridgeLeft := by
    change
      J.right (Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex) =
        bridgeLeft
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex =
          J.toPathOfSetsSystem.firstIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_firstIndex_cast J hcard.symm]
    rw [hJfirst]
    simp [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join]
    have hPsingle :
        P.toPathOfSetsSystem.firstIndex =
          P.toPathOfSetsSystem.lastIndex := by
      apply Fin.ext
      simpa [P] using congrArg Fin.val hsingle
    rw [hPsingle]
    exact hPright
  have hSysRightFirst_of_ne
      (hsingle :
        Cn.system.toPathOfSetsSystem.firstIndex ≠
          Cn.system.toPathOfSetsSystem.lastIndex) :
      Sys.right Sys.toPathOfSetsSystem.firstIndex =
        Cn.system.right Cn.system.toPathOfSetsSystem.firstIndex := by
    change
      J.right (Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex) =
        Cn.system.right Cn.system.toPathOfSetsSystem.firstIndex
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.firstIndex =
          J.toPathOfSetsSystem.firstIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_firstIndex_cast J hcard.symm]
    rw [hJfirst]
    simp [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join]
    have hPfirst :
        P.toPathOfSetsSystem.firstIndex =
          Cn.system.toPathOfSetsSystem.firstIndex := by
      apply Fin.ext
      rfl
    rw [hPfirst]
    simp [P,
      StrongPathOfSetsSystem.replaceBothOuterNails,
      StrongPathOfSetsSystem.replaceRightLast,
      StrongPathOfSetsSystem.replaceLeftFirst, hsingle]
    intro hbad
    exact False.elim (hsingle (by
      calc
        Cn.system.toPathOfSetsSystem.firstIndex =
            (Cn.system.replaceLeftFirst firstNails
              hFirstNailsCluster hFirstNailsOld hFirstNailsCard
              hFirstNailsWL hFirstNailsLinked
              ).toPathOfSetsSystem.lastIndex := hbad
        _ = Cn.system.toPathOfSetsSystem.lastIndex := by
          apply Fin.ext
          rfl))
  have hSysLeftLast_singleton
      (hsingle :
        En.system.toPathOfSetsSystem.firstIndex =
          En.system.toPathOfSetsSystem.lastIndex) :
      Sys.left Sys.toPathOfSetsSystem.lastIndex = bridgeRight := by
    change
      J.left (Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex) =
        bridgeRight
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex =
          J.toPathOfSetsSystem.lastIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_lastIndex_cast J hcard.symm]
    rw [hJlast]
    simp [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join]
    have hQsingle :
        Q.toPathOfSetsSystem.lastIndex =
          Q.toPathOfSetsSystem.firstIndex := by
      apply Fin.ext
      simpa [Q] using congrArg Fin.val hsingle.symm
    rw [hQsingle]
    exact hQleft
  have hSysLeftLast_of_ne
      (hsingle :
        En.system.toPathOfSetsSystem.firstIndex ≠
          En.system.toPathOfSetsSystem.lastIndex) :
      Sys.left Sys.toPathOfSetsSystem.lastIndex =
        En.system.left En.system.toPathOfSetsSystem.lastIndex := by
    change
      J.left (Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex) =
        En.system.left En.system.toPathOfSetsSystem.lastIndex
    rw [show
      Fin.cast hcard Sys.toPathOfSetsSystem.lastIndex =
          J.toPathOfSetsSystem.lastIndex by
        simpa [Sys] using
          StrongPathOfSetsSystem.castLength_lastIndex_cast J hcard.symm]
    rw [hJlast]
    simp [J, StrongPathOfSetsSystem.joinOfCompatible,
      StrongPathOfSetsSystem.join]
    have hQlast :
        Q.toPathOfSetsSystem.lastIndex =
          En.system.toPathOfSetsSystem.lastIndex := by
      apply Fin.ext
      rfl
    rw [hQlast]
    simp [Q,
      StrongPathOfSetsSystem.replaceBothOuterNails,
      StrongPathOfSetsSystem.replaceRightLast,
      StrongPathOfSetsSystem.replaceLeftFirst, hsingle]
    intro hbad
    exact False.elim (hsingle hbad.symm)
  exact ⟨{
    active := by
      rw [hbelow]
      exact Cn.active.mono (Finset.subset_union_left)
    system := Sys
    leafOrder := O
    leafOrder_bijective := hOBijective
    cluster_eq := hClusterEq
    leftReserve := firstReserve
    rightReserve := secondReserve
    leftAmbient := Cn.leftAmbient
    rightAmbient := En.rightAmbient
    leftAnchor := firstAnchor
    rightAnchor := secondAnchor
    leftRoute := firstRoute
    rightRoute := secondRoute
    leftAnchor_subset := hFirstAnchorA
    rightAnchor_subset := hSecondAnchorA
    leftAmbient_subset_leaf := by
      rw [hOrderFirst]
      exact Cn.leftAmbient_subset_leaf
    rightAmbient_subset_leaf := by
      rw [hOrderLast]
      exact En.rightAmbient_subset_leaf
    leftAmbient_nodeWellLinked := by
      rw [hOrderFirst]
      exact Cn.leftAmbient_nodeWellLinked
    rightAmbient_nodeWellLinked := by
      rw [hOrderLast]
      exact En.rightAmbient_nodeWellLinked
    outerAmbient_eq_of_singleton := by
      intro h
      have hv := congrArg Fin.val h
      have hcpos := Cn.active.card_pos
      have hdpos := En.active.card_pos
      simp [Sys] at hv
      omega
    outerAmbient_linked_of_singleton := by
      intro h
      have hv := congrArg Fin.val h
      have hcpos := Cn.active.card_pos
      have hdpos := En.active.card_pos
      simp [Sys] at hv
      omega
    leftReserve_subset_ambient := by
      exact Finset.inter_subset_right.trans
        (by simpa [hFirstOuterEq] using Cn.leftReserve_subset_ambient)
    rightReserve_subset_ambient := by
      exact Finset.inter_subset_right.trans
        (by simpa [hSecondOuterEq] using En.rightReserve_subset_ambient)
    leftReserve_disjoint_firstRight := by
      by_cases hsingle :
          Cn.system.toPathOfSetsSystem.firstIndex =
            Cn.system.toPathOfSetsSystem.lastIndex
      · rw [hSysRightFirst_singleton hsingle]
        exact hFirstReserveBridge
      · apply Finset.disjoint_of_subset_left
          (Finset.inter_subset_right.trans (by
            rw [hFirstOuterEq]))
        rw [hSysRightFirst_of_ne hsingle]
        exact Cn.leftReserve_disjoint_firstRight
    rightReserve_disjoint_lastLeft := by
      by_cases hsingle :
          En.system.toPathOfSetsSystem.firstIndex =
            En.system.toPathOfSetsSystem.lastIndex
      · rw [hSysLeftLast_singleton hsingle]
        exact hBridgeSecondReserve
      · apply Finset.disjoint_of_subset_right
          (Finset.inter_subset_right.trans (by
            rw [hSecondOuterEq]))
        rw [hSysLeftLast_of_ne hsingle]
        exact En.rightReserve_disjoint_lastLeft
    first_left_subset_ambient := by
      rw [hSysLeftFirst]
      exact hFirstNailsAmbient
    first_right_subset_ambient := by
      by_cases hsingle :
          Cn.system.toPathOfSetsSystem.firstIndex =
            Cn.system.toPathOfSetsSystem.lastIndex
      · have hbridge :
            bridgeLeft ⊆ Cn.leftAmbient := by
          simpa [Cn.outerAmbient_eq_of_singleton hsingle] using
            hBridgeLeftAmbient
        rw [hSysRightFirst_singleton hsingle]
        exact hbridge
      · rw [hSysRightFirst_of_ne hsingle]
        exact Cn.first_right_subset_ambient
    last_left_subset_ambient := by
      by_cases hsingle :
          En.system.toPathOfSetsSystem.firstIndex =
            En.system.toPathOfSetsSystem.lastIndex
      · have hbridge :
            bridgeRight ⊆ En.rightAmbient := by
          simpa [En.outerAmbient_eq_of_singleton hsingle] using
            hBridgeRightAmbient
        rw [hSysLeftLast_singleton hsingle]
        exact hbridge
      · rw [hSysLeftLast_of_ne hsingle]
        exact En.last_left_subset_ambient
    last_right_subset_ambient := by
      rw [hSysRightLast]
      exact hSecondNailsAmbient
    leftReserve_subset_leaf := by
      apply Finset.inter_subset_right.trans
      rw [hOrderFirst]
      simpa [hFirstOuterEq] using Cn.leftReserve_subset_leaf
    rightReserve_subset_leaf := by
      apply Finset.inter_subset_right.trans
      rw [hOrderLast]
      simpa [hSecondOuterEq] using En.rightReserve_subset_leaf
    left_nails_subset := by
      rw [hSysLeftFirst]
      exact hFirstNails
    right_nails_subset := by
      rw [hSysRightLast]
      exact hSecondNails
    left_reserve_count := hFirstCount
    right_reserve_count := hSecondCount
    leftRoute_staysIn := hFirstRouteStay
    rightRoute_staysIn := hSecondRouteStay
    leftRoute_internallyDisjoint_leafCluster := hFirstRouteInternal
    rightRoute_internallyDisjoint_leafCluster := hSecondRouteInternal
    leftRoute_trivial_of_root_selected := by
      intro hv
      have hcmem :
          c ∈ children Tsys.meta_isTree S.root v :=
        (mem_children Tsys.meta_isTree S.root v c).2 hc
      exact False.elim (by
        rw [S.children_eq_empty_of_mem_leaves hv] at hcmem
        simpa using hcmem)
    rightRoute_trivial_of_root_selected := by
      intro hv
      have hdmem :
          d ∈ children Tsys.meta_isTree S.root v :=
        (mem_children Tsys.meta_isTree S.root v d).2 hd
      exact False.elim (by
        rw [S.children_eq_empty_of_mem_leaves hv] at hdmem
        simpa using hdmem)
    outerRoutes_disjoint := hOuterRoutes
    connectors_stayIn := by
      intro i hi
      let k := Fin.cast hcard i
      have hk :
          k.1 + 1 <
            (S.selectedBelow c).card + (S.selectedBelow d).card := by
        change i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card
        rw [← hcard]
        exact hi
      simpa [Sys] using hJConnectorStay k hk
    leftRoute_disjoint_connectors := by
      intro i hi
      let k := Fin.cast hcard i
      have hk :
          k.1 + 1 <
            (S.selectedBelow c).card + (S.selectedBelow d).card := by
        change i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card
        rw [← hcard]
        exact hi
      simpa [Sys] using hFirstJ k hk
    rightRoute_disjoint_connectors := by
      intro i hi
      let k := Fin.cast hcard i
      have hk :
          k.1 + 1 <
            (S.selectedBelow c).card + (S.selectedBelow d).card := by
        change i.1 + 1 <
          (S.selectedBelow c).card + (S.selectedBelow d).card
        rw [← hcard]
        exact hi
      simpa [Sys] using hSecondJ k hk }⟩

end TwoChildAssembly

section RecursiveAssembly

variable {m W ell w : ℕ}
variable {Tsys : StrongTreeOfSetsSystem G m W}

/-- The full bottom-up DFS construction below a nonroot active meta-vertex.
The induction follows the same active-child decomposition as Theorem 4.7;
at leaves it splits the routed leaf target into the two half-width reserves,
at degree-two vertices it transports the exposed routes, and at branching
vertices it applies the two-child merge proved above. -/
theorem exists_theorem46_subtreeRoutedDfsState
    (S : Theorem46LeafExtractionSetup Tsys ell)
    (hell : 0 < ell)
    (hw : 0 < w)
    (hW : 16 * w * ell ^ 2 + 1 < W)
    {v : Fin m} (hvroot : v ≠ S.root)
    (hactive : (S.selectedBelow v).Nonempty)
    {A : Finset V}
    (hA :
      A ⊆ Tsys.interface v
        (parent Tsys.meta_isTree S.root v)
        (parent_adj Tsys.meta_isTree S.root hvroot).symm)
    (hAcard :
      A.card = (S.selectedBelow v).card * (W / ell)) :
    Nonempty (Theorem46RoutedDfsState (w := w) S v A) := by
  classical
  have hquota : ell * (W / ell) ≤ W :=
    Nat.mul_div_le W ell
  have hwHalf : w ≤ W / (2 * ell) :=
    theorem46_width_le_halfWidth_reserve hell hW
  induction hn : (descendants Tsys.meta_isTree S.root v).card
      using Nat.strong_induction_on generalizing v A with
  | h n ih =>
      subst hn
      by_cases hvleaf : v ∈ S.leaves
      · let E :=
          Classical.choice
            (exists_theorem47_leafSubtreeRoutingData (q := W / ell) S hvleaf
              (hA.trans (Tsys.interface_subset_cluster
                v (parent Tsys.meta_isTree S.root v)
                (parent_adj Tsys.meta_isTree S.root hvroot).symm))
              (NodeWellLinkedIn.mono_terminals
                (Tsys.interface_nodeWellLinked
                  v (parent Tsys.meta_isTree S.root v)
                  (parent_adj Tsys.meta_isTree S.root hvroot).symm)
                hA)
              (by
                have hAcard' := hAcard
                rw [S.selectedBelow_eq_singleton_of_mem_leaves hvleaf]
                  at hAcard'
                simpa using hAcard'))
        have hvbelow : v ∈ S.selectedBelow v := by
          simp [S.selectedBelow_eq_singleton_of_mem_leaves hvleaf]
        have htarget :
            (E.leafTarget v).card = W / ell :=
          E.leafTarget_card v hvbelow
        obtain ⟨L, R, hL, hR, hLR, hLcard, hRcard⟩ :=
          exists_two_leaf_reserves (E.leafTarget v) htarget
        exact exists_theorem46RoutedDfsState_leaf
          S E hvleaf L R hL hR hLR hLcard hRcard hw hwHalf
      · have hbelowActive :
          S.selectedBelow v =
            (S.activeChildren v).biUnion S.selectedBelow :=
          S.selectedBelow_eq_biUnion_activeChildren hvleaf
        have hactiveChildren : (S.activeChildren v).Nonempty := by
          rcases hactive with ⟨x, hx⟩
          rw [hbelowActive] at hx
          rcases Finset.mem_biUnion.mp hx with ⟨c, hc, _⟩
          exact ⟨c, hc⟩
        have hactiveCardPos : 0 < (S.activeChildren v).card :=
          hactiveChildren.card_pos
        have hactiveCardLe : (S.activeChildren v).card ≤ 2 :=
          S.activeChildren_card_le_two hvroot
        have hAle : A.card ≤ W := by
          have hbelowCard :
              (S.selectedBelow v).card ≤ ell := by
            have :=
              Finset.card_le_card (S.selectedBelow_subset_leaves v)
            simpa [S.leaves_card] using this
          calc
            A.card =
                (S.selectedBelow v).card * (W / ell) := hAcard
            _ ≤ ell * (W / ell) :=
              Nat.mul_le_mul_right (W / ell) hbelowCard
            _ ≤ W := hquota
        by_cases hcardOne : (S.activeChildren v).card = 1
        · rcases Finset.card_eq_one.mp hcardOne with ⟨c, hcEq⟩
          have hcActive : c ∈ S.activeChildren v := by simp [hcEq]
          have hcMem :
              c ∈ children Tsys.meta_isTree S.root v :=
            (S.mem_activeChildren v c).1 hcActive |>.1
          have hc :
              IsChild Tsys.meta_isTree S.root v c :=
            (mem_children Tsys.meta_isTree S.root v c).1 hcMem
          have hcBelow : (S.selectedBelow c).Nonempty :=
            (S.mem_activeChildren v c).1 hcActive |>.2
          have hbelow : S.selectedBelow v = S.selectedBelow c := by
            rw [hbelowActive, hcEq]
            simp
          have hpc :
              parent Tsys.meta_isTree S.root v ≠ c := by
            intro h
            subst c
            exact S.parent_not_mem_children hvroot hcMem
          let hpv :=
            (parent_adj Tsys.meta_isTree S.root hvroot).symm
          let hvc := S.adj_child hc
          let D :=
            Classical.choice
              (exists_theorem47_oneChildTransitionData
                (T := Tsys) hpv hvc hpc hA hAle)
          have hDescSubset :
              descendants Tsys.meta_isTree S.root c ⊆
                descendants Tsys.meta_isTree S.root v := by
            intro x hx
            exact S.mem_descendants_of_childSubtree hc hx
          have hvNotChild :
              v ∉ descendants Tsys.meta_isTree S.root c := by
            simpa [childSubtree] using
              parent_not_mem_childSubtree Tsys.meta_isTree S.root
                S.parentDistanceDecreases hc
          have hDescStrict :
              descendants Tsys.meta_isTree S.root c ⊂
                descendants Tsys.meta_isTree S.root v := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hDescSubset, ?_⟩
            intro heq
            exact hvNotChild (by
              rw [heq]
              exact self_mem_descendants
                Tsys.meta_isTree S.root v)
          have hDescCard :
              (descendants Tsys.meta_isTree S.root c).card <
                (descendants Tsys.meta_isTree S.root v).card :=
            Finset.card_lt_card hDescStrict
          have hDcanonical :
              D.childIncoming ⊆
                Tsys.interface c
                  (parent Tsys.meta_isTree S.root c)
                  (parent_adj Tsys.meta_isTree S.root hc.1).symm := by
            simpa [hc.2, hvc] using D.childIncoming_subset
          have hDcard :
              D.childIncoming.card =
                (S.selectedBelow c).card * (W / ell) := by
            rw [D.childIncoming_card, hAcard, hbelow]
          let C :=
            Classical.choice
              (ih _ hDescCard hc.1 hcBelow
                hDcanonical hDcard rfl)
          exact C.liftOneChild S hc hbelow
            (hA.trans (Tsys.interface_subset_cluster
              v (parent Tsys.meta_isTree S.root v)
              (parent_adj Tsys.meta_isTree S.root hvroot).symm)) D
        · have hcardTwo : (S.activeChildren v).card = 2 := by
            omega
          rcases Finset.card_eq_two.mp hcardTwo with
            ⟨c, d, hcd, hchildrenEq⟩
          have hcActive : c ∈ S.activeChildren v := by
            simp [hchildrenEq]
          have hdActive : d ∈ S.activeChildren v := by
            simp [hchildrenEq]
          have hcMem :
              c ∈ children Tsys.meta_isTree S.root v :=
            (S.mem_activeChildren v c).1 hcActive |>.1
          have hdMem :
              d ∈ children Tsys.meta_isTree S.root v :=
            (S.mem_activeChildren v d).1 hdActive |>.1
          have hc :
              IsChild Tsys.meta_isTree S.root v c :=
            (mem_children Tsys.meta_isTree S.root v c).1 hcMem
          have hd :
              IsChild Tsys.meta_isTree S.root v d :=
            (mem_children Tsys.meta_isTree S.root v d).1 hdMem
          have hcBelow : (S.selectedBelow c).Nonempty :=
            (S.mem_activeChildren v c).1 hcActive |>.2
          have hdBelow : (S.selectedBelow d).Nonempty :=
            (S.mem_activeChildren v d).1 hdActive |>.2
          have hbelow :
              S.selectedBelow v =
                S.selectedBelow c ∪ S.selectedBelow d := by
            rw [hbelowActive, hchildrenEq]
            simp [Finset.union_comm]
          have hpNeC :
              parent Tsys.meta_isTree S.root v ≠ c := by
            intro h
            subst c
            exact S.parent_not_mem_children hvroot hcMem
          have hpNeD :
              parent Tsys.meta_isTree S.root v ≠ d := by
            intro h
            subst d
            exact S.parent_not_mem_children hvroot hdMem
          let k₁ := (S.selectedBelow c).card * (W / ell)
          let k₂ := (S.selectedBelow d).card * (W / ell)
          have hQuota :
              A.card = k₁ + k₂ := by
            rw [hAcard, hbelow,
              Finset.card_union_of_disjoint
                (S.selectedBelow_children_disjoint hcMem hdMem hcd)]
            simp [k₁, k₂, Nat.add_mul]
          let hpv :=
            (parent_adj Tsys.meta_isTree S.root hvroot).symm
          let hvc := S.adj_child hc
          let hvd := S.adj_child hd
          let D :=
            Classical.choice
              (exists_theorem47_twoChildTransitionData
                (T := Tsys) hpv hvc hvd hpNeC hpNeD hcd
                hA hQuota hAle)
          have childCardLt :
              ∀ {x : Fin m},
                IsChild Tsys.meta_isTree S.root v x →
                (descendants Tsys.meta_isTree S.root x).card <
                  (descendants Tsys.meta_isTree S.root v).card := by
            intro x hx
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨?_, ?_⟩
            · intro y hy
              exact S.mem_descendants_of_childSubtree hx hy
            · intro heq
              have hvNot :
                  v ∉ descendants Tsys.meta_isTree S.root x := by
                simpa [childSubtree] using
                  parent_not_mem_childSubtree
                    Tsys.meta_isTree S.root
                    S.parentDistanceDecreases hx
              exact hvNot (by
                rw [heq]
                exact self_mem_descendants
                  Tsys.meta_isTree S.root v)
          have hLeftCanonical :
              D.leftIncoming ⊆
                Tsys.interface c
                  (parent Tsys.meta_isTree S.root c)
                  (parent_adj Tsys.meta_isTree S.root hc.1).symm := by
            simpa [hc.2, hvc] using D.leftIncoming_subset
          have hRightCanonical :
              D.rightIncoming ⊆
                Tsys.interface d
                  (parent Tsys.meta_isTree S.root d)
                  (parent_adj Tsys.meta_isTree S.root hd.1).symm := by
            simpa [hd.2, hvd] using D.rightIncoming_subset
          have hLeftCard :
              D.leftIncoming.card =
                (S.selectedBelow c).card * (W / ell) := by
            simpa [k₁] using D.leftIncoming_card
          have hRightCard :
              D.rightIncoming.card =
                (S.selectedBelow d).card * (W / ell) := by
            simpa [k₂] using D.rightIncoming_card
          let C :=
            Classical.choice
              (ih _ (childCardLt hc) hc.1 hcBelow
                hLeftCanonical hLeftCard rfl)
          let E :=
            Classical.choice
              (ih _ (childCardLt hd) hd.1 hdBelow
                hRightCanonical hRightCard rfl)
          exact exists_theorem46RoutedDfsState_twoChildren
            S hc hd hcd hbelow hA D C E hell hW

/-- Root the DFS construction at the distinguished meta-tree leaf.  The
root--child connector supplies the initial Step 1 tranche, and the unique
active child is then lifted through the same one-child transition used inside
the recursion. -/
theorem exists_theorem46_rootRoutedDfsState
    (S : Theorem46LeafExtractionSetup Tsys ell)
    (hell : 0 < ell)
    (hw : 0 < w)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    ∃ A : Finset V,
      A ⊆ Tsys.interface S.root S.child S.root_child_adj ∧
      Nonempty (Theorem46RoutedDfsState (w := w) S S.root A) := by
  classical
  let q := W / ell
  have hquota : ell * q ≤ W := by
    dsimp [q]
    exact Nat.mul_div_le W ell
  have hAcardLe :
      ell * q ≤
        (Tsys.interface S.root S.child S.root_child_adj).card := by
    simpa [Tsys.interface_card S.root S.child S.root_child_adj] using
      hquota
  rcases Finset.exists_subset_card_eq hAcardLe with
    ⟨A, hA, hAcard⟩
  let C := Tsys.connector S.root S.child S.root_child_adj
  let R := C.restrictSourceSet A hA
  let B := C.targetSet (C.sourceIndexSetOfSubset A)
  have hBsub :
      B ⊆ Tsys.interface S.child S.root S.root_child_adj.symm :=
    C.targetSet_subset_right _
  have hBcard : B.card = ell * q := by
    calc
      B.card = R.card := R.card_eq_right_card.symm
      _ = A.card := by simp [R]
      _ = ell * q := hAcard
  have hc :
      IsChild Tsys.meta_isTree S.root S.root S.child := by
    exact (mem_children Tsys.meta_isTree S.root S.root S.child).1
      (by simp [S.children_root_eq_singleton])
  have hBcanonical :
      B ⊆
        Tsys.interface S.child
          (parent Tsys.meta_isTree S.root S.child)
          (parent_adj Tsys.meta_isTree S.root hc.1).symm := by
    simpa [hc.2] using hBsub
  have hchildActive :
      (S.selectedBelow S.child).Nonempty := by
    rw [S.selectedBelow_child_eq_leaves]
    exact Finset.card_pos.mp (by simpa [S.leaves_card] using hell)
  have hBcardCanonical :
      B.card =
        (S.selectedBelow S.child).card * (W / ell) := by
    simpa [q, S.selectedBelow_child_card] using hBcard
  let E :=
    Classical.choice
      (exists_theorem46_subtreeRoutedDfsState
        S hell hw hW hc.1 hchildActive hBcanonical hBcardCanonical)
  let D :
      Theorem47OneChildTransitionData Tsys
        S.root_child_adj S.root_child_adj A := {
    childIncoming := B
    childIncoming_subset := hBsub
    childIncoming_card := by
      calc
        B.card = A.card := by rw [hBcard, hAcard]
        _ = A.card := rfl
    transition := R
    transition_card := by simp [R]
    transition_staysIn := by
      intro i x hx
      exact Finset.mem_union_right _
        (C.restrictSourceSet_staysIn_vertexSet A hA i hx)
    transition_internallyDisjoint_child :=
      C.restrictSourceSet_internallyDisjointFromSet A hA
        (Tsys.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj S.child) }
  have hbelow :
      S.selectedBelow S.root = S.selectedBelow S.child := by
    rw [S.selectedBelow_root_eq_leaves,
      S.selectedBelow_child_eq_leaves]
  have hAcluster : A ⊆ Tsys.cluster S.root :=
    hA.trans
      (Tsys.interface_subset_cluster
        S.root S.child S.root_child_adj)
  exact ⟨A, hA, E.liftOneChild S hc hbelow hAcluster D⟩

/-- The source-faithful many-leaves branch of Chekuri--Chuzhoy journal
Theorem 4.6. -/
theorem strongPathOfSetsFromLeafyStrongTreeOfSets_proved :
    StrongPathOfSetsFromLeafyStrongTreeOfSets.{u} := by
  intro V _ _ G m W ell w T hell hw _ hW hleaves
  let S :=
    Classical.choice
      (exists_theorem46_leafExtractionSetup T hleaves)
  have hellPos : 0 < ell := lt_trans Nat.zero_lt_one hell
  have hwPos : 0 < w := lt_trans Nat.zero_lt_one hw
  obtain ⟨A, _, E⟩ :=
    exists_theorem46_rootRoutedDfsState S hellPos hwPos hW
  let C := Classical.choice E
  have hlength : (S.selectedBelow S.root).card = ell := by
    rw [S.selectedBelow_root_eq_leaves, S.leaves_card]
  exact ⟨C.system.castLength hlength⟩

end RecursiveAssembly

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
