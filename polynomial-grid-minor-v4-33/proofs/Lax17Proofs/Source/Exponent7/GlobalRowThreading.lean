import Lax17Proofs.Source.ChekuriChuzhoyStitchedRows

namespace Lax17Proofs

/-!
# Global row threading through an arbitrary strong path-of-sets system

The Appendix C stitching proof is specialized to `2 * g * (g - 1)` clusters.
Here the same concatenation invariant is proved for an arbitrary number of
clusters.

For every cluster we choose a full-width perfect left-to-right linkage.  A
`GlobalRowPrefix` concatenates those local linkages and the path-of-sets
connectors up to one cluster.  Besides the resulting perfect packing, it
records:

* the local path occurring in every global row;
* exact containment of the global trace in that local path; and
* the order in which cluster traces occur.
-/

namespace SimpleGraph
namespace Exponent7

open ChekuriChuzhoy

universe u

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell w : ℕ}

namespace StrongPathOfSetsSystem

/-- A fixed full-width perfect linkage through one cluster. -/
noncomputable def clusterLinkage
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    PerfectPathPacking G (P.left i) (P.right i) :=
  Classical.choose (P.exists_left_right_perfect_linkage i)

@[simp] theorem clusterLinkage_card
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    (StrongPathOfSetsSystem.clusterLinkage P i).card = w :=
  (Classical.choose_spec (P.exists_left_right_perfect_linkage i)).1

theorem clusterLinkage_staysIn
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking.StaysIn
      (P.cluster i) :=
  (Classical.choose_spec (P.exists_left_right_perfect_linkage i)).2

/-- The initial left terminals are disjoint from every later cluster. -/
theorem firstLeft_disjoint_cluster
    (P : StrongPathOfSetsSystem G ell w) {i : Fin ell}
    (hi : 0 < i.1) :
    Disjoint (P.left P.firstIndex) (P.cluster i) := by
  apply Disjoint.mono_left (P.left_subset_cluster P.firstIndex)
  apply P.cluster_disjoint
  intro h
  have hval := congrArg Fin.val h
  simpa [PathOfSetsSystem.firstIndex] using hi.ne' (Eq.symm hval)

/-- A current connector is internally disjoint from the whole path-of-sets
prefix through its source cluster. -/
theorem connector_internallyDisjoint_prefix
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    (P.connector i hi).toPathPacking.InternallyDisjointFromSet
      (stitchingPrefixRegion P i) := by
  classical
  intro a v hvPath hvPrefix
  rcases Finset.mem_union.mp hvPrefix with hvStrict | hvCurrent
  · rcases Finset.mem_union.mp hvStrict with hvClusters | hvConnectors
    · rcases Finset.mem_biUnion.mp hvClusters with ⟨j, _hj, hvCluster⟩
      exact P.connector_internally_disjoint_clusters i hi
        (earlierPathOfSetsIndex i j) a hvPath hvCluster
    · rcases Finset.mem_biUnion.mp hvConnectors with
        ⟨j, _hj, hvConnector⟩
      have hne : i ≠ earlierPathOfSetsIndex i j := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      have hdisj :=
        PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint hi
            (earlierPathOfSetsIndex_gap i j) hne)
      exact False.elim
        (Finset.disjoint_left.mp hdisj
          ((P.connector i hi).toPathPacking.path_vertexSet_subset_vertexSet
            a hvPath)
          hvConnector)
  · exact P.connector_internally_disjoint_clusters i hi i a hvPath hvCurrent

/-- The next left nail set is disjoint from the prefix through the current
cluster. -/
theorem nextLeft_disjoint_prefix
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    Disjoint (P.left ⟨i.1 + 1, hi⟩) (stitchingPrefixRegion P i) := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvPrefix
  exact Finset.disjoint_left.mp
    (stitchingPrefixRegion_disjoint_cluster_of_lt P (by simp))
    hvPrefix (P.left_subset_cluster ⟨i.1 + 1, hi⟩ hvLeft)

/-- The current right nail set is disjoint from the next cluster. -/
theorem right_disjoint_nextCluster
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    Disjoint (P.right i) (P.cluster ⟨i.1 + 1, hi⟩) := by
  apply Disjoint.mono_left (P.right_subset_cluster i)
  apply P.cluster_disjoint
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- The one-step region added after cluster `i` is contained in the prefix
through cluster `i + 1`. -/
theorem stepRegion_subset_nextPrefix
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (hi : i.1 + 1 < ell) :
    (stitchingPrefixRegion P i ∪
        (P.connector i hi).toPathPacking.vertexSet) ∪
      P.cluster ⟨i.1 + 1, hi⟩ ⊆
        stitchingPrefixRegion P ⟨i.1 + 1, hi⟩ := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvOld | hvNext
  · rcases Finset.mem_union.mp hvOld with hvPrefix | hvConnector
    · exact Finset.mem_union_left _
        (stitchingPrefixRegion_subset_strict_of_lt P (by simp) hvPrefix)
    · exact Finset.mem_union_left _
        (connector_subset_strictStitchingPrefixRegion P hi (by simp)
          hvConnector)
  · exact Finset.mem_union_right _ hvNext

end StrongPathOfSetsSystem

/-- A provenance-preserving full-width row packing through clusters
`0, ..., i`. -/
structure GlobalRowPrefix
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) where
  packing :
    PerfectPathPacking G (P.left P.firstIndex) (P.right i)
  card_eq : packing.card = w
  staysIn :
    packing.toPathPacking.StaysIn (stitchingPrefixRegion P i)
  localIndex :
    ∀ (j : Fin ell), j.1 ≤ i.1 →
      packing.Index →
        (StrongPathOfSetsSystem.clusterLinkage P j).Index
  localIndex_injective :
    ∀ (j : Fin ell) (hji : j.1 ≤ i.1),
      Function.Injective (localIndex j hji)
  local_path_subset :
    ∀ (j : Fin ell) (hji : j.1 ≤ i.1) (a : packing.Index),
      ((StrongPathOfSetsSystem.clusterLinkage P j).path
        (localIndex j hji a)).vertexSet ⊆
        (packing.path a).vertexSet
  local_trace_subset :
    ∀ (j : Fin ell) (hji : j.1 ≤ i.1) (a : packing.Index),
      (packing.path a).vertexSet ∩ P.cluster j ⊆
        ((StrongPathOfSetsSystem.clusterLinkage P j).path
          (localIndex j hji a)).vertexSet
  clusters_ordered :
    ∀ (a : packing.Index) ⦃j k : Fin ell⦄,
      j.1 < k.1 →
      k.1 ≤ i.1 →
      ∀ ⦃u v : V⦄,
        u ∈ (packing.path a).vertexSet →
        u ∈ P.cluster j →
        v ∈ (packing.path a).vertexSet →
        v ∈ P.cluster k →
        (packing.path a).Before u v

namespace GlobalRowPrefix

variable {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}

/-- The recorded local path is the exact trace of a global row in a completed
cluster. -/
theorem local_trace_eq
    (F : GlobalRowPrefix P i) (j : Fin ell) (hji : j.1 ≤ i.1)
    (a : F.packing.Index) :
    (F.packing.path a).vertexSet ∩ P.cluster j =
      ((StrongPathOfSetsSystem.clusterLinkage P j).path
        (F.localIndex j hji a)).vertexSet := by
  apply Finset.Subset.antisymm
  · exact F.local_trace_subset j hji a
  · intro v hv
    exact Finset.mem_inter.mpr
      ⟨F.local_path_subset j hji a hv,
        StrongPathOfSetsSystem.clusterLinkage_staysIn P j
          (F.localIndex j hji a) hv⟩

theorem traceOn_cluster
    (F : GlobalRowPrefix P i) (j : Fin ell) (hji : j.1 ≤ i.1)
    (a : F.packing.Index) :
    (F.packing.path a).TraceOn (P.cluster j) :=
  ⟨(StrongPathOfSetsSystem.clusterLinkage P j).path
      (F.localIndex j hji a),
    (F.local_trace_eq j hji a).symm⟩

/-- Base prefix consisting of the chosen linkage in the first cluster. -/
noncomputable def first
    (P : StrongPathOfSetsSystem G ell w) :
    GlobalRowPrefix P P.firstIndex where
  packing := StrongPathOfSetsSystem.clusterLinkage P P.firstIndex
  card_eq := StrongPathOfSetsSystem.clusterLinkage_card P P.firstIndex
  staysIn := by
    intro a v hv
    exact Finset.mem_union_right _
      (StrongPathOfSetsSystem.clusterLinkage_staysIn P P.firstIndex a hv)
  localIndex := by
    intro j hji
    have hj : j = P.firstIndex := by
      apply Fin.ext
      simp [PathOfSetsSystem.firstIndex] at hji ⊢
      exact hji
    subst j
    exact fun a => a
  localIndex_injective := by
    intro j hji
    have hj : j = P.firstIndex := by
      apply Fin.ext
      simp [PathOfSetsSystem.firstIndex] at hji ⊢
      exact hji
    subst j
    exact fun _ _ h => h
  local_path_subset := by
    intro j hji
    have hj : j = P.firstIndex := by
      apply Fin.ext
      simp [PathOfSetsSystem.firstIndex] at hji ⊢
      exact hji
    subst j
    exact fun _ _ hv => hv
  local_trace_subset := by
    intro j hji
    have hj : j = P.firstIndex := by
      apply Fin.ext
      simp [PathOfSetsSystem.firstIndex] at hji ⊢
      exact hji
    subst j
    intro a v hv
    exact (Finset.mem_inter.mp hv).1
  clusters_ordered := by
    intro a j k hjk hk
    simp [PathOfSetsSystem.firstIndex] at hk
    have : False := by omega
    exact this.elim

/-- A completed prefix is vertex-disjoint from every later cluster. -/
theorem packing_disjoint_futureCluster
    (F : GlobalRowPrefix P i) {j : Fin ell} (hij : i.1 < j.1) :
    Disjoint F.packing.toPathPacking.vertexSet (P.cluster j) := by
  rw [Finset.disjoint_left]
  intro v hvPacking hvCluster
  have hvPrefix :=
    PathPacking.vertexSet_subset_of_staysIn F.staysIn hvPacking
  exact Finset.disjoint_left.mp
    (stitchingPrefixRegion_disjoint_cluster_of_lt P hij)
    hvPrefix hvCluster

/-- Append the connector after a completed prefix, stopping at the next left
nail set. -/
noncomputable def toNextLeft
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    PerfectPathPacking G (P.left P.firstIndex)
      (P.left ⟨i.1 + 1, hi⟩) :=
  F.packing.concatOfFirstStaysInSecondInternallyDisjoint
    (P.connector i hi) F.staysIn
    (StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi)
    (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi)

@[simp] theorem toNextLeft_card
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    (F.toNextLeft hi).card = w := by
  simpa [toNextLeft] using F.card_eq

theorem toNextLeft_staysIn
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    (F.toNextLeft hi).toPathPacking.StaysIn
      (stitchingPrefixRegion P i ∪
        (P.connector i hi).toPathPacking.vertexSet) := by
  simpa [toNextLeft] using
    F.packing.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      (P.connector i hi) F.staysIn
      (StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi)
      (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi)
      (fun a v hv =>
        (P.connector i hi).toPathPacking.path_vertexSet_subset_vertexSet a hv)

theorem toNextLeft_internallyDisjoint_nextCluster
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    (F.toNextLeft hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster ⟨i.1 + 1, hi⟩) := by
  dsimp [toNextLeft,
    PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint]
  apply PerfectPathPacking.concat_internallyDisjointFromSet_right
  · exact F.packing_disjoint_futureCluster (by simp)
  · exact StrongPathOfSetsSystem.right_disjoint_nextCluster P i hi
  · exact P.connector_internally_disjoint_clusters i hi
      ⟨i.1 + 1, hi⟩

/-- Complete the successor prefix by appending the fixed linkage in the next
cluster. -/
noncomputable def extendPacking
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    PerfectPathPacking G (P.left P.firstIndex)
      (P.right ⟨i.1 + 1, hi⟩) :=
  (F.toNextLeft hi).concatOfFirstInternallyDisjointSecondStaysIn
    (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
    (F.toNextLeft_internallyDisjoint_nextCluster hi)
    (StrongPathOfSetsSystem.clusterLinkage_staysIn P ⟨i.1 + 1, hi⟩)
    (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _))

@[simp] theorem extendPacking_card
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    (F.extendPacking hi).card = w := by
  simpa [extendPacking] using F.toNextLeft_card hi

theorem extendPacking_staysIn
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    (F.extendPacking hi).toPathPacking.StaysIn
      (stitchingPrefixRegion P ⟨i.1 + 1, hi⟩) := by
  have hUnion :
      (F.extendPacking hi).toPathPacking.StaysIn
        ((stitchingPrefixRegion P i ∪
            (P.connector i hi).toPathPacking.vertexSet) ∪
          P.cluster ⟨i.1 + 1, hi⟩) := by
    simpa [extendPacking] using
      PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        (F.toNextLeft hi)
        (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
        (F.toNextLeft_internallyDisjoint_nextCluster hi)
        (StrongPathOfSetsSystem.clusterLinkage_staysIn P
          ⟨i.1 + 1, hi⟩)
        (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _))
        (F.toNextLeft_staysIn hi)
  intro a v hv
  exact StrongPathOfSetsSystem.stepRegion_subset_nextPrefix P i hi
    (hUnion a hv)

/-- Old prefix paths occur unchanged inside the half-step packing. -/
theorem packing_path_subset_toNextLeft
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (a : (F.toNextLeft hi).Index) :
    (F.packing.path a).vertexSet ⊆
      ((F.toNextLeft hi).path a).vertexSet := by
  exact
    ChekuriChuzhoy.StitchingPieces.perfect_left_path_subset_concatOfFirstStays
      F.packing
    (P.connector i hi) F.staysIn
    (StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi)
    (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi) a

/-- The half-step path occurs unchanged inside the completed successor path. -/
theorem toNextLeft_path_subset_extendPacking
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (a : (F.extendPacking hi).Index) :
    ((F.toNextLeft hi).path a).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  exact
    ChekuriChuzhoy.StitchingPieces.perfect_left_path_subset_concatOfFirstInternallyDisjoint
    (F.toNextLeft hi)
    (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
    (F.toNextLeft_internallyDisjoint_nextCluster hi)
    (StrongPathOfSetsSystem.clusterLinkage_staysIn P ⟨i.1 + 1, hi⟩)
    (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _)) a

/-- The newly appended local path occurs unchanged in its global row. -/
theorem nextLocal_path_subset_extendPacking
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (a : (F.extendPacking hi).Index) :
    ((StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩).path
      ((F.toNextLeft hi).indexOfSourceTarget
        (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩) a)).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  exact
    ChekuriChuzhoy.StitchingPieces.perfect_right_path_subset_concatOfFirstInternallyDisjoint
    (F.toNextLeft hi)
    (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
    (F.toNextLeft_internallyDisjoint_nextCluster hi)
    (StrongPathOfSetsSystem.clusterLinkage_staysIn P ⟨i.1 + 1, hi⟩)
    (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _)) a

/-- Local-linkage provenance after one successor step. -/
noncomputable def extendLocalIndex
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (j : Fin ell) (hj : j.1 ≤ (⟨i.1 + 1, hi⟩ : Fin ell).1)
    (a : (F.extendPacking hi).Index) :
    (StrongPathOfSetsSystem.clusterLinkage P j).Index := by
  by_cases hnew : j = ⟨i.1 + 1, hi⟩
  · subst j
    exact (F.toNextLeft hi).indexOfSourceTarget
      (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩) a
  · have hval_ne : j.1 ≠ i.1 + 1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hj' : j.1 ≤ i.1 + 1 := by simpa using hj
    have hji : j.1 ≤ i.1 := by omega
    exact F.localIndex j hji a

theorem extendLocalIndex_injective
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (j : Fin ell) (hj : j.1 ≤ (⟨i.1 + 1, hi⟩ : Fin ell).1) :
    Function.Injective (F.extendLocalIndex hi j hj) := by
  by_cases hnew : j = ⟨i.1 + 1, hi⟩
  · subst j
    intro a b hab
    exact
      ChekuriChuzhoy.StitchingPieces.perfect_indexOfSourceTarget_injective
        (F.toNextLeft hi)
        (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
        (by simpa [extendLocalIndex] using hab)
  · have hval_ne : j.1 ≠ i.1 + 1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hj' : j.1 ≤ i.1 + 1 := by simpa using hj
    have hji : j.1 ≤ i.1 := by omega
    intro a b hab
    apply F.localIndex_injective j hji
    simpa [extendLocalIndex, hnew] using hab

theorem extendLocal_path_subset
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (j : Fin ell) (hj : j.1 ≤ (⟨i.1 + 1, hi⟩ : Fin ell).1)
    (a : (F.extendPacking hi).Index) :
    ((StrongPathOfSetsSystem.clusterLinkage P j).path
      (F.extendLocalIndex hi j hj a)).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  by_cases hnew : j = ⟨i.1 + 1, hi⟩
  · subst j
    simpa [extendLocalIndex] using F.nextLocal_path_subset_extendPacking hi a
  · have hval_ne : j.1 ≠ i.1 + 1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hj' : j.1 ≤ i.1 + 1 := by simpa using hj
    have hji : j.1 ≤ i.1 := by omega
    calc
      ((StrongPathOfSetsSystem.clusterLinkage P j).path
          (F.extendLocalIndex hi j hj a)).vertexSet ⊆
          (F.packing.path a).vertexSet := by
        simpa [extendLocalIndex, hnew] using F.local_path_subset j hji a
      _ ⊆ ((F.toNextLeft hi).path a).vertexSet :=
        F.packing_path_subset_toNextLeft hi a
      _ ⊆ ((F.extendPacking hi).path a).vertexSet :=
        F.toNextLeft_path_subset_extendPacking hi a

theorem extendLocal_trace_subset
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (j : Fin ell) (hj : j.1 ≤ (⟨i.1 + 1, hi⟩ : Fin ell).1)
    (a : (F.extendPacking hi).Index) :
    ((F.extendPacking hi).path a).vertexSet ∩ P.cluster j ⊆
      ((StrongPathOfSetsSystem.clusterLinkage P j).path
        (F.extendLocalIndex hi j hj a)).vertexSet := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvExtend, hvCluster⟩
  have hsplit :=
    (F.toNextLeft hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩)
      (F.toNextLeft_internallyDisjoint_nextCluster hi)
      (StrongPathOfSetsSystem.clusterLinkage_staysIn P ⟨i.1 + 1, hi⟩)
      (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _))
      a hvExtend
  by_cases hnew : j = ⟨i.1 + 1, hi⟩
  · subst j
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · rcases F.toNextLeft_internallyDisjoint_nextCluster hi a
          hvHalf hvCluster with hsource | htarget
      · exact False.elim (Finset.disjoint_left.mp
          (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P (Nat.succ_pos _))
          ((F.toNextLeft hi).source_mem a)
          (by rw [← hsource]; exact hvCluster))
      · have hglue :
            v =
              ((StrongPathOfSetsSystem.clusterLinkage P
                ⟨i.1 + 1, hi⟩).path
                ((F.toNextLeft hi).indexOfSourceTarget
                  (StrongPathOfSetsSystem.clusterLinkage P
                    ⟨i.1 + 1, hi⟩) a)).source :=
          htarget.trans
            ((F.toNextLeft hi).source_indexOfSourceTarget
              (StrongPathOfSetsSystem.clusterLinkage P
                ⟨i.1 + 1, hi⟩) a).symm
        simpa [extendLocalIndex, hglue] using
          GraphPath.source_mem_vertexSet
            ((StrongPathOfSetsSystem.clusterLinkage P
              ⟨i.1 + 1, hi⟩).path
              ((F.toNextLeft hi).indexOfSourceTarget
                (StrongPathOfSetsSystem.clusterLinkage P
                  ⟨i.1 + 1, hi⟩) a))
    · simpa [extendLocalIndex] using hvLocal
  · have hval_ne : j.1 ≠ i.1 + 1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hj' : j.1 ≤ i.1 + 1 := by simpa using hj
    have hji : j.1 ≤ i.1 := by omega
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · have hsplitHalf :=
        F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          (P.connector i hi) F.staysIn
          (StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi)
          (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi)
          a hvHalf
      rcases Finset.mem_union.mp hsplitHalf with hvOld | hvConnector
      · simpa [extendLocalIndex, hnew] using
          F.local_trace_subset j hji a
            (Finset.mem_inter.mpr ⟨hvOld, hvCluster⟩)
      · have hvPrefix : v ∈ stitchingPrefixRegion P i := by
          rcases lt_or_eq_of_le hji with hlt | heq
          · exact Finset.mem_union_left _
              (cluster_subset_strictStitchingPrefixRegion P hlt hvCluster)
          · have hji_eq : j = i := Fin.ext heq
            subst j
            exact Finset.mem_union_right _ hvCluster
        rcases StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi
            (F.packing.indexOfSourceTarget (P.connector i hi) a)
            hvConnector hvPrefix with hsource | htarget
        · have hvOld : v ∈ (F.packing.path a).vertexSet := by
            have htarget_eq : v = (F.packing.path a).target :=
              hsource.trans
                (F.packing.source_indexOfSourceTarget
                  (P.connector i hi) a)
            rw [htarget_eq]
            exact GraphPath.target_mem_vertexSet (F.packing.path a)
          simpa [extendLocalIndex, hnew] using
            F.local_trace_subset j hji a
              (Finset.mem_inter.mpr ⟨hvOld, hvCluster⟩)
        · exact False.elim (Finset.disjoint_left.mp
            (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi)
            ((P.connector i hi).target_mem
              (F.packing.indexOfSourceTarget (P.connector i hi) a))
            (by simpa [htarget] using hvPrefix))
    · have hvNext : v ∈ P.cluster ⟨i.1 + 1, hi⟩ :=
        StrongPathOfSetsSystem.clusterLinkage_staysIn P
          ⟨i.1 + 1, hi⟩ _ hvLocal
      have hne : j ≠ ⟨i.1 + 1, hi⟩ := hnew
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne)
          hvCluster hvNext)

/-- A vertex of an old cluster occurring in a successor row already belongs
to the old prefix row. -/
theorem mem_packing_of_mem_extend_of_cluster_le
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (a : (F.extendPacking hi).Index) {j : Fin ell}
    (hji : j.1 ≤ i.1) {v : V}
    (hv : v ∈ ((F.extendPacking hi).path a).vertexSet)
    (hvCluster : v ∈ P.cluster j) :
    v ∈ (F.packing.path a).vertexSet := by
  have hjNext : j.1 ≤ (⟨i.1 + 1, hi⟩ : Fin ell).1 := by
    simpa using Nat.le_trans hji (Nat.le_succ i.1)
  have hnew : j ≠ (⟨i.1 + 1, hi⟩ : Fin ell) := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  have hvLocal :=
    F.extendLocal_trace_subset hi j hjNext a
      (Finset.mem_inter.mpr ⟨hv, hvCluster⟩)
  apply F.local_path_subset j hji a
  simpa [extendLocalIndex, hnew] using hvLocal

/-- A vertex of the new cluster occurring in a successor row belongs to its
newly appended local path. -/
theorem mem_nextLocal_of_mem_extend
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell)
    (a : (F.extendPacking hi).Index) {v : V}
    (hv : v ∈ ((F.extendPacking hi).path a).vertexSet)
    (hvCluster : v ∈ P.cluster ⟨i.1 + 1, hi⟩) :
    v ∈
      ((StrongPathOfSetsSystem.clusterLinkage P ⟨i.1 + 1, hi⟩).path
        ((F.toNextLeft hi).indexOfSourceTarget
          (StrongPathOfSetsSystem.clusterLinkage P
            ⟨i.1 + 1, hi⟩) a)).vertexSet := by
  have hvLocal :=
    F.extendLocal_trace_subset hi ⟨i.1 + 1, hi⟩ (by simp) a
      (Finset.mem_inter.mpr ⟨hv, hvCluster⟩)
  simpa [extendLocalIndex] using hvLocal

/-- Successor constructor for arbitrary-chain global row threading. -/
noncomputable def extend
    (F : GlobalRowPrefix P i) (hi : i.1 + 1 < ell) :
    GlobalRowPrefix P ⟨i.1 + 1, hi⟩ where
  packing := F.extendPacking hi
  card_eq := F.extendPacking_card hi
  staysIn := F.extendPacking_staysIn hi
  localIndex := F.extendLocalIndex hi
  localIndex_injective := F.extendLocalIndex_injective hi
  local_path_subset := F.extendLocal_path_subset hi
  local_trace_subset := F.extendLocal_trace_subset hi
  clusters_ordered := by
    intro a j k hjk hk u v hu hju hv hkv
    by_cases hkOld : k.1 ≤ i.1
    · have hjOld : j.1 ≤ i.1 := Nat.le_trans (Nat.le_of_lt hjk) hkOld
      have huOld :=
        F.mem_packing_of_mem_extend_of_cluster_le hi a hjOld hu hju
      have hvOld :=
        F.mem_packing_of_mem_extend_of_cluster_le hi a hkOld hv hkv
      have hBeforeOld :=
        F.clusters_ordered a hjk hkOld huOld hju hvOld hkv
      have hBeforeHalf :
          ((F.toNextLeft hi).path a).Before u v := by
        simpa [toNextLeft] using
          GraphPath.before_appendWithEq_of_left
            (F.packing.path a)
            ((P.connector i hi).path
              (F.packing.indexOfSourceTarget (P.connector i hi) a))
            (F.packing.source_indexOfSourceTarget (P.connector i hi) a).symm
            (PerfectPathPacking.concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
              F.packing (P.connector i hi) F.staysIn
              (StrongPathOfSetsSystem.connector_internallyDisjoint_prefix P i hi)
              (StrongPathOfSetsSystem.nextLeft_disjoint_prefix P i hi) a)
            hBeforeOld
      simpa [extendPacking] using
        GraphPath.before_appendWithEq_of_left
          ((F.toNextLeft hi).path a)
          ((StrongPathOfSetsSystem.clusterLinkage P
            ⟨i.1 + 1, hi⟩).path
            ((F.toNextLeft hi).indexOfSourceTarget
              (StrongPathOfSetsSystem.clusterLinkage P
                ⟨i.1 + 1, hi⟩) a))
          ((F.toNextLeft hi).source_indexOfSourceTarget
            (StrongPathOfSetsSystem.clusterLinkage P
              ⟨i.1 + 1, hi⟩) a).symm
          (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
            (F.toNextLeft hi)
            (StrongPathOfSetsSystem.clusterLinkage P
              ⟨i.1 + 1, hi⟩)
            (F.toNextLeft_internallyDisjoint_nextCluster hi)
            (StrongPathOfSetsSystem.clusterLinkage_staysIn P
              ⟨i.1 + 1, hi⟩)
            (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P
              (Nat.succ_pos _)) a)
          hBeforeHalf
    · have hkNew : k = (⟨i.1 + 1, hi⟩ : Fin ell) := by
        apply Fin.ext
        have hk' : k.1 ≤ i.1 + 1 := by simpa using hk
        simp
        omega
      subst k
      have hjOld : j.1 ≤ i.1 := by
        simp at hjk
        omega
      have huOld :=
        F.mem_packing_of_mem_extend_of_cluster_le hi a hjOld hu hju
      have huHalf : u ∈ ((F.toNextLeft hi).path a).vertexSet :=
        F.packing_path_subset_toNextLeft hi a huOld
      have hvLocal := F.mem_nextLocal_of_mem_extend hi a hv hkv
      simpa [extendPacking] using
        GraphPath.before_appendWithEq_of_mem_left_of_mem_right
          ((F.toNextLeft hi).path a)
          ((StrongPathOfSetsSystem.clusterLinkage P
            ⟨i.1 + 1, hi⟩).path
            ((F.toNextLeft hi).indexOfSourceTarget
              (StrongPathOfSetsSystem.clusterLinkage P
                ⟨i.1 + 1, hi⟩) a))
          ((F.toNextLeft hi).source_indexOfSourceTarget
            (StrongPathOfSetsSystem.clusterLinkage P
              ⟨i.1 + 1, hi⟩) a).symm
          (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
            (F.toNextLeft hi)
            (StrongPathOfSetsSystem.clusterLinkage P
              ⟨i.1 + 1, hi⟩)
            (F.toNextLeft_internallyDisjoint_nextCluster hi)
            (StrongPathOfSetsSystem.clusterLinkage_staysIn P
              ⟨i.1 + 1, hi⟩)
            (StrongPathOfSetsSystem.firstLeft_disjoint_cluster P
              (Nat.succ_pos _)) a)
          (ha := huHalf) (hb := hvLocal)

/-- Build a prefix at a natural cluster ordinal. -/
noncomputable def ofNat
    (P : StrongPathOfSetsSystem G ell w)
    (n : ℕ) (hn : n < ell) :
    GlobalRowPrefix P ⟨n, hn⟩ :=
  match n with
  | 0 => GlobalRowPrefix.first P
  | n + 1 =>
      (ofNat P n (lt_trans (Nat.lt_succ_self n) hn)).extend hn

/-- The canonical threaded prefix ending at an arbitrary cluster. -/
noncomputable def prefixAt
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    GlobalRowPrefix P i :=
  ofNat P i.1 i.2

/-- Full-width global rows through every cluster. -/
noncomputable def globalRows
    (P : StrongPathOfSetsSystem G ell w) :
    GlobalRowPrefix P P.lastIndex :=
  prefixAt P P.lastIndex

theorem index_le_last
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) :
    i.1 ≤ P.lastIndex.1 := by
  simp [PathOfSetsSystem.lastIndex]
  omega

theorem globalRows_traceOn_cluster
    (P : StrongPathOfSetsSystem G ell w)
    (j : Fin ell) (a : (globalRows P).packing.Index) :
    ((globalRows P).packing.path a).TraceOn (P.cluster j) :=
  (globalRows P).traceOn_cluster j (index_le_last P j) a

theorem globalRows_clusters_ordered
    (P : StrongPathOfSetsSystem G ell w)
    (a : (globalRows P).packing.Index)
    {j k : Fin ell} (hjk : j.1 < k.1)
    {u v : V}
    (hu : u ∈ ((globalRows P).packing.path a).vertexSet)
    (hju : u ∈ P.cluster j)
    (hv : v ∈ ((globalRows P).packing.path a).vertexSet)
    (hkv : v ∈ P.cluster k) :
    ((globalRows P).packing.path a).Before u v :=
  (globalRows P).clusters_ordered a hjk (index_le_last P k)
    hu hju hv hkv

/-- Select the first `g` of the full-width global rows. -/
noncomputable def selectedGlobalIndex
    (F : GlobalRowPrefix P i) (g : ℕ) (hgw : g ≤ w) :
    Fin g ↪ F.packing.Index where
  toFun r :=
    F.packing.finIndexEquiv
      ⟨r.1, by
        have hr : r.1 < g := r.2
        have hcard : F.packing.card = w := F.card_eq
        omega⟩
  inj' := by
    intro r s hrs
    have hfin := F.packing.finIndexEquiv.injective hrs
    have hval : r.1 = s.1 :=
      congrArg (fun x : Fin F.packing.card => x.1) hfin
    exact Fin.ext hval

/-- The selected global row's corresponding local path in cluster `j`. -/
noncomputable def selectedLocalIndex
    (F : GlobalRowPrefix P i) (j : Fin ell) (hji : j.1 ≤ i.1)
    (g : ℕ) (hgw : g ≤ w) :
    Fin g ↪ (StrongPathOfSetsSystem.clusterLinkage P j).Index where
  toFun r := F.localIndex j hji (F.selectedGlobalIndex g hgw r)
  inj' :=
    (F.localIndex_injective j hji).comp
      (F.selectedGlobalIndex g hgw).injective

end GlobalRowPrefix

end Exponent7
end SimpleGraph

end Lax17Proofs
