import Lax17Proofs.Source.HairyPathOfSetsContract
import Lax17Proofs.Source.DegreeThreeStrongPathOfSets
import Lax17Proofs.Source.HairyCrossbarGridIndex

namespace Lax17Proofs

universe u v w

/-!
# Finding hairy path-of-sets systems

This module exposes the hairy Path-of-Sets System existence theorem outside
the contract namespace.  It keeps the contract-backed theorem available as a
legacy conditional endpoint, and also formalizes the Appendix A.4 split-cluster
assembly and the Appendix A.2 composition from explicit proof-facing inputs.

The theorem named `exists_subgraph_hairy_pathOfSets_of_treewidth` at the end of
this file is still the broad Chuzhoy--Tan Theorem 2.3 contract, not a
self-contained proof.  The `*_of_sparsifier_*` and `*_of_A1omega_*` theorems
are the proof-facing routes that avoid the broad A.2 contract by exposing the
lower-level paper inputs.
-/

namespace SimpleGraph
namespace HairyPathOfSetsTheorem


open HairyCrossbarGrid

namespace StrongPathOfSetsSystem

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-!
Appendix A.4 keeps every other cluster of a doubled strong path-of-sets system.
The connector between two retained clusters is routed through the two original
gaps and the intervening cluster.  The next definitions isolate the region used
by such a two-gap stitch, and prove the region disjointness fact directly for
strong path-of-sets systems.  The same argument is used later in the crossbar
grid construction; here it is stated without requiring an already-built hairy
system.
-/

/-- The base path-of-sets region used by the two-gap stitch from selected
cluster `i` to the next selected cluster. -/
noncomputable def twoGapStitchRegion
    {ell w m : ℕ} (P : StrongPathOfSetsSystem G ell w)
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    Finset V :=
  (P.connector (oddClusterIndex hlen i)
    (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
    (P.cluster (middleClusterIndex hlen i) ∪
      (P.connector (middleClusterIndex hlen i)
        (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)

/-- Stitch regions belonging to distinct selected gaps are disjoint.  The proof
is a nine-case split over the three region pieces on each side; connector
families are disjoint for different base gaps, connector paths avoid
nonincident clusters, and distinct middle clusters are disjoint. -/
theorem twoGapStitchRegion_disjoint_of_ne
    {ell w m : ℕ} (P : StrongPathOfSetsSystem G ell w)
    (hlen : 2 * m ≤ ell) {i j : Fin m}
    (hinext : i.1 + 1 < m) (hjnext : j.1 + 1 < m)
    (hij : i ≠ j) :
    Disjoint
      (twoGapStitchRegion P hlen i hinext)
      (twoGapStitchRegion P hlen j hjnext) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [twoGapStitchRegion] at hvi hvj
  rcases Finset.mem_union.mp hvi with hiFirst | hiRest
  · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint
            (i := oddClusterIndex hlen i) (j := oddClusterIndex hlen j)
            (oddClusterIndex_gap hlen i) (oddClusterIndex_gap hlen j)
            (oddClusterIndex_ne_of_ne hlen hij)))
        hiFirst hjFirst
    · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
      · exact Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne
            (oddClusterIndex hlen i) (oddClusterIndex_gap hlen i)
            (middleClusterIndex hlen j)
            (middleClusterIndex_ne_oddClusterIndex hlen j i)
            (by
              simpa [middleClusterIndex_eq_odd_succ hlen i] using
                (middleClusterIndex_ne_of_ne hlen
                  (i := j) (j := i) (fun h => hij h.symm))))
          hiFirst hjMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (P.connector_mutually_nodeDisjoint
              (i := oddClusterIndex hlen i) (j := middleClusterIndex hlen j)
              (oddClusterIndex_gap hlen i) (middleClusterIndex_gap hlen hjnext)
              (oddClusterIndex_ne_middleClusterIndex hlen i j)))
          hiFirst hjSecond
  · rcases Finset.mem_union.mp hiRest with hiMiddle | hiSecond
    · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
      · exact Finset.disjoint_left.mp
          ((P.connector_vertexSet_disjoint_cluster_of_ne
            (oddClusterIndex hlen j) (oddClusterIndex_gap hlen j)
            (middleClusterIndex hlen i)
            (middleClusterIndex_ne_oddClusterIndex hlen i j)
            (by
              simpa [middleClusterIndex_eq_odd_succ hlen j] using
                (middleClusterIndex_ne_of_ne hlen
                  (i := i) (j := j) hij))).symm)
          hiMiddle hjFirst
      · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
        · exact Finset.disjoint_left.mp
            (P.cluster_disjoint
              (middleClusterIndex_ne_of_ne hlen hij))
            hiMiddle hjMiddle
        · exact Finset.disjoint_left.mp
            ((P.connector_vertexSet_disjoint_cluster_of_ne
              (middleClusterIndex hlen j) (middleClusterIndex_gap hlen hjnext)
              (middleClusterIndex hlen i)
              (middleClusterIndex_ne_of_ne hlen hij)
              (by
                simpa [oddClusterIndex_next_eq_middle_succ hlen hjnext] using
                  (middleClusterIndex_ne_oddClusterIndex hlen i
                    ⟨j.1 + 1, hjnext⟩))).symm)
            hiMiddle hjSecond
    · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (P.connector_mutually_nodeDisjoint
              (i := middleClusterIndex hlen i) (j := oddClusterIndex hlen j)
              (middleClusterIndex_gap hlen hinext) (oddClusterIndex_gap hlen j)
              (middleClusterIndex_ne_oddClusterIndex hlen i j)))
          hiSecond hjFirst
      · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
        · exact Finset.disjoint_left.mp
            (P.connector_vertexSet_disjoint_cluster_of_ne
              (middleClusterIndex hlen i) (middleClusterIndex_gap hlen hinext)
              (middleClusterIndex hlen j)
              (middleClusterIndex_ne_of_ne hlen (i := j) (j := i)
                (fun h => hij h.symm))
              (by
                simpa [oddClusterIndex_next_eq_middle_succ hlen hinext] using
                  (middleClusterIndex_ne_oddClusterIndex hlen j
                    ⟨i.1 + 1, hinext⟩)))
            hiSecond hjMiddle
        · exact Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (P.connector_mutually_nodeDisjoint
                (i := middleClusterIndex hlen i) (j := middleClusterIndex hlen j)
                (middleClusterIndex_gap hlen hinext)
                (middleClusterIndex_gap hlen hjnext)
                (middleClusterIndex_ne_of_ne hlen hij)))
            hiSecond hjSecond

end StrongPathOfSetsSystem

/-! ## Appendix A.4 split-cluster assembly -/

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- The local cluster-splitting data used by Chuzhoy--Tan Appendix A.4 after
choosing every other cluster of a doubled strong path-of-sets system.

The structure records the retained base cluster, the corresponding hair
cluster, the retained left/right nails, and the base-side/hair-side endpoints.
It deliberately does not contain the inter-cluster connectors: those are
constructed below from the original strong system by the two-gap stitching
lemma. -/
structure AppendixA4SplitData {ell W w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * ell) W) where
  baseCluster : Fin ell → Finset V
  hairCluster : Fin ell → Finset V
  left : Fin ell → Finset V
  right : Fin ell → Finset V
  x : Fin ell → Finset V
  y : Fin ell → Finset V
  base_subset_old :
    ∀ i : Fin ell,
      baseCluster i ⊆ P.cluster (oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i)
  hair_subset_old :
    ∀ i : Fin ell,
      hairCluster i ⊆ P.cluster (oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i)
  base_connected : ∀ i : Fin ell, IsCluster G (baseCluster i)
  hair_connected : ∀ i : Fin ell, IsCluster G (hairCluster i)
  hair_disjoint_base : ∀ i : Fin ell, Disjoint (hairCluster i) (baseCluster i)
  left_subset_base : ∀ i : Fin ell, left i ⊆ baseCluster i
  right_subset_base : ∀ i : Fin ell, right i ⊆ baseCluster i
  x_subset_base : ∀ i : Fin ell, x i ⊆ baseCluster i
  y_subset_hair : ∀ i : Fin ell, y i ⊆ hairCluster i
  left_subset_old_left :
    ∀ i : Fin ell,
      left i ⊆ P.left (oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i)
  right_subset_old_right :
    ∀ i : Fin ell,
      right i ⊆ P.right (oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i)
  left_card : ∀ i : Fin ell, (left i).card = w
  right_card : ∀ i : Fin ell, (right i).card = w
  x_card : ∀ i : Fin ell, (x i).card = w
  y_card : ∀ i : Fin ell, (y i).card = w
  left_right_disjoint : ∀ i : Fin ell, Disjoint (left i) (right i)
  x_disjoint_nails : ∀ i : Fin ell, Disjoint (x i) (left i ∪ right i)
  left_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (baseCluster i) (left i)
  right_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (baseCluster i) (right i)
  left_right_nodeLinked :
    ∀ i : Fin ell, NodeLinkedIn G (baseCluster i) (left i) (right i)
  left_x_nodeLinked :
    ∀ i : Fin ell, NodeLinkedIn G (baseCluster i) (left i) (x i)
  y_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (hairCluster i) (y i)
  hairConnector : ∀ i : Fin ell, PerfectPathPacking G (x i) (y i)
  hairConnector_card : ∀ i : Fin ell, (hairConnector i).card = w
  hairConnector_staysIn_old :
    ∀ i : Fin ell,
      (hairConnector i).toPathPacking.StaysIn
        (P.cluster (oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i))
  hairConnector_internally_disjoint_base_self :
    ∀ i : Fin ell,
      (hairConnector i).toPathPacking.InternallyDisjointFromSet
        (baseCluster i)
  hairConnector_internally_disjoint_hair_self :
    ∀ i : Fin ell,
      (hairConnector i).toPathPacking.InternallyDisjointFromSet
        (hairCluster i)

namespace AppendixA4SplitData

variable {ell W w : ℕ} {P : StrongPathOfSetsSystem G (2 * ell) W}

/-- The old retained cluster index corresponding to new index `i`. -/
abbrev oldIndex (i : Fin ell) : Fin (2 * ell) :=
  oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i

/-- The old middle cluster between retained clusters `i` and `i+1`. -/
abbrev middleIndex (i : Fin ell) : Fin (2 * ell) :=
  middleClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i

/-- The two-gap connector between retained base clusters. -/
noncomputable def baseConnector (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    PerfectPathPacking G (D.right i) (D.left ⟨i.1 + 1, hi⟩) :=
  Classical.choose
    (P.exists_twoGap_concatPacking_between_subsets
      (oldIndex i)
      (by
        simpa [oldIndex] using
          oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) i)
      (by
        simpa [oldIndex, middleIndex] using
          middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hi)
      (D.right_subset_old_right i)
      (by
        have hnext :
            oldIndex ⟨i.1 + 1, hi⟩ =
              ⟨(middleIndex i).1 + 1,
                by
                  simpa [middleIndex] using
                    middleClusterIndex_gap
                      (le_rfl : 2 * ell ≤ 2 * ell) hi⟩ := by
          simp [oldIndex, middleIndex,
            oddClusterIndex_next_eq_middle_succ
              (le_rfl : 2 * ell ≤ 2 * ell) hi]
        convert D.left_subset_old_left ⟨i.1 + 1, hi⟩ using 1)
      ((D.right_card i).trans (D.left_card ⟨i.1 + 1, hi⟩).symm))

theorem baseConnector_spec (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    (D.baseConnector i hi).card = (D.right i).card ∧
      (D.baseConnector i hi).toPathPacking.StaysIn
        ((P.connector (oldIndex i)
          (by
            simpa [oldIndex] using
              oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) i)).toPathPacking.vertexSet ∪
          (P.cluster (middleIndex i) ∪
            (P.connector (middleIndex i)
              (by
                simpa [middleIndex] using
                  middleClusterIndex_gap
                    (le_rfl : 2 * ell ≤ 2 * ell) hi)).toPathPacking.vertexSet)) ∧
        (D.baseConnector i hi).toPathPacking.InternallyDisjointFromSet
          (P.cluster (oldIndex i)) ∧
          (D.baseConnector i hi).toPathPacking.InternallyDisjointFromSet
            (P.cluster (oldIndex ⟨i.1 + 1, hi⟩)) := by
  classical
  unfold baseConnector
  simpa [oldIndex, middleIndex] using
    Classical.choose_spec
      (P.exists_twoGap_concatPacking_between_subsets
        (oldIndex i)
        (by
          simpa [oldIndex] using
            oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) i)
        (by
          simpa [oldIndex, middleIndex] using
            middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hi)
        (D.right_subset_old_right i)
        (by
          have hnext :
              oldIndex ⟨i.1 + 1, hi⟩ =
                ⟨(middleIndex i).1 + 1,
                  by
                    simpa [middleIndex] using
                      middleClusterIndex_gap
                        (le_rfl : 2 * ell ≤ 2 * ell) hi⟩ := by
            simp [oldIndex, middleIndex,
              oddClusterIndex_next_eq_middle_succ
                (le_rfl : 2 * ell ≤ 2 * ell) hi]
          convert D.left_subset_old_left ⟨i.1 + 1, hi⟩ using 1)
        ((D.right_card i).trans (D.left_card ⟨i.1 + 1, hi⟩).symm))

@[simp] theorem baseConnector_card (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    (D.baseConnector i hi).card = w := by
  exact (D.baseConnector_spec i hi).1.trans (D.right_card i)

theorem baseConnector_staysIn_region (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    (D.baseConnector i hi).toPathPacking.StaysIn
      (StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) i hi) := by
  simpa [StrongPathOfSetsSystem.twoGapStitchRegion, oldIndex, middleIndex] using
    (baseConnector_spec D i hi).2.1

theorem baseConnector_internallyDisjoint_old_current
    (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    (D.baseConnector i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (oldIndex i)) :=
  (baseConnector_spec D i hi).2.2.1

theorem baseConnector_internallyDisjoint_old_next
    (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    (D.baseConnector i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (oldIndex ⟨i.1 + 1, hi⟩)) :=
  (baseConnector_spec D i hi).2.2.2

/-- Distinct retained base clusters are disjoint because they lie in distinct
old strong path-of-sets clusters. -/
theorem baseCluster_disjoint (D : AppendixA4SplitData (w := w) P)
    {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (D.baseCluster i) (D.baseCluster j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hOld :
      oldIndex i ≠ oldIndex j :=
    oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
  exact Finset.disjoint_left.mp (P.cluster_disjoint hOld)
    (D.base_subset_old i hvi) (D.base_subset_old j hvj)

/-- A retained two-gap connector is internally disjoint from every retained
base cluster. -/
theorem baseConnector_internallyDisjoint_baseCluster
    (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (hi : i.1 + 1 < ell) (j : Fin ell) :
    (D.baseConnector i hi).toPathPacking.InternallyDisjointFromSet
      (D.baseCluster j) := by
  classical
  intro a v hvPath hvCluster
  by_cases hji : j = i
  · subst j
    exact baseConnector_internallyDisjoint_old_current D i hi a hvPath
      (D.base_subset_old i hvCluster)
  by_cases hjnext : j = ⟨i.1 + 1, hi⟩
  · subst j
    exact baseConnector_internallyDisjoint_old_next D i hi a hvPath
      (D.base_subset_old ⟨i.1 + 1, hi⟩ hvCluster)
  have hvRegion :
      v ∈ StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) i hi :=
    baseConnector_staysIn_region D i hi a hvPath
  have hvOld : v ∈ P.cluster (oldIndex j) :=
    D.base_subset_old j hvCluster
  rw [StrongPathOfSetsSystem.twoGapStitchRegion] at hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
  · have hstart : oldIndex j ≠ oldIndex i := by
      intro h
      apply hji
      exact (oddClusterIndex_injective (le_rfl : 2 * ell ≤ 2 * ell)) (by
        simpa [oldIndex] using h)
    have hmiddle : oldIndex j ≠ middleIndex i := by
      simpa [oldIndex, middleIndex] using
        oddClusterIndex_ne_middleClusterIndex
          (le_rfl : 2 * ell ≤ 2 * ell) j i
    exact False.elim <|
      Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne
          (oldIndex i)
          (by
            simpa [oldIndex] using
              oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) i)
          (oldIndex j) hstart hmiddle)
        hvFirst hvOld
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
    · have hmiddle_old : middleIndex i ≠ oldIndex j := by
        simpa [oldIndex, middleIndex] using
          middleClusterIndex_ne_oddClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) i j
      exact False.elim <|
        Finset.disjoint_left.mp (P.cluster_disjoint hmiddle_old)
          hvMiddle hvOld
    · have hstart : oldIndex j ≠ middleIndex i := by
        simpa [oldIndex, middleIndex] using
          oddClusterIndex_ne_middleClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) j i
      have hnext : oldIndex j ≠
          ⟨(middleIndex i).1 + 1,
            by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hi⟩ := by
        intro h
        apply hjnext
        apply Fin.ext
        have hval : 2 * j.1 = 2 * i.1 + 1 + 1 := by
          simpa [oldIndex, middleIndex] using congrArg Fin.val h
        have hval' : 2 * j.1 = 2 * (i.1 + 1) := by omega
        exact Nat.mul_left_cancel (by decide : 0 < 2) hval'
      exact False.elim <|
        Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne
            (middleIndex i)
            (by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hi)
            (oldIndex j) hstart hnext)
          hvSecond hvOld

/-- Retained two-gap connectors for distinct new gaps are mutually
node-disjoint. -/
theorem baseConnector_mutually_nodeDisjoint
    (D : AppendixA4SplitData (w := w) P)
    {i j : Fin ell} (hi : i.1 + 1 < ell) (hj : j.1 + 1 < ell)
    (hij : i ≠ j) :
    (D.baseConnector i hi).toPathPacking.MutuallyNodeDisjoint
      (D.baseConnector j hj).toPathPacking := by
  classical
  intro a b
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hviRegion :
      v ∈ StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) i hi :=
    baseConnector_staysIn_region D i hi a hvi
  have hvjRegion :
      v ∈ StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) j hj :=
    baseConnector_staysIn_region D j hj b hvj
  exact Finset.disjoint_left.mp
    (StrongPathOfSetsSystem.twoGapStitchRegion_disjoint_of_ne
      P (le_rfl : 2 * ell ≤ 2 * ell) hi hj hij)
    hviRegion hvjRegion

/-- Appendix A.4 base assembly: after splitting the retained old clusters,
the retained clusters and the two-gap stitched connectors form a strong
path-of-sets system. -/
noncomputable def toStrongPathOfSetsSystem
    (D : AppendixA4SplitData (w := w) P)
    (hell : 0 < ell) (hw : 0 < w) :
    StrongPathOfSetsSystem G ell w where
  length_pos := hell
  width_pos := hw
  cluster := D.baseCluster
  cluster_connected := D.base_connected
  cluster_disjoint := by
    intro i j hij
    exact D.baseCluster_disjoint hij
  left := D.left
  right := D.right
  left_subset_cluster := D.left_subset_base
  right_subset_cluster := D.right_subset_base
  left_right_disjoint := D.left_right_disjoint
  left_card := D.left_card
  right_card := D.right_card
  connector := fun i hi => D.baseConnector i hi
  connector_card := by
    intro i hi
    exact D.baseConnector_card i hi
  connector_internally_disjoint_clusters := by
    intro i hi j
    exact D.baseConnector_internallyDisjoint_baseCluster i hi j
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij
    exact D.baseConnector_mutually_nodeDisjoint hi hj hij
  left_nodeWellLinked := D.left_nodeWellLinked
  right_nodeWellLinked := D.right_nodeWellLinked
  left_right_nodeLinked := D.left_right_nodeLinked

end AppendixA4SplitData

namespace AppendixA4SplitData

variable {ell W w : ℕ} {P : StrongPathOfSetsSystem G (2 * ell) W}

theorem hairCluster_disjoint (D : AppendixA4SplitData (w := w) P)
    {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (D.hairCluster i) (D.hairCluster j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hOld :
      oldIndex i ≠ oldIndex j :=
    oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
  exact Finset.disjoint_left.mp (P.cluster_disjoint hOld)
    (D.hair_subset_old i hvi) (D.hair_subset_old j hvj)

theorem hairCluster_disjoint_baseCluster
    (D : AppendixA4SplitData (w := w) P)
    (i j : Fin ell) :
    Disjoint (D.hairCluster i) (D.baseCluster j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact D.hair_disjoint_base i
  · rw [Finset.disjoint_left]
    intro v hvHair hvBase
    have hOld :
        oldIndex i ≠ oldIndex j :=
      oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
    exact Finset.disjoint_left.mp (P.cluster_disjoint hOld)
      (D.hair_subset_old i hvHair) (D.base_subset_old j hvBase)

theorem hairConnector_mutually_nodeDisjoint
    (D : AppendixA4SplitData (w := w) P)
    {i j : Fin ell} (hij : i ≠ j) :
    (D.hairConnector i).toPathPacking.MutuallyNodeDisjoint
      (D.hairConnector j).toPathPacking := by
  classical
  intro a b
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hOld :
      oldIndex i ≠ oldIndex j :=
    oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
  exact Finset.disjoint_left.mp (P.cluster_disjoint hOld)
    (D.hairConnector_staysIn_old i a hvi)
    (D.hairConnector_staysIn_old j b hvj)

theorem hairConnector_internallyDisjoint_baseCluster
    (D : AppendixA4SplitData (w := w) P)
    (i j : Fin ell) :
    (D.hairConnector i).toPathPacking.InternallyDisjointFromSet
      (D.baseCluster j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact D.hairConnector_internally_disjoint_base_self i
  · intro a v hvPath hvBase
    have hOld :
        oldIndex i ≠ oldIndex j :=
      oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
    exact False.elim <|
      Finset.disjoint_left.mp (P.cluster_disjoint hOld)
        (D.hairConnector_staysIn_old i a hvPath)
        (D.base_subset_old j hvBase)

theorem hairConnector_internallyDisjoint_hairCluster
    (D : AppendixA4SplitData (w := w) P)
    (i j : Fin ell) :
    (D.hairConnector i).toPathPacking.InternallyDisjointFromSet
      (D.hairCluster j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact D.hairConnector_internally_disjoint_hair_self i
  · intro a v hvPath hvHair
    have hOld :
        oldIndex i ≠ oldIndex j :=
      oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
    exact False.elim <|
      Finset.disjoint_left.mp (P.cluster_disjoint hOld)
        (D.hairConnector_staysIn_old i a hvPath)
        (D.hair_subset_old j hvHair)

/-- Hair clusters are automatically disjoint from the stitched base
connectors.  For an incident retained cluster, the base connector can meet the
old cluster only at its base nail endpoint; for non-incident retained clusters,
the two-gap stitch region is disjoint from the old cluster. -/
theorem hairCluster_disjoint_baseConnector
    (D : AppendixA4SplitData (w := w) P)
    (i j : Fin ell) (hj : j.1 + 1 < ell) :
    Disjoint (D.hairCluster i)
      (D.baseConnector j hj).toPathPacking.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvHair hvConnSet
  rcases ((D.baseConnector j hj).toPathPacking.mem_vertexSet).1
      hvConnSet with
    ⟨a, hvConn⟩
  by_cases hij : i = j
  · subst i
    have hvOld : v ∈ P.cluster (oldIndex j) :=
      D.hair_subset_old j hvHair
    rcases D.baseConnector_internallyDisjoint_old_current j hj a
        hvConn hvOld with hsrc | htgt
    · have hvRight : v ∈ D.right j := by
        simpa [hsrc] using (D.baseConnector j hj).source_mem a
      exact Finset.disjoint_left.mp (D.hair_disjoint_base j)
        hvHair (D.right_subset_base j hvRight)
    · have hvNextOld :
          v ∈ P.cluster (oldIndex ⟨j.1 + 1, hj⟩) :=
        P.left_subset_cluster (oldIndex ⟨j.1 + 1, hj⟩)
          (D.left_subset_old_left ⟨j.1 + 1, hj⟩
            (by simpa [htgt] using (D.baseConnector j hj).target_mem a))
      have hjne : j ≠ ⟨j.1 + 1, hj⟩ := by
        intro h
        have hval : j.1 = j.1 + 1 := by
          simpa using congrArg Fin.val h
        omega
      have hOldNe :
          oldIndex j ≠ oldIndex ⟨j.1 + 1, hj⟩ :=
        oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hjne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hOldNe)
        hvOld hvNextOld
  by_cases hinext : i = ⟨j.1 + 1, hj⟩
  · subst i
    have hvOld : v ∈ P.cluster (oldIndex ⟨j.1 + 1, hj⟩) :=
      D.hair_subset_old ⟨j.1 + 1, hj⟩ hvHair
    rcases D.baseConnector_internallyDisjoint_old_next j hj a
        hvConn hvOld with hsrc | htgt
    · have hvCurrentOld : v ∈ P.cluster (oldIndex j) :=
        P.right_subset_cluster (oldIndex j)
          (D.right_subset_old_right j
            (by simpa [hsrc] using (D.baseConnector j hj).source_mem a))
      have hjne : j ≠ ⟨j.1 + 1, hj⟩ := by
        intro h
        have hval : j.1 = j.1 + 1 := by
          simpa using congrArg Fin.val h
        omega
      have hOldNe :
          oldIndex j ≠ oldIndex ⟨j.1 + 1, hj⟩ :=
        oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hjne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hOldNe)
        hvCurrentOld hvOld
    · have hvLeft : v ∈ D.left ⟨j.1 + 1, hj⟩ := by
        simpa [htgt] using (D.baseConnector j hj).target_mem a
      exact Finset.disjoint_left.mp
        (D.hair_disjoint_base ⟨j.1 + 1, hj⟩)
        hvHair (D.left_subset_base ⟨j.1 + 1, hj⟩ hvLeft)
  have hvRegion :
      v ∈ StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) j hj :=
    D.baseConnector_staysIn_region j hj a hvConn
  have hvOld : v ∈ P.cluster (oldIndex i) :=
    D.hair_subset_old i hvHair
  rw [StrongPathOfSetsSystem.twoGapStitchRegion] at hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
  · have hstart : oldIndex i ≠ oldIndex j :=
      oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
    have hmiddle : oldIndex i ≠ middleIndex j := by
      simpa [oldIndex, middleIndex] using
        oddClusterIndex_ne_middleClusterIndex
          (le_rfl : 2 * ell ≤ 2 * ell) i j
    exact False.elim <|
      Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne
          (oldIndex j)
          (by
            simpa [oldIndex] using
              oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) j)
          (oldIndex i) hstart hmiddle)
        hvFirst hvOld
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
    · have hmiddle_old : middleIndex j ≠ oldIndex i := by
        simpa [oldIndex, middleIndex] using
          middleClusterIndex_ne_oddClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) j i
      exact False.elim <|
        Finset.disjoint_left.mp (P.cluster_disjoint hmiddle_old)
          hvMiddle hvOld
    · have hstart : oldIndex i ≠ middleIndex j := by
        simpa [oldIndex, middleIndex] using
          oddClusterIndex_ne_middleClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) i j
      have hnext : oldIndex i ≠
          ⟨(middleIndex j).1 + 1,
            by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hj⟩ := by
        intro h
        apply hinext
        apply Fin.ext
        have hval : 2 * i.1 = 2 * j.1 + 1 + 1 := by
          simpa [oldIndex, middleIndex] using congrArg Fin.val h
        have hval' : 2 * i.1 = 2 * (j.1 + 1) := by omega
        exact Nat.mul_left_cancel (by decide : 0 < 2) hval'
      exact False.elim <|
        Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne
            (middleIndex j)
            (by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hj)
          (oldIndex i) hstart hnext)
          hvSecond hvOld

/-- A hair connector for cluster `i` is disjoint from the left/right nail
union of the same base cluster.  Its only possible base-cluster endpoint is in
`x i`, and `x i` is disjoint from the nails. -/
theorem hairConnector_path_disjoint_nails
    (D : AppendixA4SplitData (w := w) P)
    (i : Fin ell) (a : (D.hairConnector i).Index) :
    Disjoint ((D.hairConnector i).path a).vertexSet
      (D.left i ∪ D.right i) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPath hvNails
  have hvBase : v ∈ D.baseCluster i := by
    rcases Finset.mem_union.mp hvNails with hvLeft | hvRight
    · exact D.left_subset_base i hvLeft
    · exact D.right_subset_base i hvRight
  rcases D.hairConnector_internally_disjoint_base_self i a
      hvPath hvBase with hsrc | htgt
  · exact Finset.disjoint_left.mp (D.x_disjoint_nails i)
      (by simpa [hsrc] using (D.hairConnector i).source_mem a)
      (by simpa [hsrc] using hvNails)
  · have hvHair : v ∈ D.hairCluster i :=
      D.y_subset_hair i
        (by simpa [htgt] using (D.hairConnector i).target_mem a)
    exact Finset.disjoint_left.mp (D.hair_disjoint_base i)
      hvHair hvBase

/-- Hair connectors are automatically node-disjoint from the stitched base
connectors.  In incident clusters this follows from the nail-disjointness
helper above; in non-incident clusters it follows from disjointness of the
two-gap stitch region and the old cluster containing the hair connector. -/
theorem hairConnector_disjoint_baseConnector
    (D : AppendixA4SplitData (w := w) P)
    (i j : Fin ell) (hj : j.1 + 1 < ell) :
    (D.hairConnector i).toPathPacking.MutuallyNodeDisjoint
      (D.baseConnector j hj).toPathPacking := by
  classical
  intro a b
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvHair hvBase
  by_cases hij : i = j
  · subst i
    have hvOld : v ∈ P.cluster (oldIndex j) :=
      D.hairConnector_staysIn_old j a hvHair
    rcases D.baseConnector_internallyDisjoint_old_current j hj b
        hvBase hvOld with hsrc | htgt
    · have hvRight : v ∈ D.right j := by
        simpa [hsrc] using (D.baseConnector j hj).source_mem b
      exact Finset.disjoint_left.mp
        (D.hairConnector_path_disjoint_nails j a)
        hvHair (Finset.mem_union_right _ hvRight)
    · have hvNextOld :
          v ∈ P.cluster (oldIndex ⟨j.1 + 1, hj⟩) :=
        P.left_subset_cluster (oldIndex ⟨j.1 + 1, hj⟩)
          (D.left_subset_old_left ⟨j.1 + 1, hj⟩
            (by simpa [htgt] using (D.baseConnector j hj).target_mem b))
      have hjne : j ≠ ⟨j.1 + 1, hj⟩ := by
        intro h
        have hval : j.1 = j.1 + 1 := by
          simpa using congrArg Fin.val h
        omega
      have hOldNe :
          oldIndex j ≠ oldIndex ⟨j.1 + 1, hj⟩ :=
        oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hjne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hOldNe)
        hvOld hvNextOld
  by_cases hinext : i = ⟨j.1 + 1, hj⟩
  · subst i
    have hvOld : v ∈ P.cluster (oldIndex ⟨j.1 + 1, hj⟩) :=
      D.hairConnector_staysIn_old ⟨j.1 + 1, hj⟩ a hvHair
    rcases D.baseConnector_internallyDisjoint_old_next j hj b
        hvBase hvOld with hsrc | htgt
    · have hvCurrentOld : v ∈ P.cluster (oldIndex j) :=
        P.right_subset_cluster (oldIndex j)
          (D.right_subset_old_right j
            (by simpa [hsrc] using (D.baseConnector j hj).source_mem b))
      have hjne : j ≠ ⟨j.1 + 1, hj⟩ := by
        intro h
        have hval : j.1 = j.1 + 1 := by
          simpa using congrArg Fin.val h
        omega
      have hOldNe :
          oldIndex j ≠ oldIndex ⟨j.1 + 1, hj⟩ :=
        oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hjne
      exact Finset.disjoint_left.mp (P.cluster_disjoint hOldNe)
        hvCurrentOld hvOld
    · have hvLeft : v ∈ D.left ⟨j.1 + 1, hj⟩ := by
        simpa [htgt] using (D.baseConnector j hj).target_mem b
      exact Finset.disjoint_left.mp
        (D.hairConnector_path_disjoint_nails ⟨j.1 + 1, hj⟩ a)
        hvHair (Finset.mem_union_left _ hvLeft)
  have hvRegion :
      v ∈ StrongPathOfSetsSystem.twoGapStitchRegion P
        (le_rfl : 2 * ell ≤ 2 * ell) j hj :=
    D.baseConnector_staysIn_region j hj b hvBase
  have hvOld : v ∈ P.cluster (oldIndex i) :=
    D.hairConnector_staysIn_old i a hvHair
  rw [StrongPathOfSetsSystem.twoGapStitchRegion] at hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
  · have hstart : oldIndex i ≠ oldIndex j :=
      oddClusterIndex_ne_of_ne (le_rfl : 2 * ell ≤ 2 * ell) hij
    have hmiddle : oldIndex i ≠ middleIndex j := by
      simpa [oldIndex, middleIndex] using
        oddClusterIndex_ne_middleClusterIndex
          (le_rfl : 2 * ell ≤ 2 * ell) i j
    exact False.elim <|
      Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne
          (oldIndex j)
          (by
            simpa [oldIndex] using
              oddClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) j)
          (oldIndex i) hstart hmiddle)
        hvFirst hvOld
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
    · have hmiddle_old : middleIndex j ≠ oldIndex i := by
        simpa [oldIndex, middleIndex] using
          middleClusterIndex_ne_oddClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) j i
      exact False.elim <|
        Finset.disjoint_left.mp (P.cluster_disjoint hmiddle_old)
          hvMiddle hvOld
    · have hstart : oldIndex i ≠ middleIndex j := by
        simpa [oldIndex, middleIndex] using
          oddClusterIndex_ne_middleClusterIndex
            (le_rfl : 2 * ell ≤ 2 * ell) i j
      have hnext : oldIndex i ≠
          ⟨(middleIndex j).1 + 1,
            by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hj⟩ := by
        intro h
        apply hinext
        apply Fin.ext
        have hval : 2 * i.1 = 2 * j.1 + 1 + 1 := by
          simpa [oldIndex, middleIndex] using congrArg Fin.val h
        have hval' : 2 * i.1 = 2 * (j.1 + 1) := by omega
        exact Nat.mul_left_cancel (by decide : 0 < 2) hval'
      exact False.elim <|
        Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne
            (middleIndex j)
            (by
              simpa [middleIndex] using
                middleClusterIndex_gap (le_rfl : 2 * ell ≤ 2 * ell) hj)
            (oldIndex i) hstart hnext)
          hvSecond hvOld

/-- Appendix A.4 assembly from split clusters, two-gap stitched base
connectors, and the automatically verified hair/backbone separation facts. -/
noncomputable def toHairyPathOfSetsSystem
    (D : AppendixA4SplitData (w := w) P)
    (hell : 0 < ell) (hw : 0 < w) :
    HairyPathOfSetsSystem G ell w where
  base := D.toStrongPathOfSetsSystem hell hw
  hairCluster := D.hairCluster
  hairCluster_connected := D.hair_connected
  hairCluster_disjoint := by
    intro i j hij
    exact D.hairCluster_disjoint hij
  hairCluster_disjoint_base := by
    intro i j
    exact D.hairCluster_disjoint_baseCluster i j
  hairCluster_disjoint_baseConnectors := by
    intro i j hj
    exact D.hairCluster_disjoint_baseConnector i j hj
  x := D.x
  y := D.y
  x_subset_cluster := D.x_subset_base
  y_subset_hairCluster := D.y_subset_hair
  x_card := D.x_card
  y_card := D.y_card
  x_disjoint_nails := D.x_disjoint_nails
  y_nodeWellLinked := D.y_nodeWellLinked
  left_x_nodeLinked := D.left_x_nodeLinked
  hairConnector := D.hairConnector
  hairConnector_card := D.hairConnector_card
  hairConnector_mutually_nodeDisjoint := by
    intro i j hij
    exact D.hairConnector_mutually_nodeDisjoint hij
  hairConnector_disjoint_baseConnectors := by
    intro i j hj
    exact D.hairConnector_disjoint_baseConnector i j hj
  hairConnector_internally_disjoint_baseClusters := by
    intro i j
    exact D.hairConnector_internallyDisjoint_baseCluster i j
  hairConnector_internally_disjoint_hairClusters := by
    intro i j
    exact D.hairConnector_internallyDisjoint_hairCluster i j

end AppendixA4SplitData

/-- Existence form of the Appendix A.4 split-cluster construction.  The
external cluster-splitting ingredients are isolated in the existence of
`AppendixA4SplitData`; the Lean assembly from that data, including the
hair/backbone separation checks, is proved above. -/
def AppendixA4SplitInput (cSplit : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * ell) (cSplit * w)),
      0 < ell →
        0 < w →
          MaxDegreeAtMost G 3 →
            Nonempty (AppendixA4SplitData (w := w) P)

/-- Local split-cluster data supplied by the theorem quoted as Appendix A.3
in Chuzhoy--Tan.

This is the single-cluster version of the data needed by Appendix A.4.  Given
a strong cluster `C` with left/right nail sets `A` and `B`, it produces the
retained base cluster, the hair cluster, thinned nail sets, a base-side hair
endpoint set, a hair-side endpoint set, and the hair paths joining them. -/
structure AppendixA3ClusterSplitData
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C A B : Finset V) (w : ℕ) where
  baseCluster : Finset V
  hairCluster : Finset V
  left : Finset V
  right : Finset V
  x : Finset V
  y : Finset V
  base_subset_cluster : baseCluster ⊆ C
  hair_subset_cluster : hairCluster ⊆ C
  base_connected : IsCluster G baseCluster
  hair_connected : IsCluster G hairCluster
  hair_disjoint_base : Disjoint hairCluster baseCluster
  left_subset_base : left ⊆ baseCluster
  right_subset_base : right ⊆ baseCluster
  x_subset_base : x ⊆ baseCluster
  y_subset_hair : y ⊆ hairCluster
  left_subset_old_left : left ⊆ A
  right_subset_old_right : right ⊆ B
  left_card : left.card = w
  right_card : right.card = w
  x_card : x.card = w
  y_card : y.card = w
  left_right_disjoint : Disjoint left right
  x_disjoint_nails : Disjoint x (left ∪ right)
  left_nodeWellLinked : NodeWellLinkedIn G baseCluster left
  right_nodeWellLinked : NodeWellLinkedIn G baseCluster right
  left_right_nodeLinked : NodeLinkedIn G baseCluster left right
  left_x_nodeLinked : NodeLinkedIn G baseCluster left x
  y_nodeWellLinked : NodeWellLinkedIn G hairCluster y
  hairConnector : PerfectPathPacking G x y
  hairConnector_card : hairConnector.card = w
  hairConnector_staysIn_cluster : hairConnector.toPathPacking.StaysIn C
  hairConnector_internally_disjoint_base :
    hairConnector.toPathPacking.InternallyDisjointFromSet baseCluster
  hairConnector_internally_disjoint_hair :
    hairConnector.toPathPacking.InternallyDisjointFromSet hairCluster

namespace AppendixA3ClusterSplitData

/-- Transfer a split-cluster construction from a same-vertex subgraph to the
ambient graph. All set-theoretic fields are unchanged; paths are mapped along
the graph inclusion. -/
def mapLe {V : Type u} [DecidableEq V]
    {H G : _root_.SimpleGraph V} {C A B : Finset V} {w : ℕ}
    (D : AppendixA3ClusterSplitData H C A B w) (hHG : H ≤ G) :
    AppendixA3ClusterSplitData G C A B w where
  baseCluster := D.baseCluster
  hairCluster := D.hairCluster
  left := D.left
  right := D.right
  x := D.x
  y := D.y
  base_subset_cluster := D.base_subset_cluster
  hair_subset_cluster := D.hair_subset_cluster
  base_connected := IsCluster.mono_graph D.base_connected hHG
  hair_connected := IsCluster.mono_graph D.hair_connected hHG
  hair_disjoint_base := D.hair_disjoint_base
  left_subset_base := D.left_subset_base
  right_subset_base := D.right_subset_base
  x_subset_base := D.x_subset_base
  y_subset_hair := D.y_subset_hair
  left_subset_old_left := D.left_subset_old_left
  right_subset_old_right := D.right_subset_old_right
  left_card := D.left_card
  right_card := D.right_card
  x_card := D.x_card
  y_card := D.y_card
  left_right_disjoint := D.left_right_disjoint
  x_disjoint_nails := D.x_disjoint_nails
  left_nodeWellLinked := NodeWellLinkedIn.mono_graph D.left_nodeWellLinked hHG
  right_nodeWellLinked := NodeWellLinkedIn.mono_graph D.right_nodeWellLinked hHG
  left_right_nodeLinked := NodeLinkedIn.mono_graph D.left_right_nodeLinked hHG
  left_x_nodeLinked := NodeLinkedIn.mono_graph D.left_x_nodeLinked hHG
  y_nodeWellLinked := NodeWellLinkedIn.mono_graph D.y_nodeWellLinked hHG
  hairConnector := D.hairConnector.mapLe hHG
  hairConnector_card := by simpa using D.hairConnector_card
  hairConnector_staysIn_cluster := by
    intro i
    change ((D.hairConnector.path i).mapLe hHG).vertexSet ⊆ C
    simpa using D.hairConnector_staysIn_cluster i
  hairConnector_internally_disjoint_base := by
    intro i
    change ((D.hairConnector.path i).mapLe hHG).InternallyDisjointFromSet
      D.baseCluster
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      D.hairConnector_internally_disjoint_base i
  hairConnector_internally_disjoint_hair := by
    intro i
    change ((D.hairConnector.path i).mapLe hHG).InternallyDisjointFromSet
      D.hairCluster
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      D.hairConnector_internally_disjoint_hair i

end AppendixA3ClusterSplitData

/-- Appendix A.3 in the local form consumed by Appendix A.4.

The source theorem is applied to a single degree-three graph cluster whose two
nail sets have size `cSplit * w`, are node-well-linked, and are node-linked to
each other.  It returns the split data with final width `w`. -/
def AppendixA3ClusterSplitInput (cSplit : ℕ) : Prop :=
  0 < cSplit ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {C A B : Finset V} {w : ℕ},
        0 < w →
          MaxDegreeAtMost G 3 →
            IsCluster G C →
              A ⊆ C →
                B ⊆ C →
                  A.card = cSplit * w →
                    B.card = cSplit * w →
                      Disjoint A B →
                        NodeWellLinkedIn G C A →
                          NodeWellLinkedIn G C B →
                            NodeLinkedIn G C A B →
                              Nonempty (AppendixA3ClusterSplitData G C A B w)

/-- The per-cluster split theorem from Appendix A.3 supplies the global
Appendix A.4 split input by applying it independently to every retained odd
cluster of the doubled strong path-of-sets system. -/
theorem appendixA4SplitInput_of_appendixA3ClusterSplitInput
    {cSplit : ℕ}
    (hinput : AppendixA3ClusterSplitInput.{u} cSplit) :
    AppendixA4SplitInput.{u} cSplit := by
  classical
  rcases hinput with ⟨_hcSplit, hsplit⟩
  intro V _ _ G ell w P hell hw hdegree
  let oldIndex : Fin ell → Fin (2 * ell) :=
    fun i => oddClusterIndex (le_rfl : 2 * ell ≤ 2 * ell) i
  let D : ∀ i : Fin ell,
      AppendixA3ClusterSplitData G
        (P.cluster (oldIndex i)) (P.left (oldIndex i))
        (P.right (oldIndex i)) w :=
    fun i =>
      Classical.choice
        (hsplit G hw hdegree (P.cluster_connected (oldIndex i))
          (P.left_subset_cluster (oldIndex i))
          (P.right_subset_cluster (oldIndex i))
          (P.left_card (oldIndex i))
          (P.right_card (oldIndex i))
          (P.left_right_disjoint (oldIndex i))
          (P.left_nodeWellLinked (oldIndex i))
          (P.right_nodeWellLinked (oldIndex i))
          (P.left_right_nodeLinked (oldIndex i)))
  refine ⟨?_⟩
  exact
    { baseCluster := fun i => (D i).baseCluster
      hairCluster := fun i => (D i).hairCluster
      left := fun i => (D i).left
      right := fun i => (D i).right
      x := fun i => (D i).x
      y := fun i => (D i).y
      base_subset_old := fun i => (D i).base_subset_cluster
      hair_subset_old := fun i => (D i).hair_subset_cluster
      base_connected := fun i => (D i).base_connected
      hair_connected := fun i => (D i).hair_connected
      hair_disjoint_base := fun i => (D i).hair_disjoint_base
      left_subset_base := fun i => (D i).left_subset_base
      right_subset_base := fun i => (D i).right_subset_base
      x_subset_base := fun i => (D i).x_subset_base
      y_subset_hair := fun i => (D i).y_subset_hair
      left_subset_old_left := fun i => (D i).left_subset_old_left
      right_subset_old_right := fun i => (D i).right_subset_old_right
      left_card := fun i => (D i).left_card
      right_card := fun i => (D i).right_card
      x_card := fun i => (D i).x_card
      y_card := fun i => (D i).y_card
      left_right_disjoint := fun i => (D i).left_right_disjoint
      x_disjoint_nails := fun i => (D i).x_disjoint_nails
      left_nodeWellLinked := fun i => (D i).left_nodeWellLinked
      right_nodeWellLinked := fun i => (D i).right_nodeWellLinked
      left_right_nodeLinked := fun i => (D i).left_right_nodeLinked
      left_x_nodeLinked := fun i => (D i).left_x_nodeLinked
      y_nodeWellLinked := fun i => (D i).y_nodeWellLinked
      hairConnector := fun i => (D i).hairConnector
      hairConnector_card := fun i => (D i).hairConnector_card
      hairConnector_staysIn_old := fun i => (D i).hairConnector_staysIn_cluster
      hairConnector_internally_disjoint_base_self :=
        fun i => (D i).hairConnector_internally_disjoint_base
      hairConnector_internally_disjoint_hair_self :=
        fun i => (D i).hairConnector_internally_disjoint_hair }

/-!
Appendix A.2 proves Theorem 2.3 from two ingredients:

* the quoted degree-three sparsifier together with the quoted strong
  path-of-sets theorem, after absorbing constants; and
* the Chuzhoy--Tan conversion from a strong path-of-sets system of doubled
  length and larger width to a hairy path-of-sets system.

The definitions below expose that proof boundary explicitly.  The final theorem
`exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs` is the
formalized Appendix A.2 composition, with no use of the Theorem 2.3 contract.
-/

/-- Combined external input used at the start of Appendix A.2: after applying
the degree-three treewidth sparsifier and the quoted strong path-of-sets
theorem, a sufficiently large-treewidth graph has a degree-three subgraph with
a strong path-of-sets system of doubled length and scaled width. -/
def DegreeThreeStrongPathOfSetsInput (cStrong cStrongLog cSplit : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w k : ℕ},
      1 < ell →
        1 < w →
          1 < k →
            k ≤ treewidth G →
              cStrong * (cSplit * w) * (2 * ell) ^ 50 *
                  (Nat.log 2 k) ^ cStrongLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧
                    MaxDegreeAtMost H 3 ∧
                      Nonempty (StrongPathOfSetsSystem H (2 * ell) (cSplit * w))


/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier and the reduced Chekuri--Chuzhoy A.2 source route.

This avoids the broad `exists_strongPathOfSets_of_treewidth` contract by using
the cut-well-linked Theorem 2.21 boundary plus the Section 4 tree-of-sets
route. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
      (cSplit := cSplit) hcSplit hsparseInput hcut hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, the cut-well-linked Theorem 2.21 boundary, and the
faithful direct Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseInput hcut hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, Lemma 2.17 routability, the cut-matching/AARV
embedding source, and the Section 4 tree-of-sets route. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, Lemma 2.17 routability, the cut-matching/AARV
embedding source, and the faithful direct Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, and Theorem 4.6
extraction. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hextract with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, and the split proof
of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hdichotomy hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from the
degree-three sparsifier, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, the proved
finite-tree dichotomy, and the DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from Theorem A.1
in its paper-shaped Omega form, Lemma 2.17 routability, the cut-matching/AARV
embedding source, and the faithful direct Section 4 path route. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from Theorem A.1
in Omega form and the bundled explicit Chekuri--Chuzhoy A.2 source inputs. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_theoremA2SourceInputs
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_theoremA2SourceInputs
      (cSplit := cSplit) hcSplit hsparseOmega hA2 with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from Theorem A.1
in its paper-shaped Omega form, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, and Theorem 4.6
extraction. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hextract with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from Theorem A.1
in its paper-shaped Omega form, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, and the split proof
of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hdichotomy hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge

/-- The Appendix A.2 degree-three/strong-path-of-sets input from Theorem A.1
in its paper-shaped Omega form, Lemma 2.17 routability, the cut-matching/AARV
embedding source, the Section 4 strong-tree construction, the proved
finite-tree dichotomy, and the DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit := by
  rcases
    DegreeThreeStrongPathOfSets.exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  exact hinput (V := V) G hell hw hk htw hlarge


/-- Chuzhoy--Tan Appendix A.4, in the exact parameter shape used by Appendix
A.2: a strong path-of-sets system of doubled length and scaled width in a
degree-three graph yields a hairy path-of-sets system of the requested length
and width. -/
def StrongPathOfSetsToHairyInput (cSplit : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w : ℕ},
      1 < ell →
        1 < w →
          MaxDegreeAtMost G 3 →
            Nonempty (StrongPathOfSetsSystem G (2 * ell) (cSplit * w)) →
              Nonempty (HairyPathOfSetsSystem G ell w)

/-- The formal Appendix A.4 assembly supplies the strong-to-hairy input used in
Appendix A.2 once the split-cluster existence statement is available. -/
theorem strongPathOfSetsToHairyInput_of_appendixA4SplitInput
    {cSplit : ℕ} (hinput : AppendixA4SplitInput.{u} cSplit) :
    StrongPathOfSetsToHairyInput.{u} cSplit := by
  intro V _ _ G ell w hell hw hdegree hP
  rcases hP with ⟨P⟩
  have hell_pos : 0 < ell := lt_trans Nat.zero_lt_one hell
  have hw_pos : 0 < w := lt_trans Nat.zero_lt_one hw
  rcases hinput G P hell_pos hw_pos hdegree with ⟨D⟩
  exact ⟨D.toHairyPathOfSetsSystem hell_pos hw_pos⟩

/-- Appendix A.2 with all non-arithmetic graph-theoretic ingredients exposed as
explicit inputs.  The proof absorbs the doubled length into the constant:
`(2 * ell)^50 = 2^50 * ell^50`. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    (hinputs :
      ∃ cStrong cStrongLog cSplit : ℕ,
        0 < cStrong ∧ 0 < cStrongLog ∧ 0 < cSplit ∧
          DegreeThreeStrongPathOfSetsInput.{u} cStrong cStrongLog cSplit ∧
            StrongPathOfSetsToHairyInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hinputs with
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hstrong, htoHairy⟩
  refine ⟨cStrong * cSplit * 2 ^ 50, cStrongLog, ?_, hcStrongLog, ?_⟩
  · positivity
  · intro V _ _ G ell w k hell hw hk htw hlarge
    have hscaled :
        cStrong * (cSplit * w) * (2 * ell) ^ 50 *
            (Nat.log 2 k) ^ cStrongLog < k := by
      have hscale_eq :
          cStrong * (cSplit * w) * (2 * ell) ^ 50 *
              (Nat.log 2 k) ^ cStrongLog =
            (cStrong * cSplit * 2 ^ 50) * w * ell ^ 50 *
              (Nat.log 2 k) ^ cStrongLog := by
        rw [Nat.mul_pow]
        ring
      simpa [hscale_eq] using hlarge
    rcases hstrong G hell hw hk htw hscaled with ⟨H, hHG, hdegree, hP⟩
    exact ⟨H, hHG, hdegree, htoHairy H hell hw hdegree hP⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier, the
reduced Chekuri--Chuzhoy A.2 route, and the Appendix A.4 split-cluster input.

This is the proof-facing replacement for the broad Theorem 2.3 contract along
the route currently formalized in this repository. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_cutCore_route_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
      (cSplit := cSplit) hcSplit hsparseInput hcut hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier, the
cut-well-linked Theorem 2.21 boundary, the faithful direct Section 4 path
route, and the Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_cutCore_pathRoute_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseInput hcut hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
tree-of-sets route, and the Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_route_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the faithful
direct Section 4 path route, and the Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, Theorem 4.6 extraction, and the Appendix A.4
split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hextract with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the split proof of Theorem 4.6, and the Appendix A.4
split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_leafExtraction_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hdichotomy hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from the degree-three sparsifier,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the proved finite-tree dichotomy, the DFS/many-leaves
branch of Theorem 4.6, and the Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      (cSplit := cSplit) hcSplit hsparseInput hroutable hcutMatching
      hbuild hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the faithful direct Section 4 path route, and the Appendix A.4 split-cluster
input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching hroute with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from Theorem A.1 in its paper-shaped Omega
form, the bundled explicit Chekuri--Chuzhoy A.2 source inputs, and the
Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_theoremA2SourceInputs_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_theoremA2SourceInputs
      (cSplit := cSplit) hcSplit hsparseOmega hA2 with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, Theorem 4.6 extraction, and the
Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hextract with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, the split proof of Theorem 4.6, and
the Appendix A.4 split-cluster input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_leafExtraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hdichotomy hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩

/-- Treewidth-to-hairy path-of-sets from Theorem A.1 in its paper-shaped
Omega form, Lemma 2.17 routability, the cut-matching/AARV embedding source,
the Section 4 strong-tree construction, the proved finite-tree dichotomy, the
DFS/many-leaves branch of Theorem 4.6, and the Appendix A.4 split-cluster
input. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧ AppendixA4SplitInput.{u} cSplit) :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 50 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  rcases hsplit with ⟨cSplit, hcSplit, hsplitInput⟩
  rcases
    exists_degreeThreeStrongPathOfSetsInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      (cSplit := cSplit) hcSplit hsparseOmega hroutable hcutMatching
      hbuild hleaf with
    ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hdegreeInput⟩
  exact exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
    ⟨cStrong, cStrongLog, cSplit, hcStrong, hcStrongLog, hcSplit,
      hdegreeInput,
      strongPathOfSetsToHairyInput_of_appendixA4SplitInput hsplitInput⟩


end HairyPathOfSetsTheorem
end SimpleGraph

end Lax17Proofs
