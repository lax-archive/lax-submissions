import Mathlib.Tactic
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Stitched rows for the Chekuri--Chuzhoy path-of-sets theorem

This module contains the interface data extracted from Chekuri--Chuzhoy,
Corollary 3.2, in the form needed by the Appendix C.1 sparse-grid assembly.
It is kept separate from the assembly proof so the contract file can state only
the missing extraction theorem.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- The zero-based index of the `i`th even one-based cluster used in
Chekuri--Chuzhoy Appendix C.  The paper's clusters `S_2, S_4, ...` correspond
to Lean indices `1, 3, ...`. -/
def evenClusterIndex (g : ℕ) (i : Fin (g * (g - 1))) :
    Fin (2 * g * (g - 1)) :=
  ⟨2 * i.1 + 1, by
    have hi : i.1 < g * (g - 1) := i.2
    have hsucc : i.1 + 1 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
    calc
      2 * i.1 + 1 < 2 * (i.1 + 1) := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩

@[simp] theorem evenClusterIndex_val (g : ℕ)
    (i : Fin (g * (g - 1))) :
    (evenClusterIndex g i).1 = 2 * i.1 + 1 := rfl

theorem evenClusterIndex_lt_of_lt {g : ℕ}
    {i j : Fin (g * (g - 1))} (hij : i.1 < j.1) :
    (evenClusterIndex g i).1 < (evenClusterIndex g j).1 := by
  simp [evenClusterIndex]
  omega

theorem evenClusterIndex_injective {g : ℕ} :
    Function.Injective (evenClusterIndex g) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [evenClusterIndex] at hval
  omega

/-- The next even one-based cluster ordinal, when it exists. -/
def nextEvenClusterOrdinal {g : ℕ} (i : Fin (g * (g - 1)))
    (hi : i.1 + 1 < g * (g - 1)) : Fin (g * (g - 1)) :=
  ⟨i.1 + 1, hi⟩

@[simp] theorem nextEvenClusterOrdinal_val {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (nextEvenClusterOrdinal i hi).1 = i.1 + 1 := rfl

/-- The last even one-based cluster ordinal, when the path-of-sets system has
at least one even one-based cluster. -/
def lastEvenClusterOrdinal {g : ℕ} (hN : 0 < g * (g - 1)) :
    Fin (g * (g - 1)) :=
  ⟨g * (g - 1) - 1, Nat.sub_lt hN (by decide : 0 < 1)⟩

@[simp] theorem lastEvenClusterOrdinal_val {g : ℕ}
    (hN : 0 < g * (g - 1)) :
    (lastEvenClusterOrdinal hN).1 = g * (g - 1) - 1 := rfl

/-- The last even one-based cluster is exactly the last cluster of a
`2 * g * (g - 1)`-long path-of-sets system. -/
theorem evenClusterIndex_lastEven_eq_lastIndex {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) :
    evenClusterIndex g (lastEvenClusterOrdinal hN) = P.lastIndex := by
  apply Fin.ext
  dsimp [lastEvenClusterOrdinal, evenClusterIndex, PathOfSetsSystem.lastIndex]
  rw [Nat.mul_assoc]
  set N := g * (g - 1)
  have hN_one : 1 ≤ N := by
    simpa [N] using Nat.succ_le_of_lt hN
  omega

/-- The odd one-based cluster lying immediately after an even one-based
cluster.  In Lean's zero-based indexing this is the cluster after
`evenClusterIndex g i`. -/
def oddClusterAfterEvenIndex (g : ℕ) (i : Fin (g * (g - 1)))
    (hi : i.1 + 1 < g * (g - 1)) :
    Fin (2 * g * (g - 1)) :=
  ⟨2 * i.1 + 2, by
    have hmul : 2 * (i.1 + 1) < 2 * (g * (g - 1)) :=
      Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
    calc
      2 * i.1 + 2 = 2 * (i.1 + 1) := by omega
      _ < 2 * (g * (g - 1)) := hmul
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩

@[simp] theorem oddClusterAfterEvenIndex_val (g : ℕ)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (oddClusterAfterEvenIndex g i hi).1 = 2 * i.1 + 2 := rfl

/-- Every cluster is either the first cluster, an even one-based cluster, or
the intervening odd cluster following a nonfinal even one-based cluster. -/
theorem clusterIndex_cases {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (k : Fin (2 * g * (g - 1))) :
    k = P.firstIndex ∨
      (∃ i : Fin (g * (g - 1)), k = evenClusterIndex g i) ∨
      ∃ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
        k = oddClusterAfterEvenIndex g i hi := by
  let N := g * (g - 1)
  have hklt : k.1 < 2 * N := by
    simpa [N, Nat.mul_assoc] using k.2
  by_cases hkzero : k.1 = 0
  · left
    apply Fin.ext
    simpa using hkzero
  · right
    by_cases hkodd : k.1 % 2 = 1
    · left
      let i : Fin N := ⟨k.1 / 2, by omega⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      simp [i, evenClusterIndex]
      omega
    · right
      have hkeven : k.1 % 2 = 0 := by omega
      let i : Fin N := ⟨k.1 / 2 - 1, by omega⟩
      have hi : i.1 + 1 < N := by
        dsimp [i]
        omega
      refine ⟨i, hi, ?_⟩
      apply Fin.ext
      simp [i, oddClusterAfterEvenIndex]
      omega

/-- The cluster after the odd cluster between two consecutive even one-based
clusters is the next even one-based cluster. -/
theorem oddClusterAfterEvenIndex_succ_eq_nextEven (g : ℕ)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (⟨(oddClusterAfterEvenIndex g i hi).1 + 1, by
      have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
      calc
        (oddClusterAfterEvenIndex g i hi).1 + 1 = 2 * i.1 + 3 := by
          simp [oddClusterAfterEvenIndex]
        _ < 2 * (i.1 + 2) := by omega
        _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
        _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩ : Fin (2 * g * (g - 1))) =
      evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
  apply Fin.ext
  simp [oddClusterAfterEvenIndex, nextEvenClusterOrdinal, evenClusterIndex]
  omega

/-- A cluster no later than the next even one-based cluster is either in the
completed prefix, the intervening odd cluster, or that next even cluster. -/
theorem clusterIndex_le_nextEven_cases {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1))
    (k : Fin (2 * g * (g - 1)))
    (hk : k.1 ≤
      (evenClusterIndex g (nextEvenClusterOrdinal i hi)).1) :
    k.1 ≤ (evenClusterIndex g i).1 ∨
      k = oddClusterAfterEvenIndex g i hi ∨
      k = evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
  by_cases hold : k.1 ≤ (evenClusterIndex g i).1
  · exact Or.inl hold
  · right
    by_cases hodd : k.1 = (oddClusterAfterEvenIndex g i hi).1
    · exact Or.inl (Fin.ext hodd)
    · exact Or.inr (Fin.ext (by
        simp [evenClusterIndex, nextEvenClusterOrdinal,
          oddClusterAfterEvenIndex] at hk hold hodd ⊢
        omega))

/-- A cluster strictly before the next even one-based cluster is either in the
completed prefix or is the intervening odd cluster. -/
theorem clusterIndex_lt_nextEven_cases {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1))
    (k : Fin (2 * g * (g - 1)))
    (hk : k.1 <
      (evenClusterIndex g (nextEvenClusterOrdinal i hi)).1) :
    k.1 ≤ (evenClusterIndex g i).1 ∨
      k = oddClusterAfterEvenIndex g i hi := by
  by_cases hold : k.1 ≤ (evenClusterIndex g i).1
  · exact Or.inl hold
  · exact Or.inr (Fin.ext (by
      simp [evenClusterIndex, nextEvenClusterOrdinal,
        oddClusterAfterEvenIndex] at hk hold ⊢
      omega))

/-- The gap from an even one-based cluster to the following odd one-based
cluster exists whenever the next even one-based cluster exists. -/
theorem evenClusterIndex_succ_lt_length {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (evenClusterIndex g i).1 + 1 < 2 * g * (g - 1) := by
  dsimp [evenClusterIndex]
  calc
    2 * i.1 + 1 + 1 = 2 * (i.1 + 1) := by omega
    _ < 2 * (g * (g - 1)) :=
      Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The gap from the odd one-based cluster after an even one to the next even
one-based cluster exists whenever the next even ordinal exists. -/
theorem oddClusterAfterEvenIndex_succ_lt_length {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (oddClusterAfterEvenIndex g i hi).1 + 1 < 2 * g * (g - 1) := by
  have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
  calc
    (oddClusterAfterEvenIndex g i hi).1 + 1 = 2 * i.1 + 3 := by
      simp [oddClusterAfterEvenIndex]
    _ < 2 * (i.1 + 2) := by omega
    _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The first connector gap exists when there is at least one even one-based
cluster. -/
theorem firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (_hN : 0 < g * (g - 1)) :
    P.firstIndex.1 + 1 < 2 * g * (g - 1) := by
  calc
    P.firstIndex.1 + 1 = 1 := by simp [PathOfSetsSystem.firstIndex]
    _ < 2 * (g * (g - 1)) := by omega
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The vertex region used by the initial stitching paths. -/
noncomputable def firstStitchingRegion {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) : Finset V :=
  P.cluster P.firstIndex ∪
    (P.connector P.firstIndex
      (firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
        P.toPathOfSetsSystem hN)).toPathPacking.vertexSet

/-- The vertex region used to stitch between two consecutive even one-based
clusters. -/
noncomputable def betweenStitchingRegion {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    Finset V :=
  (P.connector (evenClusterIndex g i)
      (evenClusterIndex_succ_lt_length i hi)).toPathPacking.vertexSet ∪
    (P.cluster (oddClusterAfterEvenIndex g i hi) ∪
      (P.connector (oddClusterAfterEvenIndex g i hi)
        (oddClusterAfterEvenIndex_succ_lt_length i hi)).toPathPacking.vertexSet)

/-- Embed an index strictly before `i` back into the full path-of-sets index
type.  Using `Fin i.1` gives the strict prefix a canonical finite index type. -/
def earlierPathOfSetsIndex {ell : ℕ} (i : Fin ell) (j : Fin i.1) : Fin ell :=
  ⟨j.1, lt_trans j.2 i.2⟩

/-- Every index strictly before `i` starts a connector gap. -/
def earlierPathOfSetsIndex_gap {ell : ℕ} (i : Fin ell) (j : Fin i.1) :
    (earlierPathOfSetsIndex i j).1 + 1 < ell :=
  lt_of_le_of_lt (Nat.succ_le_iff.mpr j.2) i.2

/-- All clusters strictly before `i`, together with all connectors whose source
index is strictly before `i`. -/
noncomputable def strictStitchingPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) : Finset V :=
  (Finset.univ.biUnion fun j : Fin i.1 =>
      P.cluster (earlierPathOfSetsIndex i j)) ∪
    (Finset.univ.biUnion fun j : Fin i.1 =>
      (P.connector (earlierPathOfSetsIndex i j)
        (earlierPathOfSetsIndex_gap i j)).toPathPacking.vertexSet)

/-- The full path-of-sets region through cluster `i`. -/
noncomputable def stitchingPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell) : Finset V :=
  strictStitchingPrefixRegion P i ∪ P.cluster i

theorem cluster_subset_strictStitchingPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) {i j : Fin ell}
    (hji : j.1 < i.1) :
    P.cluster j ⊆ strictStitchingPrefixRegion P i := by
  classical
  intro v hv
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨⟨j.1, hji⟩, by simp,
    by simpa [earlierPathOfSetsIndex] using hv⟩

theorem connector_subset_strictStitchingPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) {i j : Fin ell}
    (hj : j.1 + 1 < ell) (hji : j.1 < i.1) :
    (P.connector j hj).toPathPacking.vertexSet ⊆
      strictStitchingPrefixRegion P i := by
  classical
  intro v hv
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨j.1, hji⟩, by simp, ?_⟩
  simpa [earlierPathOfSetsIndex] using hv

/-- A region through `i` is part of the strict region before every later
cluster `j`. -/
theorem stitchingPrefixRegion_subset_strict_of_lt
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) {i j : Fin ell}
    (hij : i.1 < j.1) :
    stitchingPrefixRegion P i ⊆ strictStitchingPrefixRegion P j := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvStrict | hvCluster
  · rcases Finset.mem_union.mp hvStrict with hvClusters | hvConnectors
    · rcases Finset.mem_biUnion.mp hvClusters with ⟨k, _hk, hvK⟩
      apply Finset.mem_union_left
      refine Finset.mem_biUnion.mpr
        ⟨⟨k.1, lt_trans k.2 hij⟩, by simp, ?_⟩
      simpa [earlierPathOfSetsIndex] using hvK
    · rcases Finset.mem_biUnion.mp hvConnectors with ⟨k, _hk, hvK⟩
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr
        ⟨⟨k.1, lt_trans k.2 hij⟩, by simp, ?_⟩
      simpa [earlierPathOfSetsIndex] using hvK
  · exact cluster_subset_strictStitchingPrefixRegion P hij hvCluster

theorem stitchingPrefixRegion_mono_of_lt
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) {i j : Fin ell}
    (hij : i.1 < j.1) :
    stitchingPrefixRegion P i ⊆ stitchingPrefixRegion P j := by
  intro v hv
  exact Finset.mem_union_left _
    (stitchingPrefixRegion_subset_strict_of_lt P hij hv)

/-- A path-of-sets prefix is disjoint from every later cluster. -/
theorem stitchingPrefixRegion_disjoint_cluster_of_lt
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : StrongPathOfSetsSystem G ell w) {i k : Fin ell}
    (hik : i.1 < k.1) :
    Disjoint (stitchingPrefixRegion P i) (P.cluster k) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPrefix hvK
  rcases Finset.mem_union.mp hvPrefix with hvStrict | hvI
  · rcases Finset.mem_union.mp hvStrict with hvClusters | hvConnectors
    · rcases Finset.mem_biUnion.mp hvClusters with ⟨j, _hj, hvJ⟩
      have hjk : earlierPathOfSetsIndex i j ≠ k := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      exact Finset.disjoint_left.mp (P.cluster_disjoint hjk) hvJ hvK
    · rcases Finset.mem_biUnion.mp hvConnectors with ⟨j, _hj, hvJ⟩
      have hk_ne_j : k ≠ earlierPathOfSetsIndex i j := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      have hk_ne_next :
          k ≠ ⟨(earlierPathOfSetsIndex i j).1 + 1,
            earlierPathOfSetsIndex_gap i j⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne
          (earlierPathOfSetsIndex i j) (earlierPathOfSetsIndex_gap i j)
          k hk_ne_j hk_ne_next)
        hvJ hvK
  · have hik_ne : i ≠ k := by
      intro h
      have hval := congrArg Fin.val h
      omega
    exact Finset.disjoint_left.mp (P.cluster_disjoint hik_ne) hvI hvK

/-- The specialized initial region lies in the generic region through the
first even one-based cluster. -/
theorem firstStitchingRegion_subset_prefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) :
    firstStitchingRegion P hN ⊆
      stitchingPrefixRegion P (evenClusterIndex g ⟨0, hN⟩) := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvCluster | hvConnector
  · exact Finset.mem_union_left _
      (cluster_subset_strictStitchingPrefixRegion P (by
        simp [PathOfSetsSystem.firstIndex, evenClusterIndex]) hvCluster)
  · exact Finset.mem_union_left _
      (connector_subset_strictStitchingPrefixRegion P
        (firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
          P.toPathOfSetsSystem hN)
        (by simp [PathOfSetsSystem.firstIndex, evenClusterIndex])
        (by simpa [firstStitchingRegion] using hvConnector))

/-- A two-gap region lies in the generic prefix through its target even
cluster. -/
theorem betweenStitchingRegion_subset_nextPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    betweenStitchingRegion P i hi ⊆
      stitchingPrefixRegion P
        (evenClusterIndex g (nextEvenClusterOrdinal i hi)) := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvConnEven | hvRest
  · exact Finset.mem_union_left _
      (connector_subset_strictStitchingPrefixRegion P
        (evenClusterIndex_succ_lt_length i hi)
        (by simp [evenClusterIndex, nextEvenClusterOrdinal])
        hvConnEven)
  · rcases Finset.mem_union.mp hvRest with hvOdd | hvConnOdd
    · exact Finset.mem_union_left _
        (cluster_subset_strictStitchingPrefixRegion P
          (by
            simp [oddClusterAfterEvenIndex, evenClusterIndex,
              nextEvenClusterOrdinal]
            omega)
          hvOdd)
    · exact Finset.mem_union_left _
        (connector_subset_strictStitchingPrefixRegion P
          (oddClusterAfterEvenIndex_succ_lt_length i hi)
          (by
            simp [oddClusterAfterEvenIndex, evenClusterIndex,
              nextEvenClusterOrdinal]
            omega)
          hvConnOdd)

/-- The region used between consecutive even clusters is disjoint from the
strict path-of-sets region before its source even cluster. -/
theorem betweenStitchingRegion_disjoint_strictPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    Disjoint (betweenStitchingRegion P i hi)
      (strictStitchingPrefixRegion P (evenClusterIndex g i)) := by
  classical
  let e := evenClusterIndex g i
  let odd := oddClusterAfterEvenIndex g i hi
  let he := evenClusterIndex_succ_lt_length i hi
  let hodd := oddClusterAfterEvenIndex_succ_lt_length i hi
  rw [Finset.disjoint_left]
  intro v hvBetween hvEarlier
  rcases Finset.mem_union.mp hvBetween with hvConnE | hvRest
  · rcases Finset.mem_union.mp hvEarlier with hvClusters | hvConnectors
    · rcases Finset.mem_biUnion.mp hvClusters with ⟨j, _hj, hvCluster⟩
      have hj_ne_e : earlierPathOfSetsIndex e j ≠ e := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      have hj_ne_next :
          earlierPathOfSetsIndex e j ≠ ⟨e.1 + 1, he⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne e he
          (earlierPathOfSetsIndex e j) hj_ne_e hj_ne_next)
        (by simpa [betweenStitchingRegion, e, he] using hvConnE) hvCluster
    · rcases Finset.mem_biUnion.mp hvConnectors with ⟨j, _hj, hvConn⟩
      have he_ne_j : e ≠ earlierPathOfSetsIndex e j := by
        intro h
        have hval := congrArg Fin.val h
        simp [earlierPathOfSetsIndex] at hval
        omega
      exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint he
            (earlierPathOfSetsIndex_gap e j) he_ne_j))
        (by simpa [betweenStitchingRegion, e, he] using hvConnE) hvConn
  · rcases Finset.mem_union.mp hvRest with hvOdd | hvConnOdd
    · rcases Finset.mem_union.mp hvEarlier with hvClusters | hvConnectors
      · rcases Finset.mem_biUnion.mp hvClusters with ⟨j, _hj, hvCluster⟩
        have hodd_ne_j : odd ≠ earlierPathOfSetsIndex e j := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        exact Finset.disjoint_left.mp (P.cluster_disjoint hodd_ne_j)
          (by simpa [betweenStitchingRegion, odd] using hvOdd) hvCluster
      · rcases Finset.mem_biUnion.mp hvConnectors with ⟨j, _hj, hvConn⟩
        have hodd_ne_j : odd ≠ earlierPathOfSetsIndex e j := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        have hodd_ne_next :
            odd ≠ ⟨(earlierPathOfSetsIndex e j).1 + 1,
              earlierPathOfSetsIndex_gap e j⟩ := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        exact Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne
            (earlierPathOfSetsIndex e j) (earlierPathOfSetsIndex_gap e j)
            odd hodd_ne_j hodd_ne_next).symm
          (by simpa [betweenStitchingRegion, odd] using hvOdd) hvConn
    · rcases Finset.mem_union.mp hvEarlier with hvClusters | hvConnectors
      · rcases Finset.mem_biUnion.mp hvClusters with ⟨j, _hj, hvCluster⟩
        have hj_ne_odd : earlierPathOfSetsIndex e j ≠ odd := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        have hj_ne_next :
            earlierPathOfSetsIndex e j ≠ ⟨odd.1 + 1, hodd⟩ := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        exact Finset.disjoint_left.mp
          (P.connector_vertexSet_disjoint_cluster_of_ne odd hodd
            (earlierPathOfSetsIndex e j) hj_ne_odd hj_ne_next)
          (by simpa [betweenStitchingRegion, odd, hodd] using hvConnOdd)
          hvCluster
      · rcases Finset.mem_biUnion.mp hvConnectors with ⟨j, _hj, hvConn⟩
        have hodd_ne_j : odd ≠ earlierPathOfSetsIndex e j := by
          intro h
          have hval := congrArg Fin.val h
          simp [odd, e, oddClusterAfterEvenIndex, evenClusterIndex,
            earlierPathOfSetsIndex] at hval
          omega
        exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (P.connector_mutually_nodeDisjoint hodd
              (earlierPathOfSetsIndex_gap e j) hodd_ne_j))
          (by simpa [betweenStitchingRegion, odd, hodd] using hvConnOdd)
          hvConn

/-- The old prefix, the next two-gap region, and the next even cluster all lie
in the generic prefix through that next even cluster. -/
theorem stitchingStepRegion_subset_nextPrefixRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    ((stitchingPrefixRegion P (evenClusterIndex g i) ∪
        betweenStitchingRegion P i hi) ∪
      P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) ⊆
        stitchingPrefixRegion P
          (evenClusterIndex g (nextEvenClusterOrdinal i hi)) := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvOld | hvNext
  · rcases Finset.mem_union.mp hvOld with hvPrefix | hvBetween
    · exact stitchingPrefixRegion_mono_of_lt P
        (evenClusterIndex_lt_of_lt (by simp [nextEvenClusterOrdinal])) hvPrefix
    · exact betweenStitchingRegion_subset_nextPrefixRegion P i hi hvBetween
  · exact Finset.mem_union_right _ hvNext

/-- The first stitching region is disjoint from the region used to stitch from
the first even one-based cluster to the second. -/
theorem betweenStitchingRegion_first_disjoint_firstStitchingRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) (hi : 0 + 1 < g * (g - 1)) :
    Disjoint (betweenStitchingRegion P ⟨0, hN⟩ hi)
      (firstStitchingRegion P hN) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, hN⟩
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let odd : Fin (2 * g * (g - 1)) := oddClusterAfterEvenIndex g first hi
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem hN
  let hgap1 := evenClusterIndex_succ_lt_length first hi
  let hgap2 := oddClusterAfterEvenIndex_succ_lt_length first hi
  have hfirst_ne_e0 : P.firstIndex ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e0, first, evenClusterIndex] at hval
  have he0_ne_first : e0 ≠ P.firstIndex := fun h => hfirst_ne_e0 h.symm
  have hfirst_ne_odd : P.firstIndex ≠ odd := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  have hodd_ne_first : odd ≠ P.firstIndex := fun h => hfirst_ne_odd h.symm
  have hfirst_ne_after_e0 : P.firstIndex ≠ ⟨e0.1 + 1, hgap1⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e0, first, evenClusterIndex] at hval
  have hodd_ne_e0 : odd ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [odd, e0, first, oddClusterAfterEvenIndex, evenClusterIndex] at hval
  have hodd_ne_after_first : odd ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  have hfirst_ne_after_odd : P.firstIndex ≠ ⟨odd.1 + 1, hgap2⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvBetween hvFirst
  simp [betweenStitchingRegion, firstStitchingRegion] at hvBetween hvFirst
  rcases hvBetween with hvConnEven | hvOdd | hvConnOdd
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne e0 hgap1 P.firstIndex
          hfirst_ne_e0 hfirst_ne_after_e0)
        hvConnEven hvFirstCluster
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint hgap1 hgap0 he0_ne_first))
        hvConnEven hvFirstConn
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp (P.cluster_disjoint hodd_ne_first)
        hvOdd hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 odd
          hodd_ne_first hodd_ne_after_first).symm)
        hvOdd hvFirstConn
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne odd hgap2 P.firstIndex
          hfirst_ne_odd hfirst_ne_after_odd)
        hvConnOdd hvFirstCluster
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint hgap2 hgap0 hodd_ne_first))
        hvConnOdd hvFirstConn

/-- The local output obtained by applying Chekuri--Chuzhoy Theorem 3.1 inside
one even one-based cluster: a fixed-size family of disjoint left-to-right paths
inside that cluster, plus pairwise bridges localized to the cluster.

Appendix C stitches these outputs through the intervening odd clusters to
produce the global `StitchedRows` object. -/
structure EvenClusterOutput {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (q : ℕ) where
  /-- The local row pieces returned in the even cluster. -/
  paths : PathPacking G (P.left (evenClusterIndex g i))
    (P.right (evenClusterIndex g i))
  /-- The number of local row pieces. -/
  paths_card : paths.card = q
  /-- The local row pieces stay inside the even cluster. -/
  paths_staysIn :
    paths.StaysIn (P.cluster (evenClusterIndex g i))
  /-- The local bridge guarantee from Chekuri--Chuzhoy Theorem 3.1. -/
  pairwise_bridges :
    paths.HasPairwiseBridgesIn (P.cluster (evenClusterIndex g i))

/-- Local outputs for all even one-based clusters of a path-of-sets system. -/
structure EvenClusterOutputs {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w) (q : ℕ) where
  /-- The local output assigned to each even one-based cluster. -/
  output : ∀ i : Fin (g * (g - 1)), EvenClusterOutput P i q

/-- The exact first-cluster linkage used to construct an initial stitching
packing.

The index map records which path of the full-width left-to-right packing is
retained by each start path.  The trace equality is source-faithful: `leftRight`
is the packing actually concatenated with the first connector, not a linkage
chosen after the start packing has been constructed. -/
structure StartStitchingPackingData {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {T : Finset V}
    (S : PathPacking G (P.left P.firstIndex) T) where
  /-- The full-width left-to-right packing actually used in the first cluster. -/
  leftRight :
    PerfectPathPacking G (P.left P.firstIndex) (P.right P.firstIndex)
  /-- The retained first-cluster linkage has full path-of-sets width. -/
  leftRight_card : leftRight.card = w
  /-- The retained linkage stays inside the first cluster. -/
  leftRight_staysIn :
    leftRight.toPathPacking.StaysIn (P.cluster P.firstIndex)
  /-- The full-width path underlying each target-restricted start path. -/
  indexMap : S.Index → leftRight.Index
  /-- Distinct start paths retain distinct full-width paths. -/
  indexMap_injective : Function.Injective indexMap
  /-- A start path has exactly its retained left-to-right path as its trace in
  the first cluster. -/
  trace_eq :
    ∀ a : S.Index,
      (S.path a).vertexSet ∩ P.cluster P.firstIndex =
        (leftRight.path (indexMap a)).vertexSet

/-- The exact middle-cluster data used to construct a packing between two
consecutive even one-based clusters.

This specializes `StrongPathOfSetsSystem.TwoGapConcatPackingData` to the
Appendix C indexing.  In particular, `middle` is the packing actually used in
`S`, and `trace_eq` identifies its paths with the traces of the collapsed
packing in the intervening odd cluster. -/
structure BetweenStitchingPackingData {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w q : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1))
    {R L : Finset V} (S : PerfectPathPacking G R L) where
  /-- Left terminals selected from the odd cluster's left nails. -/
  Lmid : Finset V
  /-- Right terminals selected from the odd cluster's right nails. -/
  Rmid : Finset V
  /-- The exact perfect packing used inside the intervening odd cluster. -/
  middle : PerfectPathPacking G Lmid Rmid
  /-- The retained middle packing has the row-packing cardinality. -/
  middle_card : middle.card = q
  /-- The selected left middle terminals have the row-packing cardinality. -/
  Lmid_card : Lmid.card = q
  /-- The selected right middle terminals have the row-packing cardinality. -/
  Rmid_card : Rmid.card = q
  /-- The left middle terminals are left nails of the odd cluster. -/
  Lmid_subset : Lmid ⊆ P.left (oddClusterAfterEvenIndex g i hi)
  /-- The right middle terminals are right nails of the odd cluster. -/
  Rmid_subset : Rmid ⊆ P.right (oddClusterAfterEvenIndex g i hi)
  /-- The retained middle packing stays inside the odd cluster. -/
  middle_staysIn :
    middle.toPathPacking.StaysIn
      (P.cluster (oddClusterAfterEvenIndex g i hi))
  /-- Bijection matching each collapsed path to its retained middle path. -/
  indexEquiv : S.Index ≃ middle.Index
  /-- Exact trace of each collapsed path in the intervening odd cluster. -/
  trace_eq :
    ∀ a : S.Index,
      (S.path a).vertexSet ∩ P.cluster (oddClusterAfterEvenIndex g i hi) =
        (middle.path (indexEquiv a)).vertexSet

namespace EvenClusterOutput

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- Consecutive local even-cluster outputs can be stitched through the
intervening odd cluster.

This is the formal local step in Appendix C of Chekuri--Chuzhoy: the target
endpoints used by the first even-cluster output and the source endpoints used
by the next even-cluster output have the same size, so the strong
Path-of-Sets linkage through the two connector gaps and the odd cluster gives
a perfect packing between them. -/
theorem exists_stitchingPacking_to_next
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem i q)
    (E_next :
      EvenClusterOutput P.toPathOfSetsSystem (nextEvenClusterOrdinal i hi) q) :
    ∃ S : PerfectPathPacking G E.paths.targetSet E_next.paths.sourceSet,
      S.card = q ∧
        S.toPathPacking.InternallyDisjointFromSet
          (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  classical
  let e := evenClusterIndex g i
  let eOdd := oddClusterAfterEvenIndex g i hi
  have hOddSucc : eOdd.1 + 1 < 2 * g * (g - 1) := by
    have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
    calc
      eOdd.1 + 1 = 2 * i.1 + 3 := by
        simp [eOdd, oddClusterAfterEvenIndex]
      _ < 2 * (i.1 + 2) := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hnext :
      (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) =
        evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
    simpa [eOdd] using oddClusterAfterEvenIndex_succ_eq_nextEven g i hi
  have hR : E.paths.targetSet ⊆ P.right e := by
    simpa [e] using E.paths.targetSet_subset_right
  have hL :
      E_next.paths.sourceSet ⊆
        P.left
          (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) := by
    intro v hv
    rw [hnext]
    exact E_next.paths.sourceSet_subset_left hv
  have hcard :
      E.paths.targetSet.card = E_next.paths.sourceSet.card := by
    rw [PathPacking.targetSet_card, PathPacking.sourceSet_card,
      E.paths_card, E_next.paths_card]
  rcases P.exists_twoGap_concatPacking_between_subsets e
      (by simpa [eOdd] using (oddClusterAfterEvenIndex g i hi).2)
      hOddSucc
      hR hL hcard with
    ⟨S, hS_card, _hS_stays, hS_first, hS_last⟩
  refine ⟨S, ?_, by simpa [e] using hS_first, ?_⟩
  · exact hS_card.trans (by rw [PathPacking.targetSet_card, E.paths_card])
  · simpa [hnext] using hS_last

/-- Consecutive local even-cluster outputs can be stitched through the
intervening odd cluster, retaining both the collapsed-packing invariants and the
exact middle packing from the same two-gap construction. -/
theorem exists_stitchingPacking_to_next_with_invariants_and_provenance
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem i q)
    (E_next :
      EvenClusterOutput P.toPathOfSetsSystem (nextEvenClusterOrdinal i hi) q) :
    ∃ S : PerfectPathPacking G E.paths.targetSet E_next.paths.sourceSet,
      Nonempty (BetweenStitchingPackingData (q := q) P i hi S) ∧
        S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
            S.toPathPacking.InternallyDisjointFromSet
              (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  classical
  let e := evenClusterIndex g i
  let eOdd := oddClusterAfterEvenIndex g i hi
  have heOdd :
      e.1 + 1 < 2 * g * (g - 1) := by
    dsimp [e, evenClusterIndex]
    calc
      2 * i.1 + 1 + 1 = 2 * (i.1 + 1) := by omega
      _ < 2 * (g * (g - 1)) :=
        Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hOddSucc : eOdd.1 + 1 < 2 * g * (g - 1) := by
    have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
    calc
      eOdd.1 + 1 = 2 * i.1 + 3 := by
        simp [eOdd, oddClusterAfterEvenIndex]
      _ < 2 * (i.1 + 2) := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hnext :
      (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) =
        evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
    simpa [eOdd] using oddClusterAfterEvenIndex_succ_eq_nextEven g i hi
  have heOdd_eq :
      (⟨e.1 + 1, heOdd⟩ : Fin (2 * g * (g - 1))) = eOdd := by
    apply Fin.ext
    simp [e, eOdd, evenClusterIndex, oddClusterAfterEvenIndex]
  have hR : E.paths.targetSet ⊆ P.right e := by
    simpa [e] using E.paths.targetSet_subset_right
  have hL :
      E_next.paths.sourceSet ⊆
        P.left
          (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) := by
    intro v hv
    rw [hnext]
    exact E_next.paths.sourceSet_subset_left hv
  have hcard :
      E.paths.targetSet.card = E_next.paths.sourceSet.card := by
    rw [PathPacking.targetSet_card, PathPacking.sourceSet_card,
      E.paths_card, E_next.paths_card]
  rcases P.exists_twoGap_concatPackingData_between_subsets e heOdd hOddSucc
      hR hL hcard with
    ⟨S, ⟨D⟩⟩
  have hS_card : S.card = q :=
    D.card_eq.trans (by rw [PathPacking.targetSet_card, E.paths_card])
  have hmiddle_card : D.middle.card = q :=
    D.middle_card_eq.trans (by rw [PathPacking.targetSet_card, E.paths_card])
  refine ⟨S, ⟨{
    Lmid := D.Lmid
    Rmid := D.Rmid
    middle := D.middle
    middle_card := hmiddle_card
    Lmid_card := D.middle.card_eq_left_card.symm.trans hmiddle_card
    Rmid_card := D.middle.card_eq_right_card.symm.trans hmiddle_card
    Lmid_subset := by simpa [heOdd_eq] using D.Lmid_subset
    Rmid_subset := by simpa [heOdd_eq] using D.Rmid_subset
    middle_staysIn := by simpa [heOdd_eq] using D.middle_staysIn
    indexEquiv := D.indexEquiv
    trace_eq := by
      intro a
      simpa [heOdd_eq] using D.trace_eq a
  }⟩, hS_card, ?_, by simpa [e] using D.internallyDisjoint_left, ?_⟩
  · simpa [betweenStitchingRegion, e, eOdd, heOdd_eq, hnext] using D.staysIn
  · simpa [hnext] using D.internallyDisjoint_right

/-- Consecutive local even-cluster outputs can be stitched through the
intervening odd cluster, with the full region and endpoint-cluster separation
certificates retained.

This compatibility projection omits the exact middle-packing provenance
retained by
`exists_stitchingPacking_to_next_with_invariants_and_provenance`. -/
theorem exists_stitchingPacking_to_next_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem i q)
    (E_next :
      EvenClusterOutput P.toPathOfSetsSystem (nextEvenClusterOrdinal i hi) q) :
    ∃ S : PerfectPathPacking G E.paths.targetSet E_next.paths.sourceSet,
      S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
            S.toPathPacking.InternallyDisjointFromSet
              (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  rcases E.exists_stitchingPacking_to_next_with_invariants_and_provenance
      P hi E_next with ⟨S, _hprovenance, hcard, hstays, hleft, hright⟩
  exact ⟨S, hcard, hstays, hleft, hright⟩

/-- The first local output can be connected back to the first left nail set,
retaining the exact full-width linkage used in the first cluster.

This constructs the one-step linkage directly from `Q` and the first
connector, then restricts its targets to the local source set.  Consequently
the provenance index and trace equality refer to the same `Q` that occurs in
the start paths. -/
theorem exists_startPacking_to_first_with_invariants_and_provenance
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem ⟨0, hN⟩ q) :
    ∃ S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet,
      Nonempty (StartStitchingPackingData P S) ∧
        S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) := by
  classical
  let firstEven : Fin (g * (g - 1)) := ⟨0, hN⟩
  let hgap := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem hN
  have hfirstEven :
      (⟨P.firstIndex.1 + 1, hgap⟩ : Fin (2 * g * (g - 1))) =
        evenClusterIndex g firstEven := by
    apply Fin.ext
    simp [PathOfSetsSystem.firstIndex, firstEven, evenClusterIndex]
  rcases P.exists_left_right_perfect_linkage P.firstIndex with
    ⟨Q, hQcard, hQstay⟩
  let hpath :=
    P.left_right_connector_concat_isPath P.firstIndex hgap Q hQstay
  let hnode :=
    P.left_right_connector_concat_nodeDisjoint P.firstIndex hgap Q hQstay hpath
  let L : PerfectPathPacking G (P.left P.firstIndex)
      (P.left ⟨P.firstIndex.1 + 1, hgap⟩) :=
    Q.concat (P.connector P.firstIndex hgap) hpath hnode
  have hT :
      E.paths.sourceSet ⊆ P.left ⟨P.firstIndex.1 + 1, hgap⟩ := by
    intro v hv
    rw [hfirstEven]
    exact E.paths.sourceSet_subset_left hv
  let R : PerfectPathPacking G
      (L.sourceSet (L.targetIndexSetOfSubset E.paths.sourceSet))
      E.paths.sourceSet :=
    L.restrictTargetSet E.paths.sourceSet hT
  have hRsource :
      L.sourceSet (L.targetIndexSetOfSubset E.paths.sourceSet) ⊆
        P.left P.firstIndex := by
    exact L.sourceSet_subset_left (L.targetIndexSetOfSubset E.paths.sourceSet)
  let S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet :=
    R.toPathPacking.widenTerminals hRsource (by intro v hv; exact hv)
  have hLstay :
      L.toPathPacking.StaysIn
        (P.cluster P.firstIndex ∪
          (P.connector P.firstIndex hgap).toPathPacking.vertexSet) := by
    exact P.left_right_connector_concat_staysIn P.firstIndex hgap Q hQstay
      hpath hnode
  have hRstay :
      R.toPathPacking.StaysIn
        (P.cluster P.firstIndex ∪
          (P.connector P.firstIndex hgap).toPathPacking.vertexSet) := by
    exact L.restrictTargetSet_staysIn E.paths.sourceSet hT hLstay
  have hLinternal :
      L.toPathPacking.InternallyDisjointFromSet
        (P.cluster ⟨P.firstIndex.1 + 1, hgap⟩) := by
    exact P.left_right_connector_concat_internallyDisjoint_nextCluster
      P.firstIndex hgap Q hQstay hpath hnode
  have hRinternal :
      R.toPathPacking.InternallyDisjointFromSet
        (P.cluster ⟨P.firstIndex.1 + 1, hgap⟩) := by
    exact L.restrictTargetSet_internallyDisjointFromSet E.paths.sourceSet hT
      hLinternal
  refine ⟨S, ⟨{
    leftRight := Q
    leftRight_card := hQcard
    leftRight_staysIn := hQstay
    indexMap := fun a => a.1
    indexMap_injective := Subtype.val_injective
    trace_eq := by
      intro a
      simpa [S, R, L, PathPacking.widenTerminals,
        PerfectPathPacking.restrictTargetSet,
        PerfectPathPacking.copyTerminals,
        PerfectPathPacking.restrictIndexSet,
        PerfectPathPacking.concat] using
        P.left_right_connector_append_inter_current_cluster_eq
          P.firstIndex hgap Q hQstay hpath a.1
  }⟩, ?_, ?_, ?_⟩
  · calc
      S.card = R.card := rfl
      _ = E.paths.sourceSet.card := by simp [R, L]
      _ = E.paths.card := by rw [PathPacking.sourceSet_card]
      _ = q := E.paths_card
  · intro a v hv
    have hvR : v ∈ (R.path a).vertexSet := by simpa [S] using hv
    simpa [firstStitchingRegion, hgap] using hRstay a hvR
  · intro a v hv hvC
    have hvR : v ∈ (R.path a).vertexSet := by simpa [S] using hv
    exact hRinternal a hvR (by simpa [hfirstEven, firstEven] using hvC)

/-- Compatibility projection of the provenance-aware initial producer. -/
theorem exists_startPacking_to_first_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem ⟨0, hN⟩ q) :
    ∃ S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet,
      S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) := by
  rcases E.exists_startPacking_to_first_with_invariants_and_provenance P hN with
    ⟨S, _hprovenance, hcard, hstays, hinternal⟩
  exact ⟨S, hcard, hstays, hinternal⟩

/-- Compatibility projection retaining the original cardinality-only type. -/
theorem exists_startPacking_to_first
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem ⟨0, hN⟩ q) :
    ∃ S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet,
      S.card = q := by
  rcases E.exists_startPacking_to_first_with_invariants P hN with
    ⟨S, hcard, _hstays, _hinternal⟩
  exact ⟨S, hcard⟩

/-- The last local even-cluster output can be viewed as ending in the last
right nail set of the whole path-of-sets system.

This is the terminal bookkeeping step in Appendix C: the last even one-based
cluster is the final cluster of the `2 * g * (g - 1)`-cluster system, so no
additional connector is needed after the last local output. -/
def toLastRight
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex) :=
  E.paths.widenTerminals (by intro v hv; exact hv) (by
    intro v hv
    rw [← evenClusterIndex_lastEven_eq_lastIndex P hN]
    exact hv)

@[simp] theorem toLastRight_card
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).card = q := by
  simpa [toLastRight] using E.paths_card

theorem toLastRight_staysIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).StaysIn (P.cluster P.lastIndex) := by
  intro i v hv
  have hvE : v ∈ (E.paths.path i).vertexSet := by
    simpa [toLastRight, PathPacking.widenTerminals] using hv
  have hstay := E.paths_staysIn i hvE
  simpa [evenClusterIndex_lastEven_eq_lastIndex P hN] using hstay

theorem toLastRight_hasPairwiseBridgesIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).HasPairwiseBridgesIn (P.cluster P.lastIndex) := by
  simpa [toLastRight, evenClusterIndex_lastEven_eq_lastIndex P hN] using
    E.paths.widenTerminals_hasPairwiseBridgesIn
      (by intro v hv; exact hv)
      (by
        intro v hv
        rw [← evenClusterIndex_lastEven_eq_lastIndex P hN]
        exact hv)
      E.pairwise_bridges

end EvenClusterOutput

namespace EvenClusterOutputs

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- Consecutive entries in a family of local even-cluster outputs can be
stitched through the odd one-based cluster between them. -/
theorem exists_stitchingPacking_to_next
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1)) :
    ∃ S : PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet),
      S.card = q ∧
        S.toPathPacking.InternallyDisjointFromSet
          (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  (E.output i).exists_stitchingPacking_to_next P hi
    (E.output (nextEvenClusterOrdinal i hi))

/-- Consecutive entries in a family of local even-cluster outputs can be
stitched through the intervening odd cluster, retaining the full two-gap region,
separation certificates, and exact middle-packing provenance. -/
theorem exists_stitchingPacking_to_next_with_invariants_and_provenance
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1)) :
    ∃ S : PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet),
      Nonempty (BetweenStitchingPackingData (q := q) P i hi S) ∧
        S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  (E.output i).exists_stitchingPacking_to_next_with_invariants_and_provenance P hi
    (E.output (nextEvenClusterOrdinal i hi))

/-- Consecutive entries in a family of local even-cluster outputs can be
stitched through the intervening odd cluster, retaining the full two-gap region
and separation certificates. -/
theorem exists_stitchingPacking_to_next_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1)) :
    ∃ S : PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet),
      S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  rcases E.exists_stitchingPacking_to_next_with_invariants_and_provenance P hi with
    ⟨S, _hprovenance, hcard, hstays, hleft, hright⟩
  exact ⟨S, hcard, hstays, hleft, hright⟩

/-- The first local output in a family can be connected back to the first left
nail set of the whole path-of-sets system. -/
theorem exists_startPacking_to_first
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    ∃ S : PathPacking G (P.left P.firstIndex)
        ((E.output ⟨0, hN⟩).paths.sourceSet),
      S.card = q :=
  (E.output ⟨0, hN⟩).exists_startPacking_to_first P hN

/-- The first local output in a family can be connected back to the first left
nail set of the whole path-of-sets system, retaining region and separation
certificates. -/
theorem exists_startPacking_to_first_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    ∃ S : PathPacking G (P.left P.firstIndex)
        ((E.output ⟨0, hN⟩).paths.sourceSet),
      S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) :=
  (E.output ⟨0, hN⟩).exists_startPacking_to_first_with_invariants P hN

/-- The family-level initial producer retaining the exact first-cluster
left-to-right linkage used by every start path. -/
theorem exists_startPacking_to_first_with_invariants_and_provenance
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    ∃ S : PathPacking G (P.left P.firstIndex)
        ((E.output ⟨0, hN⟩).paths.sourceSet),
      Nonempty (StartStitchingPackingData P S) ∧
        S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) :=
  (E.output ⟨0, hN⟩).exists_startPacking_to_first_with_invariants_and_provenance
    P hN

/-- The last local output in a family can be viewed as ending in the last right
nail set of the whole path-of-sets system. -/
def toLastRight
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight P hN

@[simp] theorem toLastRight_card
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).card = q := by
  simp [toLastRight,
    (E.output (lastEvenClusterOrdinal hN)).toLastRight_card P hN]

theorem toLastRight_staysIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).StaysIn (P.cluster P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight_staysIn P hN

theorem toLastRight_hasPairwiseBridgesIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).HasPairwiseBridgesIn (P.cluster P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight_hasPairwiseBridgesIn P hN

end EvenClusterOutputs

/-- For `g ≥ 2`, the number `g * (g - 1)` of even one-based clusters used by
Appendix C is positive. -/
theorem evenClusterOrdinal_count_pos_of_two_le {g : ℕ} (hg : 2 ≤ g) :
    0 < g * (g - 1) := by
  exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hg)
    (Nat.sub_pos_of_lt hg)

/-- The canonical stitching pieces between local even-cluster outputs.

The start piece connects the first left nail set to the first local output.
For every consecutive pair of even one-based clusters, `between` is the
perfect packing through the intervening odd cluster supplied by the strong
path-of-sets linkage.  The last local output is exposed by `last`.

The remaining Appendix C work after this structure is to concatenate these
pieces with the local outputs, then prove the trace and ordering fields of
`StitchedRows`. -/
structure StitchingPieces {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w q : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q) where
  /-- Positivity of the even-cluster ordinal set. -/
  hN : 0 < g * (g - 1)
  /-- Initial linkage from the first left nails to the first local output. -/
  start :
    PathPacking G (P.left P.firstIndex) ((E.output ⟨0, hN⟩).paths.sourceSet)
  /-- The actual first-cluster linkage used to construct `start`, together with
  its retained path indices and exact traces. -/
  start_provenance : StartStitchingPackingData P start
  /-- The initial linkage has the intended cardinality. -/
  start_card : start.card = q
  /-- The initial linkage is routed through the first cluster and first
  connector. -/
  start_staysIn : start.StaysIn (firstStitchingRegion P hN)
  /-- The initial linkage avoids the first even one-based cluster internally. -/
  start_internallyDisjoint_firstEven :
    start.InternallyDisjointFromSet (P.cluster (evenClusterIndex g ⟨0, hN⟩))
  /-- Stitching linkages between consecutive local even-cluster outputs. -/
  between :
    (i : Fin (g * (g - 1))) → (hi : i.1 + 1 < g * (g - 1)) →
      PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet)
  /-- Exact middle-cluster provenance for each between-cluster packing. -/
  between_provenance :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      BetweenStitchingPackingData (q := q) P i hi (between i hi)
  /-- Every between-cluster stitching linkage has the intended cardinality. -/
  between_card :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).card = q
  /-- Every between-cluster stitching linkage is routed through the two
  connectors and the intervening odd one-based cluster. -/
  between_staysIn :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.StaysIn (betweenStitchingRegion P i hi)
  /-- Between-cluster stitching avoids the source even cluster internally. -/
  between_internallyDisjoint_left :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.InternallyDisjointFromSet
        (P.cluster (evenClusterIndex g i))
  /-- Between-cluster stitching avoids the target even cluster internally. -/
  between_internallyDisjoint_right :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.InternallyDisjointFromSet
        (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi)))
  /-- The last local output, viewed as ending in the last right nail set. -/
  last :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex)
  /-- The last local output has the intended cardinality. -/
  last_card : last.card = q
  /-- The last local output stays inside the last cluster. -/
  last_output_staysIn : last.StaysIn (P.cluster P.lastIndex)
  /-- The last local output retains the pairwise bridges from the last even
  one-based cluster. -/
  last_output_pairwise_bridges :
    last.HasPairwiseBridgesIn (P.cluster P.lastIndex)

namespace StitchingPieces

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- One dependent choice of the initial packing, its exact first-cluster
provenance, and all concatenation invariants. -/
private structure CanonicalStartChoice
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) where
  packing :
    PathPacking G (P.left P.firstIndex)
      ((E.output ⟨0, hN⟩).paths.sourceSet)
  provenance : StartStitchingPackingData P packing
  card_eq : packing.card = q
  staysIn : packing.StaysIn (firstStitchingRegion P hN)
  internallyDisjoint_firstEven :
    packing.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g ⟨0, hN⟩))

/-- Choose all dependent start data together so every canonical projection
comes from one producer witness. -/
private noncomputable def canonicalStartChoice
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    CanonicalStartChoice P E hN :=
  Classical.choice (by
    rcases E.exists_startPacking_to_first_with_invariants_and_provenance P hN with
      ⟨S, ⟨D⟩, hcard, hstays, hinternal⟩
    exact ⟨{
      packing := S
      provenance := D
      card_eq := hcard
      staysIn := hstays
      internallyDisjoint_firstEven := hinternal
    }⟩)

/-- One dependent choice of a between-cluster packing, its exact middle
provenance, and all collapsed-packing invariants. -/
private structure CanonicalBetweenChoice
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) where
  packing :
    PerfectPathPacking G (E.output i).paths.targetSet
      ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet)
  provenance : BetweenStitchingPackingData (q := q) P i hi packing
  card_eq : packing.card = q
  staysIn : packing.toPathPacking.StaysIn (betweenStitchingRegion P i hi)
  internallyDisjoint_left :
    packing.toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g i))
  internallyDisjoint_right :
    packing.toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi)))

/-- Choose the collapsed packing and its middle provenance together, so every
canonical projection is definitionally tied to the same existential witness. -/
private noncomputable def canonicalBetweenChoice
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    CanonicalBetweenChoice P E i hi :=
  let hex := E.exists_stitchingPacking_to_next_with_invariants_and_provenance P hi
  let S := Classical.choose hex
  let hS := Classical.choose_spec hex
  {
    packing := S
    provenance := Classical.choice hS.1
    card_eq := hS.2.1
    staysIn := hS.2.2.1
    internallyDisjoint_left := hS.2.2.2.1
    internallyDisjoint_right := hS.2.2.2.2
  }

/-- Construct the canonical stitching pieces from a strong path-of-sets system
and local outputs, assuming the even-cluster ordinal set is nonempty. -/
noncomputable def canonical
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    StitchingPieces P E where
  hN := hN
  start := (canonicalStartChoice P E hN).packing
  start_provenance := (canonicalStartChoice P E hN).provenance
  start_card := (canonicalStartChoice P E hN).card_eq
  start_staysIn := (canonicalStartChoice P E hN).staysIn
  start_internallyDisjoint_firstEven :=
    (canonicalStartChoice P E hN).internallyDisjoint_firstEven
  between := fun i hi =>
    (canonicalBetweenChoice P E i hi).packing
  between_provenance := fun i hi =>
    (canonicalBetweenChoice P E i hi).provenance
  between_card := by
    intro i hi
    exact (canonicalBetweenChoice P E i hi).card_eq
  between_staysIn := by
    intro i hi
    exact (canonicalBetweenChoice P E i hi).staysIn
  between_internallyDisjoint_left := by
    intro i hi
    exact (canonicalBetweenChoice P E i hi).internallyDisjoint_left
  between_internallyDisjoint_right := by
    intro i hi
    exact (canonicalBetweenChoice P E i hi).internallyDisjoint_right
  last := E.toLastRight P.toPathOfSetsSystem hN
  last_card := by
    simp
  last_output_staysIn :=
    E.toLastRight_staysIn P.toPathOfSetsSystem hN
  last_output_pairwise_bridges :=
    E.toLastRight_hasPairwiseBridgesIn P.toPathOfSetsSystem hN

/-- For `g ≥ 2`, the canonical stitching pieces exist. -/
noncomputable def canonicalOfTwoLe
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hg : 2 ≤ g) :
    StitchingPieces P E :=
  canonical P E (evenClusterOrdinal_count_pos_of_two_le hg)

/-- The initial stitching piece, promoted to a perfect packing on the source
terminals it actually uses and the full local source set of the first even
one-based cluster. -/
noncomputable def startPerfect
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    PerfectPathPacking G K.start.sourceSet ((E.output ⟨0, K.hN⟩).paths.sourceSet) :=
  K.start.toPerfectUsedTerminals.copyTerminals rfl
    (K.start.targetSet_eq_right_of_card_eq (by
      rw [K.start_card, PathPacking.sourceSet_card,
        (E.output ⟨0, K.hN⟩).paths_card]))

@[simp] theorem startPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.card = q := by
  simp [startPerfect, K.start_card]

theorem startPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.toPathPacking.StaysIn (firstStitchingRegion P K.hN) := by
  simpa [startPerfect] using
    K.start.toPerfectUsedTerminals_staysIn K.start_staysIn

theorem startPerfect_internallyDisjoint_firstEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  simpa [startPerfect] using
    K.start.toPerfectUsedTerminals_internallyDisjointFromSet
      K.start_internallyDisjoint_firstEven

/-- The retained full-width first-cluster path underlying each perfect start
path. -/
noncomputable def startFirstClusterIndex
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.Index → K.start_provenance.leftRight.Index :=
  K.start_provenance.indexMap

theorem startFirstClusterIndex_injective
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    Function.Injective K.startFirstClusterIndex :=
  K.start_provenance.indexMap_injective

/-- Promoting the start packing to a perfect packing preserves its exact trace
in the first cluster. -/
theorem startPerfect_firstCluster_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.startPerfect.Index) :
    (K.startPerfect.path a).vertexSet ∩ P.cluster P.firstIndex =
      (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex a)).vertexSet := by
  simpa [startPerfect, startFirstClusterIndex,
    PathPacking.toPerfectUsedTerminals] using
    K.start_provenance.trace_eq a

/-- A local even-cluster row output, promoted to a perfect packing on the
terminal sets it actually uses. -/
noncomputable def localPerfect
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (_K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    PerfectPathPacking G (E.output i).paths.sourceSet (E.output i).paths.targetSet :=
  (E.output i).paths.toPerfectUsedTerminals

@[simp] theorem localPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).card = q := by
  simp [localPerfect, (E.output i).paths_card]

theorem localPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).toPathPacking.StaysIn
      (P.cluster (evenClusterIndex g i)) := by
  simpa [localPerfect] using
    (E.output i).paths.toPerfectUsedTerminals_staysIn
      (E.output i).paths_staysIn

theorem localPerfect_hasPairwiseBridgesIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).toPathPacking.HasPairwiseBridgesIn
      (P.cluster (evenClusterIndex g i)) := by
  simpa [localPerfect] using
    (E.output i).paths.toPerfectUsedTerminals_hasPairwiseBridgesIn
      (E.output i).pairwise_bridges

@[simp] theorem betweenPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).card = q :=
  K.between_card i hi

theorem betweenPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.StaysIn (betweenStitchingRegion P i hi) :=
  K.between_staysIn i hi

theorem betweenPerfect_internallyDisjoint_left
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g i)) :=
  K.between_internallyDisjoint_left i hi

theorem betweenPerfect_internallyDisjoint_right
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  K.between_internallyDisjoint_right i hi

theorem last_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.last.StaysIn (P.cluster P.lastIndex) :=
  K.last_output_staysIn

theorem last_hasPairwiseBridgesIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.last.HasPairwiseBridgesIn (P.cluster P.lastIndex) :=
  K.last_output_pairwise_bridges

/-- The source terminals used by the initial perfect stitching piece are
disjoint from the first even one-based cluster. -/
theorem startPerfect_source_disjoint_firstEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    Disjoint K.start.sourceSet
      (P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvSource hvCluster
  have hvLeft : v ∈ P.left P.firstIndex :=
    K.start.sourceSet_subset_left hvSource
  have hvFirstCluster : v ∈ P.cluster P.firstIndex :=
    P.left_subset_cluster P.firstIndex hvLeft
  have hne : P.firstIndex ≠ evenClusterIndex g ⟨0, K.hN⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hval
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
    hvFirstCluster hvCluster

/-- The first stitched prefix: the initial linkage followed by the local row
pieces in the first even one-based cluster. -/
noncomputable def firstPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output ⟨0, K.hN⟩).paths.targetSet) :=
  K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn
    (K.localPerfect ⟨0, K.hN⟩)
    K.startPerfect_internallyDisjoint_firstEven
    (K.localPerfect_staysIn ⟨0, K.hN⟩)
    K.startPerfect_source_disjoint_firstEven

@[simp] theorem firstPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.firstPrefix.card = q := by
  simp [firstPrefix]

theorem firstPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.firstPrefix.toPathPacking.StaysIn
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  simpa [firstPrefix] using
    K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      (K.localPerfect ⟨0, K.hN⟩)
      K.startPerfect_internallyDisjoint_firstEven
      (K.localPerfect_staysIn ⟨0, K.hN⟩)
      K.startPerfect_source_disjoint_firstEven
      K.startPerfect_staysIn

/-- The first between-cluster stitching packing is disjoint from the initial
stitching region. -/
theorem betweenPerfect_vertexSet_disjoint_firstStitchingRegion_first
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint (K.between ⟨0, K.hN⟩ hi).toPathPacking.vertexSet
      (firstStitchingRegion P K.hN) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvBetween hvFirst
  have hvRegion :
      v ∈ betweenStitchingRegion P ⟨0, K.hN⟩ hi :=
    PathPacking.vertexSet_subset_of_staysIn
      (K.betweenPerfect_staysIn ⟨0, K.hN⟩ hi) hvBetween
  exact Finset.disjoint_left.mp
    (betweenStitchingRegion_first_disjoint_firstStitchingRegion P K.hN hi)
    hvRegion hvFirst

/-- The first between-cluster stitching packing is internally disjoint from
the full region already used by the first prefix. -/
theorem betweenPerfect_internallyDisjoint_firstPrefixRegion_first
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.between ⟨0, K.hN⟩ hi).toPathPacking.InternallyDisjointFromSet
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  have h :=
    PathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
      (K.between ⟨0, K.hN⟩ hi).toPathPacking
      (K.betweenPerfect_internallyDisjoint_left ⟨0, K.hN⟩ hi)
      (K.betweenPerfect_vertexSet_disjoint_firstStitchingRegion_first hi)
  simpa [Finset.union_comm] using h

/-- The source terminals of the next even-cluster local output are disjoint
from the first-prefix region. -/
theorem nextEvenSource_disjoint_firstPrefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.sourceSet)
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem K.hN
  have he1_ne_firstIndex : e1 ≠ P.firstIndex := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  have he1_ne_e0 : e1 ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, e0, next, first, nextEvenClusterOrdinal, evenClusterIndex] at hval
  have he1_ne_after_first : e1 ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvSource hvRegion
  have hvE1 : v ∈ P.cluster e1 :=
    P.left_subset_cluster e1
      ((E.output next).paths.sourceSet_subset_left (by simpa [next, e1] using hvSource))
  rcases Finset.mem_union.mp hvRegion with hvFirstRegion | hvE0
  · rcases Finset.mem_union.mp (by simpa [firstStitchingRegion, hgap0] using hvFirstRegion)
        with hvFirstCluster | hvFirstConnector
    · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_firstIndex)
        hvE1 hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 e1
          he1_ne_firstIndex he1_ne_after_first).symm)
        hvE1 hvFirstConnector
  · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_e0)
      hvE1 (by simpa [e0] using hvE0)

/-- The second stitched prefix: the first prefix followed by the stitching
packing from the first even one-based cluster to the next even one. -/
noncomputable def secondPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.sourceSet) :=
  K.firstPrefix.concatOfFirstStaysInSecondInternallyDisjoint
    (K.between ⟨0, K.hN⟩ hi)
    K.firstPrefix_staysIn
    (K.betweenPerfect_internallyDisjoint_firstPrefixRegion_first hi)
    (K.nextEvenSource_disjoint_firstPrefixRegion hi)

@[simp] theorem secondPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).card = q := by
  simp [secondPrefix]

theorem secondPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).toPathPacking.StaysIn
      ((firstStitchingRegion P K.hN ∪
          P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) ∪
        betweenStitchingRegion P ⟨0, K.hN⟩ hi) := by
  simpa [secondPrefix] using
    K.firstPrefix.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      (K.between ⟨0, K.hN⟩ hi)
      K.firstPrefix_staysIn
      (K.betweenPerfect_internallyDisjoint_firstPrefixRegion_first hi)
      (K.nextEvenSource_disjoint_firstPrefixRegion hi)
      (K.betweenPerfect_staysIn ⟨0, K.hN⟩ hi)

/-- The second even one-based cluster is disjoint from the full first-prefix
region. -/
theorem nextEvenCluster_disjoint_firstPrefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)))
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem K.hN
  have he1_ne_firstIndex : e1 ≠ P.firstIndex := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  have he1_ne_e0 : e1 ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, e0, next, first, nextEvenClusterOrdinal, evenClusterIndex] at hval
  have he1_ne_after_first : e1 ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvE1 hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirstRegion | hvE0
  · rcases Finset.mem_union.mp
        (by simpa [firstStitchingRegion, hgap0] using hvFirstRegion)
        with hvFirstCluster | hvFirstConnector
    · exact Finset.disjoint_left.mp
        (P.cluster_disjoint he1_ne_firstIndex) hvE1 hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 e1
          he1_ne_firstIndex he1_ne_after_first).symm)
        hvE1 hvFirstConnector
  · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_e0)
      hvE1 (by simpa [e0] using hvE0)

/-- The first stitched prefix uses no vertex in the second even one-based
cluster. -/
theorem firstPrefix_vertexSet_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint K.firstPrefix.toPathPacking.vertexSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPrefix hvCluster
  have hvRegion :
      v ∈ firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩) :=
    PathPacking.vertexSet_subset_of_staysIn K.firstPrefix_staysIn hvPrefix
  exact Finset.disjoint_left.mp
    (K.nextEvenCluster_disjoint_firstPrefixRegion hi)
    hvCluster hvRegion

/-- The first local target set is disjoint from the second even one-based
cluster. -/
theorem firstEvenTarget_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint ((E.output ⟨0, K.hN⟩).paths.targetSet)
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  have he0_ne_e1 : e0 ≠ e1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e0, e1, first, next, nextEvenClusterOrdinal, evenClusterIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvTarget hvCluster
  have hvE0 : v ∈ P.cluster e0 :=
    P.right_subset_cluster e0
      ((E.output first).paths.targetSet_subset_right
        (by simpa [first, e0] using hvTarget))
  exact Finset.disjoint_left.mp (P.cluster_disjoint he0_ne_e1)
    hvE0 (by simpa [next, e1] using hvCluster)

/-- The global start terminals used by the stitched prefix are disjoint from
the second even one-based cluster. -/
theorem startSource_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint K.start.sourceSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  have hne : P.firstIndex ≠ e1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e1, next, first,
      nextEvenClusterOrdinal, evenClusterIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvSource hvCluster
  have hvFirst : v ∈ P.cluster P.firstIndex :=
    P.left_subset_cluster P.firstIndex (K.start.sourceSet_subset_left hvSource)
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
    hvFirst (by simpa [next, e1] using hvCluster)

/-- The second stitched prefix is internally disjoint from the second even
one-based cluster, so the second local row pieces can be appended next. -/
theorem secondPrefix_internallyDisjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  dsimp [secondPrefix, PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint]
  apply PerfectPathPacking.concat_internallyDisjointFromSet_right
  · exact K.firstPrefix_vertexSet_disjoint_nextEvenCluster hi
  · exact K.firstEvenTarget_disjoint_nextEvenCluster hi
  · exact K.betweenPerfect_internallyDisjoint_right ⟨0, K.hN⟩ hi

/-- The prefix through the second local even-cluster output. -/
noncomputable def thirdPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.targetSet) :=
  (K.secondPrefix hi).concatOfFirstInternallyDisjointSecondStaysIn
    (K.localPerfect (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
    (K.secondPrefix_internallyDisjoint_nextEvenCluster hi)
    (K.localPerfect_staysIn (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
    (K.startSource_disjoint_nextEvenCluster hi)

@[simp] theorem thirdPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.thirdPrefix hi).card = q := by
  simp [thirdPrefix]

theorem thirdPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.thirdPrefix hi).toPathPacking.StaysIn
      (((firstStitchingRegion P K.hN ∪
          P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) ∪
        betweenStitchingRegion P ⟨0, K.hN⟩ hi) ∪
          P.cluster (evenClusterIndex g
            (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  simpa [thirdPrefix] using
    (K.secondPrefix hi).concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      (K.localPerfect (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
      (K.secondPrefix_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
      (K.startSource_disjoint_nextEvenCluster hi)
      (K.secondPrefix_staysIn hi)

/-- If `j` is an earlier even-cluster ordinal than `i`, then the successor of
`j` is still a valid even-cluster ordinal. -/
theorem evenClusterOrdinal_succ_lt_of_lt
    {i j : Fin (g * (g - 1))} (hji : j.1 < i.1) :
    j.1 + 1 < g * (g - 1) :=
  lt_of_le_of_lt (Nat.succ_le_iff.mpr hji) i.2

/-- The index transport used by perfect-packing concatenation is injective. -/
theorem perfect_indexOfSourceTarget_injective
    {S T U : Finset V}
    (Q₁ : PerfectPathPacking G S T) (Q₂ : PerfectPathPacking G T U) :
    Function.Injective (Q₁.indexOfSourceTarget Q₂) := by
  intro a b hab
  apply Q₁.target_bijective.1
  apply Subtype.ext
  calc
    (Q₁.path a).target =
        (Q₂.path (Q₁.indexOfSourceTarget Q₂ a)).source :=
      (Q₁.source_indexOfSourceTarget Q₂ a).symm
    _ = (Q₂.path (Q₁.indexOfSourceTarget Q₂ b)).source := by rw [hab]
    _ = (Q₁.path b).target := Q₁.source_indexOfSourceTarget Q₂ b

theorem perfect_left_path_subset_concatOfFirstStays
    {S T U A : Finset V}
    (Q₁ : PerfectPathPacking G S T) (Q₂ : PerfectPathPacking G T U)
    (hQ₁ : Q₁.toPathPacking.StaysIn A)
    (hQ₂ : Q₂.toPathPacking.InternallyDisjointFromSet A)
    (hU : Disjoint U A)
    (a : (Q₁.concatOfFirstStaysInSecondInternallyDisjoint
      Q₂ hQ₁ hQ₂ hU).Index) :
    (Q₁.path a).vertexSet ⊆
      ((Q₁.concatOfFirstStaysInSecondInternallyDisjoint
        Q₂ hQ₁ hQ₂ hU).path a).vertexSet := by
  dsimp [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint,
    PerfectPathPacking.concat]
  exact GraphPath.left_vertexSet_subset_appendWithEq _ _ _ _

theorem perfect_right_path_subset_concatOfFirstStays
    {S T U A : Finset V}
    (Q₁ : PerfectPathPacking G S T) (Q₂ : PerfectPathPacking G T U)
    (hQ₁ : Q₁.toPathPacking.StaysIn A)
    (hQ₂ : Q₂.toPathPacking.InternallyDisjointFromSet A)
    (hU : Disjoint U A)
    (a : (Q₁.concatOfFirstStaysInSecondInternallyDisjoint
      Q₂ hQ₁ hQ₂ hU).Index) :
    (Q₂.path (Q₁.indexOfSourceTarget Q₂ a)).vertexSet ⊆
      ((Q₁.concatOfFirstStaysInSecondInternallyDisjoint
        Q₂ hQ₁ hQ₂ hU).path a).vertexSet := by
  dsimp [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint,
    PerfectPathPacking.concat]
  exact GraphPath.right_vertexSet_subset_appendWithEq _ _ _ _

theorem perfect_left_path_subset_concatOfFirstInternallyDisjoint
    {S T U A : Finset V}
    (Q₁ : PerfectPathPacking G S T) (Q₂ : PerfectPathPacking G T U)
    (hQ₁ : Q₁.toPathPacking.InternallyDisjointFromSet A)
    (hQ₂ : Q₂.toPathPacking.StaysIn A)
    (hS : Disjoint S A)
    (a : (Q₁.concatOfFirstInternallyDisjointSecondStaysIn
      Q₂ hQ₁ hQ₂ hS).Index) :
    (Q₁.path a).vertexSet ⊆
      ((Q₁.concatOfFirstInternallyDisjointSecondStaysIn
        Q₂ hQ₁ hQ₂ hS).path a).vertexSet := by
  dsimp [PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn,
    PerfectPathPacking.concat]
  exact GraphPath.left_vertexSet_subset_appendWithEq _ _ _ _

theorem perfect_right_path_subset_concatOfFirstInternallyDisjoint
    {S T U A : Finset V}
    (Q₁ : PerfectPathPacking G S T) (Q₂ : PerfectPathPacking G T U)
    (hQ₁ : Q₁.toPathPacking.InternallyDisjointFromSet A)
    (hQ₂ : Q₂.toPathPacking.StaysIn A)
    (hS : Disjoint S A)
    (a : (Q₁.concatOfFirstInternallyDisjointSecondStaysIn
      Q₂ hQ₁ hQ₂ hS).Index) :
    (Q₂.path (Q₁.indexOfSourceTarget Q₂ a)).vertexSet ⊆
      ((Q₁.concatOfFirstInternallyDisjointSecondStaysIn
        Q₂ hQ₁ hQ₂ hS).path a).vertexSet := by
  dsimp [PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn,
    PerfectPathPacking.concat]
  exact GraphPath.right_vertexSet_subset_appendWithEq _ _ _ _

/-- Region containment gives whole-vertex-set separation from a later
cluster. -/
theorem perfect_vertexSet_disjoint_futureCluster_of_staysIn
    {S T : Finset V} (Q : PerfectPathPacking G S T)
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {i j : Fin (2 * g * (g - 1))}
    (hQ : Q.toPathPacking.StaysIn (stitchingPrefixRegion P i))
    (hij : i.1 < j.1) :
    Disjoint Q.toPathPacking.vertexSet (P.cluster j) := by
  rw [Finset.disjoint_left]
  intro v hvQ hvCluster
  have hvPrefix := PathPacking.vertexSet_subset_of_staysIn hQ hvQ
  exact Finset.disjoint_left.mp
    (stitchingPrefixRegion_disjoint_cluster_of_lt P hij)
    hvPrefix hvCluster

/-- A between-cluster packing is internally disjoint from the entire prefix
region through its source even cluster. -/
theorem betweenPerfect_internallyDisjoint_prefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.InternallyDisjointFromSet
      (stitchingPrefixRegion P (evenClusterIndex g i)) := by
  have hStrict :
      Disjoint (K.between i hi).toPathPacking.vertexSet
        (strictStitchingPrefixRegion P (evenClusterIndex g i)) := by
    rw [Finset.disjoint_left]
    intro v hvBetween hvStrict
    have hvRegion : v ∈ betweenStitchingRegion P i hi :=
      PathPacking.vertexSet_subset_of_staysIn
        (K.betweenPerfect_staysIn i hi) hvBetween
    exact Finset.disjoint_left.mp
      (betweenStitchingRegion_disjoint_strictPrefixRegion P i hi)
      hvRegion hvStrict
  have h :=
    PathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
      (K.between i hi).toPathPacking
      (K.betweenPerfect_internallyDisjoint_left i hi) hStrict
  simpa [stitchingPrefixRegion, Finset.union_comm] using h

/-- The next local source terminals avoid the entire prefix through the
current even cluster. -/
theorem nextEvenSource_disjoint_prefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (_K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    Disjoint
      ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet)
      (stitchingPrefixRegion P (evenClusterIndex g i)) := by
  rw [Finset.disjoint_left]
  intro v hvSource hvPrefix
  have hvNext :
      v ∈ P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
    P.left_subset_cluster _
      ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet_subset_left
        hvSource)
  exact Finset.disjoint_left.mp
    (stitchingPrefixRegion_disjoint_cluster_of_lt P
      (evenClusterIndex_lt_of_lt (by simp [nextEvenClusterOrdinal])))
    hvPrefix hvNext

/-- The current local target terminals avoid the next even cluster. -/
theorem localTarget_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (_K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    Disjoint ((E.output i).paths.targetSet)
      (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  rw [Finset.disjoint_left]
  intro v hvTarget hvNext
  have hvCurrent : v ∈ P.cluster (evenClusterIndex g i) :=
    P.right_subset_cluster _ ((E.output i).paths.targetSet_subset_right hvTarget)
  have hne : evenClusterIndex g i ≠
      evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
    intro h
    have hord := evenClusterIndex_injective h
    have hval := congrArg Fin.val hord
    simp [nextEvenClusterOrdinal] at hval
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvCurrent hvNext

/-- The global start terminals avoid every even one-based cluster. -/
theorem startSource_disjoint_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    Disjoint K.start.sourceSet (P.cluster (evenClusterIndex g i)) := by
  rw [Finset.disjoint_left]
  intro v hvSource hvEven
  have hvFirst : v ∈ P.cluster P.firstIndex :=
    P.left_subset_cluster P.firstIndex (K.start.sourceSet_subset_left hvSource)
  have hne : P.firstIndex ≠ evenClusterIndex g i := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hval
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne) hvFirst hvEven

/-- A stitched prefix through one even one-based cluster, retaining enough
provenance to recover every constituent path in each assembled row. -/
structure StitchedPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) where
  /-- The assembled rows through local output `i`. -/
  packing : PerfectPathPacking G K.start.sourceSet (E.output i).paths.targetSet
  /-- Every prefix has the fixed local-output cardinality. -/
  card_eq : packing.card = q
  /-- The assembled rows use only the path-of-sets region through `i`. -/
  staysIn : packing.toPathPacking.StaysIn
    (stitchingPrefixRegion P (evenClusterIndex g i))
  /-- Before the next step, the whole assembled prefix avoids the next even
  cluster.  This is stronger than the internal-disjointness needed by concat. -/
  next_cluster_disjoint :
    ∀ hi : i.1 + 1 < g * (g - 1),
      Disjoint packing.toPathPacking.vertexSet
        (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi)))
  /-- The initial linkage path used by each assembled row. -/
  startIndex : packing.Index → K.startPerfect.Index
  startIndex_injective : Function.Injective startIndex
  start_path_subset :
    ∀ a : packing.Index,
      (K.startPerfect.path (startIndex a)).vertexSet ⊆
        (packing.path a).vertexSet
  /-- No later constituent contributes a new vertex in the first cluster. -/
  start_trace_eq :
    ∀ a : packing.Index,
      (packing.path a).vertexSet ∩ P.cluster P.firstIndex =
        (K.start_provenance.leftRight.path
          (K.startFirstClusterIndex (startIndex a))).vertexSet
  /-- The local path used by an assembled row in each completed even cluster. -/
  localIndex :
    ∀ (j : Fin (g * (g - 1))), j.1 ≤ i.1 →
      packing.Index → (K.localPerfect j).Index
  localIndex_injective :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1),
      Function.Injective (localIndex j hji)
  local_path_subset :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1)
      (a : packing.Index),
      ((K.localPerfect j).path (localIndex j hji a)).vertexSet ⊆
        (packing.path a).vertexSet
  /-- No other part of an assembled row enters a completed even cluster. -/
  local_trace_subset :
    ∀ (j) (hji) (a),
      (packing.path a).vertexSet ∩ P.cluster (evenClusterIndex g j) ⊆
        ((K.localPerfect j).path (localIndex j hji a)).vertexSet
  /-- The between-cluster path used by an assembled row after each earlier
  even cluster. -/
  betweenIndex :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 < i.1),
      packing.Index →
        (K.between j (evenClusterOrdinal_succ_lt_of_lt hji)).Index
  betweenIndex_injective :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 < i.1),
      Function.Injective (betweenIndex j hji)
  between_path_subset :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 < i.1)
      (a : packing.Index),
      ((K.between j (evenClusterOrdinal_succ_lt_of_lt hji)).path
          (betweenIndex j hji a)).vertexSet ⊆
        (packing.path a).vertexSet
  /-- No other part of an assembled row enters a completed intervening odd
  cluster. -/
  between_trace_subset :
    ∀ (j : Fin (g * (g - 1))) (hji : j.1 < i.1)
      (a : packing.Index),
      (packing.path a).vertexSet ∩
          P.cluster (oddClusterAfterEvenIndex g j
            (evenClusterOrdinal_succ_lt_of_lt hji)) ⊆
        ((K.between_provenance j
            (evenClusterOrdinal_succ_lt_of_lt hji)).middle.path
          ((K.between_provenance j
              (evenClusterOrdinal_succ_lt_of_lt hji)).indexEquiv
            (betweenIndex j hji a))).vertexSet
  /-- Vertices in earlier clusters occur earlier along every assembled row. -/
  clusters_ordered :
    ∀ (a : packing.Index)
      ⦃j k : Fin (2 * g * (g - 1))⦄,
      j.1 < k.1 →
        k.1 ≤ (evenClusterIndex g i).1 →
          ∀ ⦃u v : V⦄,
            u ∈ (packing.path a).vertexSet →
              u ∈ P.cluster j →
                v ∈ (packing.path a).vertexSet →
                  v ∈ P.cluster k →
                    (packing.path a).Before u v

/-- Every assembled prefix row has the provenance-selected path as its exact
trace in the first cluster. -/
theorem StitchedPrefix.traceOn_firstCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (a : F.packing.Index) :
    (F.packing.path a).TraceOn (P.cluster P.firstIndex) := by
  refine ⟨K.start_provenance.leftRight.path
    (K.startFirstClusterIndex (F.startIndex a)), ?_⟩
  exact (F.start_trace_eq a).symm

/-- In every completed intervening odd cluster, an assembled row has exactly
the middle path retained by the corresponding between-piece provenance. -/
theorem StitchedPrefix.between_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 < i.1)
    (a : F.packing.Index) :
    (F.packing.path a).vertexSet ∩
        P.cluster (oddClusterAfterEvenIndex g j
          (evenClusterOrdinal_succ_lt_of_lt hji)) =
      ((K.between_provenance j
          (evenClusterOrdinal_succ_lt_of_lt hji)).middle.path
        ((K.between_provenance j
            (evenClusterOrdinal_succ_lt_of_lt hji)).indexEquiv
          (F.betweenIndex j hji a))).vertexSet := by
  apply Finset.Subset.antisymm
  · exact F.between_trace_subset j hji a
  · intro v hv
    have hvTrace :
        v ∈ ((K.between j (evenClusterOrdinal_succ_lt_of_lt hji)).path
            (F.betweenIndex j hji a)).vertexSet ∩
          P.cluster (oddClusterAfterEvenIndex g j
            (evenClusterOrdinal_succ_lt_of_lt hji)) := by
      rw [(K.between_provenance j
        (evenClusterOrdinal_succ_lt_of_lt hji)).trace_eq]
      exact hv
    exact Finset.mem_inter.mpr
      ⟨F.between_path_subset j hji a (Finset.mem_inter.mp hvTrace).1,
        (Finset.mem_inter.mp hvTrace).2⟩

/-- Every completed intervening odd cluster has the provenance-selected middle
path as the trace of each assembled row. -/
theorem StitchedPrefix.traceOn_oddClusterAfterEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 < i.1)
    (a : F.packing.Index) :
    (F.packing.path a).TraceOn
      (P.cluster (oddClusterAfterEvenIndex g j
        (evenClusterOrdinal_succ_lt_of_lt hji))) := by
  refine ⟨(K.between_provenance j
    (evenClusterOrdinal_succ_lt_of_lt hji)).middle.path
      ((K.between_provenance j
          (evenClusterOrdinal_succ_lt_of_lt hji)).indexEquiv
        (F.betweenIndex j hji a)), ?_⟩
  exact (F.between_trace_eq j hji a).symm

theorem StitchedPrefix.local_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1)
    (a : F.packing.Index) :
    (F.packing.path a).vertexSet ∩ P.cluster (evenClusterIndex g j) =
      ((K.localPerfect j).path (F.localIndex j hji a)).vertexSet := by
  apply Finset.Subset.antisymm
  · exact F.local_trace_subset j hji a
  · intro v hv
    exact Finset.mem_inter.mpr
      ⟨F.local_path_subset j hji a hv, K.localPerfect_staysIn j _ hv⟩

/-- Every completed even cluster has exactly its local path as row trace. -/
theorem StitchedPrefix.traceOn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1)
    (a : F.packing.Index) :
    (F.packing.path a).TraceOn (P.cluster (evenClusterIndex g j)) := by
  refine ⟨(K.localPerfect j).path (F.localIndex j hji a), ?_⟩
  exact (F.local_trace_eq j hji a).symm

/-- A bridge between the local pieces followed by two assembled rows remains a
bridge between the assembled rows, provided it stays in the local cluster. -/
theorem StitchedPrefix.liftLocalBridge
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1)
    {a b : F.packing.Index}
    (beta : (K.localPerfect j).toPathPacking.BridgeBetween
      (F.localIndex j hji a) (F.localIndex j hji b))
    (hbeta : beta.path.vertexSet ⊆
      P.cluster (evenClusterIndex g j)) :
    ∃ beta' : F.packing.toPathPacking.BridgeBetween a b,
      beta'.path.vertexSet ⊆ P.cluster (evenClusterIndex g j) := by
  let R := beta.orientedPath
  have hRsource : R.source ∈ (F.packing.path a).vertexSet := by
    apply F.local_path_subset j hji a
    simpa [R] using
      PathPacking.BridgeBetween.orientedPath_source_mem_left beta
  have hRtarget : R.target ∈ (F.packing.path b).vertexSet := by
    apply F.local_path_subset j hji b
    simpa [R] using
      PathPacking.BridgeBetween.orientedPath_target_mem_right beta
  have hRinternal :
      R.InternallyDisjointFromSet F.packing.toPathPacking.vertexSet := by
    intro v hvR hvRows
    have hvCluster : v ∈ P.cluster (evenClusterIndex g j) :=
      hbeta (by simpa [R] using hvR)
    rcases (PathPacking.mem_vertexSet F.packing.toPathPacking).1 hvRows with
      ⟨c, hvc⟩
    have hvLocal :
        v ∈ ((K.localPerfect j).path
          (F.localIndex j hji c)).vertexSet := by
      rw [← F.local_trace_eq j hji c]
      exact Finset.mem_inter.mpr ⟨hvc, hvCluster⟩
    have hvLocalRows :
        v ∈ (K.localPerfect j).toPathPacking.vertexSet :=
      (PathPacking.mem_vertexSet (K.localPerfect j).toPathPacking).2
        ⟨F.localIndex j hji c, hvLocal⟩
    simpa [R] using
      PathPacking.BridgeBetween.orientedPath_internallyDisjoint beta
        (by simpa [R] using hvR) hvLocalRows
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    F.packing.toPathPacking R hRsource hRtarget hRinternal, ?_⟩
  change R.vertexSet ⊆ P.cluster (evenClusterIndex g j)
  simpa [R] using hbeta

/-- Pairwise bridges in a completed local even cluster lift to the assembled
prefix rows. -/
theorem StitchedPrefix.hasPairwiseBridgesIn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i)
    (j : Fin (g * (g - 1))) (hji : j.1 ≤ i.1) :
    F.packing.toPathPacking.HasPairwiseBridgesIn
      (P.cluster (evenClusterIndex g j)) := by
  intro a b hab
  have hlocal : F.localIndex j hji a ≠ F.localIndex j hji b := by
    intro h
    exact hab (F.localIndex_injective j hji h)
  rcases K.localPerfect_hasPairwiseBridgesIn j hlocal with ⟨beta, hbeta⟩
  exact F.liftLocalBridge j hji beta hbeta

/-- The first local-piece index followed by a row of `firstPrefix`. -/
noncomputable def firstPrefixLocalIndex
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (j : Fin (g * (g - 1))) (hj : j.1 ≤ 0)
    (a : K.firstPrefix.Index) :
    (K.localPerfect j).Index := by
  have hj0 : j = ⟨0, K.hN⟩ := by
    apply Fin.ext
    simpa using Nat.eq_zero_of_le_zero hj
  subst j
  exact K.startPerfect.indexOfSourceTarget
    (K.localPerfect ⟨0, K.hN⟩) a

theorem firstPrefixLocalIndex_injective
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (j : Fin (g * (g - 1))) (hj : j.1 ≤ 0) :
    Function.Injective (K.firstPrefixLocalIndex j hj) := by
  have hj0 : j = ⟨0, K.hN⟩ := by
    apply Fin.ext
    simpa using Nat.eq_zero_of_le_zero hj
  subst j
  simpa [firstPrefixLocalIndex] using
    perfect_indexOfSourceTarget_injective K.startPerfect
      (K.localPerfect ⟨0, K.hN⟩)

theorem startPerfect_path_subset_firstPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.firstPrefix.Index) :
    (K.startPerfect.path a).vertexSet ⊆ (K.firstPrefix.path a).vertexSet := by
  exact perfect_left_path_subset_concatOfFirstInternallyDisjoint
    K.startPerfect (K.localPerfect ⟨0, K.hN⟩)
    K.startPerfect_internallyDisjoint_firstEven
    (K.localPerfect_staysIn ⟨0, K.hN⟩)
    K.startPerfect_source_disjoint_firstEven a

/-- The base concatenation preserves the exact provenance-selected trace in
the first cluster. -/
theorem firstPrefix_start_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.firstPrefix.Index) :
    (K.firstPrefix.path a).vertexSet ∩ P.cluster P.firstIndex =
      (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex a)).vertexSet := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvPrefix, hvFirst⟩
    have hsplit :=
      K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
        (K.localPerfect ⟨0, K.hN⟩)
        K.startPerfect_internallyDisjoint_firstEven
        (K.localPerfect_staysIn ⟨0, K.hN⟩)
        K.startPerfect_source_disjoint_firstEven a hvPrefix
    rcases Finset.mem_union.mp hsplit with hvStart | hvLocal
    · have hvTrace :
          v ∈ (K.startPerfect.path a).vertexSet ∩
            P.cluster P.firstIndex :=
        Finset.mem_inter.mpr ⟨hvStart, hvFirst⟩
      rw [K.startPerfect_firstCluster_trace_eq] at hvTrace
      exact hvTrace
    · have hvEven :
          v ∈ P.cluster (evenClusterIndex g ⟨0, K.hN⟩) :=
        K.localPerfect_staysIn ⟨0, K.hN⟩ _ hvLocal
      have hne : P.firstIndex ≠ evenClusterIndex g ⟨0, K.hN⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hval
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvFirst hvEven)
  · intro v hvQ
    have hvTrace :
        v ∈ (K.startPerfect.path a).vertexSet ∩
          P.cluster P.firstIndex := by
      rw [K.startPerfect_firstCluster_trace_eq]
      exact hvQ
    exact Finset.mem_inter.mpr
      ⟨K.startPerfect_path_subset_firstPrefix a (Finset.mem_inter.mp hvTrace).1,
        (Finset.mem_inter.mp hvTrace).2⟩

theorem firstPrefixLocal_path_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (j : Fin (g * (g - 1))) (hj : j.1 ≤ 0)
    (a : K.firstPrefix.Index) :
    ((K.localPerfect j).path (K.firstPrefixLocalIndex j hj a)).vertexSet ⊆
      (K.firstPrefix.path a).vertexSet := by
  have hj0 : j = ⟨0, K.hN⟩ := by
    apply Fin.ext
    simpa using Nat.eq_zero_of_le_zero hj
  subst j
  simpa [firstPrefixLocalIndex] using
    perfect_right_path_subset_concatOfFirstInternallyDisjoint
      K.startPerfect (K.localPerfect ⟨0, K.hN⟩)
      K.startPerfect_internallyDisjoint_firstEven
      (K.localPerfect_staysIn ⟨0, K.hN⟩)
      K.startPerfect_source_disjoint_firstEven a

theorem firstPrefixLocal_trace_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (j : Fin (g * (g - 1))) (hj : j.1 ≤ 0)
    (a : K.firstPrefix.Index) :
    (K.firstPrefix.path a).vertexSet ∩
        P.cluster (evenClusterIndex g j) ⊆
      ((K.localPerfect j).path (K.firstPrefixLocalIndex j hj a)).vertexSet := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvPrefix, hvCluster⟩
  have hj0 : j = ⟨0, K.hN⟩ := by
    apply Fin.ext
    simpa using Nat.eq_zero_of_le_zero hj
  subst j
  have hsplit :=
    K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (K.localPerfect ⟨0, K.hN⟩)
      K.startPerfect_internallyDisjoint_firstEven
      (K.localPerfect_staysIn ⟨0, K.hN⟩)
      K.startPerfect_source_disjoint_firstEven a hvPrefix
  rcases Finset.mem_union.mp hsplit with hvStart | hvLocal
  · rcases K.startPerfect_internallyDisjoint_firstEven a hvStart hvCluster with
      hsource | htarget
    · exact False.elim (Finset.disjoint_left.mp
        K.startPerfect_source_disjoint_firstEven
        (K.startPerfect.source_mem a)
        (by simpa [hsource] using hvCluster))
    · have hglue :
          v = ((K.localPerfect ⟨0, K.hN⟩).path
            (K.startPerfect.indexOfSourceTarget
              (K.localPerfect ⟨0, K.hN⟩) a)).source :=
        htarget.trans
          (K.startPerfect.source_indexOfSourceTarget
            (K.localPerfect ⟨0, K.hN⟩) a).symm
      simpa [firstPrefixLocalIndex, hglue] using
        GraphPath.source_mem_vertexSet
          ((K.localPerfect ⟨0, K.hN⟩).path
            (K.startPerfect.indexOfSourceTarget
              (K.localPerfect ⟨0, K.hN⟩) a))
  · simpa [firstPrefixLocalIndex] using hvLocal

theorem firstPrefix_staysIn_prefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.firstPrefix.toPathPacking.StaysIn
      (stitchingPrefixRegion P (evenClusterIndex g ⟨0, K.hN⟩)) := by
  intro a v hv
  have hvUsed := K.firstPrefix_staysIn a hv
  rcases Finset.mem_union.mp hvUsed with hvFirst | hvEven
  · exact firstStitchingRegion_subset_prefixRegion P K.hN hvFirst
  · exact Finset.mem_union_right _ hvEven

/-- In the base prefix, the first-cluster trace occurs before the trace in the
first even one-based cluster. -/
theorem firstPrefix_clusters_ordered
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    ∀ (a : K.firstPrefix.Index)
      ⦃j k : Fin (2 * g * (g - 1))⦄,
      j.1 < k.1 →
        k.1 ≤ (evenClusterIndex g ⟨0, K.hN⟩).1 →
          ∀ ⦃u v : V⦄,
            u ∈ (K.firstPrefix.path a).vertexSet →
              u ∈ P.cluster j →
                v ∈ (K.firstPrefix.path a).vertexSet →
                  v ∈ P.cluster k →
                    (K.firstPrefix.path a).Before u v := by
  intro a j k hjk hk u v huPath huCluster hvPath hvCluster
  have hjFirst : j = P.firstIndex := by
    apply Fin.ext
    simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hk ⊢
    omega
  have hkEven : k = evenClusterIndex g ⟨0, K.hN⟩ := by
    apply Fin.ext
    simp [evenClusterIndex] at hk ⊢
    omega
  subst j
  subst k
  have huTrace :
      u ∈ (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex a)).vertexSet := by
    rw [← K.firstPrefix_start_trace_eq]
    exact Finset.mem_inter.mpr ⟨huPath, huCluster⟩
  have huStart : u ∈ (K.startPerfect.path a).vertexSet := by
    have huStartTrace :
        u ∈ (K.startPerfect.path a).vertexSet ∩
          P.cluster P.firstIndex := by
      rw [K.startPerfect_firstCluster_trace_eq]
      exact huTrace
    exact (Finset.mem_inter.mp huStartTrace).1
  have hvLocal :
      v ∈ ((K.localPerfect ⟨0, K.hN⟩).path
        (K.startPerfect.indexOfSourceTarget
          (K.localPerfect ⟨0, K.hN⟩) a)).vertexSet := by
    simpa [firstPrefixLocalIndex] using
      K.firstPrefixLocal_trace_subset ⟨0, K.hN⟩ (by simp) a
        (Finset.mem_inter.mpr ⟨hvPath, hvCluster⟩)
  dsimp [firstPrefix,
    PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn,
    PerfectPathPacking.concat]
  exact GraphPath.before_appendWithEq_of_mem_left_of_mem_right _ _ _ _
    huStart hvLocal

/-- The base prefix satisfies the ordering invariant expected of a stitched
prefix.  This is exposed separately from the proof above so later induction
can use the same endpoint without unfolding `firstPrefix`. -/
theorem firstStitchedPrefix_clusters_ordered
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    ∀ (a : K.firstPrefix.Index)
      ⦃j k : Fin (2 * g * (g - 1))⦄,
      j.1 < k.1 →
        k.1 ≤ (evenClusterIndex g ⟨0, K.hN⟩).1 →
          ∀ ⦃u v : V⦄,
            u ∈ (K.firstPrefix.path a).vertexSet →
              u ∈ P.cluster j →
                v ∈ (K.firstPrefix.path a).vertexSet →
                  v ∈ P.cluster k →
                    (K.firstPrefix.path a).Before u v := by
  exact K.firstPrefix_clusters_ordered

/-- Base of the all-even-cluster prefix induction. -/
noncomputable def firstStitchedPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    StitchedPrefix K ⟨0, K.hN⟩ where
  packing := K.firstPrefix
  card_eq := K.firstPrefix_card
  staysIn := K.firstPrefix_staysIn_prefixRegion
  next_cluster_disjoint := by
    intro hi
    exact perfect_vertexSet_disjoint_futureCluster_of_staysIn K.firstPrefix
      K.firstPrefix_staysIn_prefixRegion
      (evenClusterIndex_lt_of_lt (by simp [nextEvenClusterOrdinal]))
  startIndex := fun a => a
  startIndex_injective := fun _ _ h => h
  start_path_subset := K.startPerfect_path_subset_firstPrefix
  start_trace_eq := K.firstPrefix_start_trace_eq
  localIndex := K.firstPrefixLocalIndex
  localIndex_injective := K.firstPrefixLocalIndex_injective
  local_path_subset := K.firstPrefixLocal_path_subset
  local_trace_subset := K.firstPrefixLocal_trace_subset
  betweenIndex := by
    intro j hji
    exact (Nat.not_lt_zero j.1 (by simpa using hji)).elim
  betweenIndex_injective := by
    intro j hji
    exact (Nat.not_lt_zero j.1 (by simpa using hji)).elim
  between_path_subset := by
    intro j hji
    exact (Nat.not_lt_zero j.1 (by simpa using hji)).elim
  between_trace_subset := by
    intro j hji
    simp at hji
  clusters_ordered := K.firstStitchedPrefix_clusters_ordered

/-- Append the two-gap stitching packing after a completed prefix, stopping at
the source terminals of the next local output. -/
noncomputable def StitchedPrefix.toNextSource
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet) :=
  F.packing.concatOfFirstStaysInSecondInternallyDisjoint
    (K.between i hi) F.staysIn
    (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
    (K.nextEvenSource_disjoint_prefixRegion i hi)

@[simp] theorem StitchedPrefix.toNextSource_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    (F.toNextSource hi).card = q := by
  simpa [StitchedPrefix.toNextSource] using F.card_eq

theorem StitchedPrefix.toNextSource_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    (F.toNextSource hi).toPathPacking.StaysIn
      (stitchingPrefixRegion P (evenClusterIndex g i) ∪
        betweenStitchingRegion P i hi) := by
  simpa [StitchedPrefix.toNextSource] using
    F.packing.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      (K.between i hi) F.staysIn
      (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
      (K.nextEvenSource_disjoint_prefixRegion i hi)
      (K.betweenPerfect_staysIn i hi)

/-- The half-step prefix is internally disjoint from the next even cluster,
so the next local output can be appended. -/
theorem StitchedPrefix.toNextSource_internallyDisjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    (F.toNextSource hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  dsimp [StitchedPrefix.toNextSource,
    PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint]
  apply PerfectPathPacking.concat_internallyDisjointFromSet_right
  · exact F.next_cluster_disjoint hi
  · exact K.localTarget_disjoint_nextEvenCluster i hi
  · exact K.betweenPerfect_internallyDisjoint_right i hi

/-- Complete the successor step by appending the local output in the next even
cluster. -/
noncomputable def StitchedPrefix.extendPacking
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal i hi)).paths.targetSet) :=
  (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn
    (K.localPerfect (nextEvenClusterOrdinal i hi))
    (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
    (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
    (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))

@[simp] theorem StitchedPrefix.extendPacking_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    (F.extendPacking hi).card = q := by
  simpa [StitchedPrefix.extendPacking] using F.toNextSource_card hi

theorem StitchedPrefix.extendPacking_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    (F.extendPacking hi).toPathPacking.StaysIn
      (stitchingPrefixRegion P
        (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  have hStep :
      (F.extendPacking hi).toPathPacking.StaysIn
        ((stitchingPrefixRegion P (evenClusterIndex g i) ∪
            betweenStitchingRegion P i hi) ∪
          P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
    simpa [StitchedPrefix.extendPacking] using
      PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
          (F.toNextSource hi)
          (K.localPerfect (nextEvenClusterOrdinal i hi))
          (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
          (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
          (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
          (F.toNextSource_staysIn hi)
  intro a v hv
  exact stitchingStepRegion_subset_nextPrefixRegion P i hi (hStep a hv)

theorem StitchedPrefix.packing_path_subset_toNextSource
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.toNextSource hi).Index) :
    (F.packing.path a).vertexSet ⊆
      ((F.toNextSource hi).path a).vertexSet := by
  exact perfect_left_path_subset_concatOfFirstStays F.packing (K.between i hi)
    F.staysIn (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
    (K.nextEvenSource_disjoint_prefixRegion i hi) a

theorem StitchedPrefix.between_path_subset_toNextSource
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.toNextSource hi).Index) :
    ((K.between i hi).path
        (F.packing.indexOfSourceTarget (K.between i hi) a)).vertexSet ⊆
      ((F.toNextSource hi).path a).vertexSet := by
  exact perfect_right_path_subset_concatOfFirstStays F.packing (K.between i hi)
    F.staysIn (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
    (K.nextEvenSource_disjoint_prefixRegion i hi) a

theorem StitchedPrefix.toNextSource_path_subset_extendPacking
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index) :
    ((F.toNextSource hi).path a).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  exact perfect_left_path_subset_concatOfFirstInternallyDisjoint
    (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
    (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
    (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
    (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a

theorem StitchedPrefix.nextLocal_path_subset_extendPacking
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index) :
    ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
        ((F.toNextSource hi).indexOfSourceTarget
          (K.localPerfect (nextEvenClusterOrdinal i hi)) a)).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  exact perfect_right_path_subset_concatOfFirstInternallyDisjoint
    (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
    (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
    (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
    (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a

/-- A vertex of an extended row lying in a cluster of the completed prefix
already belongs to the old row path. -/
theorem StitchedPrefix.mem_packing_of_mem_extendPacking_of_cluster_le
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index)
    {j : Fin (2 * g * (g - 1))} {v : V}
    (hvPath : v ∈ ((F.extendPacking hi).path a).vertexSet)
    (hvCluster : v ∈ P.cluster j)
    (hj : j.1 ≤ (evenClusterIndex g i).1) :
    v ∈ (F.packing.path a).vertexSet := by
  have hsplit :=
    (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (K.localPerfect (nextEvenClusterOrdinal i hi))
      (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
      (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
      a hvPath
  rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
  · have hsplitHalf :=
      F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
        (K.between i hi) F.staysIn
        (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
        (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
    rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
    · exact hvOld
    · have hvPrefix :
          v ∈ stitchingPrefixRegion P (evenClusterIndex g i) := by
        rcases lt_or_eq_of_le hj with hjlt | hjeq
        · exact Finset.mem_union_left _
            (cluster_subset_strictStitchingPrefixRegion P hjlt hvCluster)
        · have hjEq : j = evenClusterIndex g i := Fin.ext hjeq
          subst j
          exact Finset.mem_union_right _ hvCluster
      rcases K.betweenPerfect_internallyDisjoint_prefixRegion i hi
          (F.packing.indexOfSourceTarget (K.between i hi) a)
          hvBetween hvPrefix with hsource | htarget
      · have htargetEq : v = (F.packing.path a).target :=
          hsource.trans
            (F.packing.source_indexOfSourceTarget (K.between i hi) a)
        rw [htargetEq]
        exact GraphPath.target_mem_vertexSet (F.packing.path a)
      · exact False.elim (Finset.disjoint_left.mp
          (K.nextEvenSource_disjoint_prefixRegion i hi)
          ((K.between i hi).target_mem
            (F.packing.indexOfSourceTarget (K.between i hi) a))
          (by simpa [htarget] using hvPrefix))
  · have hvNext :
        v ∈ P.cluster
          (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
      K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
    have hne :
        j ≠ evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
      intro h
      have hval := congrArg Fin.val h
      simp [evenClusterIndex, nextEvenClusterOrdinal] at hj hval
      omega
    exact False.elim
      (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvCluster hvNext)

/-- A vertex of an extended row in the newly completed intervening odd
cluster belongs to the current between-piece path. -/
theorem StitchedPrefix.mem_between_of_mem_extendPacking_of_currentOdd
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index) {v : V}
    (hvPath : v ∈ ((F.extendPacking hi).path a).vertexSet)
    (hvOdd : v ∈ P.cluster (oddClusterAfterEvenIndex g i hi)) :
    v ∈ ((K.between i hi).path
      (F.packing.indexOfSourceTarget (K.between i hi) a)).vertexSet := by
  have hsplit :=
    (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (K.localPerfect (nextEvenClusterOrdinal i hi))
      (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
      (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
      a hvPath
  rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
  · have hsplitHalf :=
      F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
        (K.between i hi) F.staysIn
        (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
        (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
    rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
    · have hvPrefix := F.staysIn a hvOld
      exact False.elim (Finset.disjoint_left.mp
        (stitchingPrefixRegion_disjoint_cluster_of_lt P (by
          simp [evenClusterIndex, oddClusterAfterEvenIndex]))
        hvPrefix hvOdd)
    · exact hvBetween
  · have hvNext :
        v ∈ P.cluster
          (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
      K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
    have hne :
        oddClusterAfterEvenIndex g i hi ≠
          evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
      intro h
      have hval := congrArg Fin.val h
      simp [oddClusterAfterEvenIndex, evenClusterIndex,
        nextEvenClusterOrdinal] at hval
      omega
    exact False.elim
      (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvOdd hvNext)

/-- A vertex of an extended row in the next even one-based cluster belongs to
the newly appended local path. -/
theorem StitchedPrefix.mem_nextLocal_of_mem_extendPacking_of_nextEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index) {v : V}
    (hvPath : v ∈ ((F.extendPacking hi).path a).vertexSet)
    (hvNext : v ∈
      P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :
    v ∈ ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
      ((F.toNextSource hi).indexOfSourceTarget
        (K.localPerfect (nextEvenClusterOrdinal i hi)) a)).vertexSet := by
  have hsplit :=
    (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (K.localPerfect (nextEvenClusterOrdinal i hi))
      (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
      (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
      a hvPath
  rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
  · rcases F.toNextSource_internallyDisjoint_nextEvenCluster hi a
        hvHalf hvNext with hsource | htarget
    · exact False.elim (Finset.disjoint_left.mp
        (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
        ((F.toNextSource hi).source_mem a)
        (by simpa [hsource] using hvNext))
    · have hglue :
          v = ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
            ((F.toNextSource hi).indexOfSourceTarget
              (K.localPerfect (nextEvenClusterOrdinal i hi)) a)).source :=
        htarget.trans
          ((F.toNextSource hi).source_indexOfSourceTarget
            (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
      simpa [hglue] using GraphPath.source_mem_vertexSet
        ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
          ((F.toNextSource hi).indexOfSourceTarget
            (K.localPerfect (nextEvenClusterOrdinal i hi)) a))
  · exact hvLocal

/-- A successor step adds no new vertices to the first-cluster trace. -/
theorem StitchedPrefix.extendStart_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (a : (F.extendPacking hi).Index) :
    ((F.extendPacking hi).path a).vertexSet ∩ P.cluster P.firstIndex =
      (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex (F.startIndex a))).vertexSet := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvExtend, hvFirst⟩
    have hsplit :=
      (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
        (K.localPerfect (nextEvenClusterOrdinal i hi))
        (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
        (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
        (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
        a hvExtend
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · have hsplitHalf :=
        F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          (K.between i hi) F.staysIn
          (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
          (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
      rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
      · have hvTrace :
            v ∈ (F.packing.path a).vertexSet ∩ P.cluster P.firstIndex :=
          Finset.mem_inter.mpr ⟨hvOld, hvFirst⟩
        rw [F.start_trace_eq] at hvTrace
        exact hvTrace
      · have hvPrefix :
            v ∈ stitchingPrefixRegion P (evenClusterIndex g i) :=
          Finset.mem_union_left _
            (cluster_subset_strictStitchingPrefixRegion P (by
              simp [PathOfSetsSystem.firstIndex, evenClusterIndex]) hvFirst)
        rcases K.betweenPerfect_internallyDisjoint_prefixRegion i hi
            (F.packing.indexOfSourceTarget (K.between i hi) a)
            hvBetween hvPrefix with hsource | htarget
        · have hvOld : v ∈ (F.packing.path a).vertexSet := by
            have htarget_eq : v = (F.packing.path a).target :=
              hsource.trans
                (F.packing.source_indexOfSourceTarget (K.between i hi) a)
            rw [htarget_eq]
            exact GraphPath.target_mem_vertexSet (F.packing.path a)
          have hvTrace :
              v ∈ (F.packing.path a).vertexSet ∩ P.cluster P.firstIndex :=
            Finset.mem_inter.mpr ⟨hvOld, hvFirst⟩
          rw [F.start_trace_eq] at hvTrace
          exact hvTrace
        · exact False.elim (Finset.disjoint_left.mp
            (K.nextEvenSource_disjoint_prefixRegion i hi)
            ((K.between i hi).target_mem
              (F.packing.indexOfSourceTarget (K.between i hi) a))
            (by simpa [htarget] using hvPrefix))
    · have hvNext :
          v ∈ P.cluster
            (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
        K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
      have hne :
          P.firstIndex ≠ evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
        intro h
        have hval := congrArg Fin.val h
        simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hval
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvFirst hvNext)
  · intro v hvQ
    have hvOldTrace :
        v ∈ (F.packing.path a).vertexSet ∩ P.cluster P.firstIndex := by
      rw [F.start_trace_eq]
      exact hvQ
    exact Finset.mem_inter.mpr
      ⟨F.toNextSource_path_subset_extendPacking hi a
          (F.packing_path_subset_toNextSource hi a
            (Finset.mem_inter.mp hvOldTrace).1),
        (Finset.mem_inter.mp hvOldTrace).2⟩

/-- Local-piece provenance after one successor step. -/
noncomputable def StitchedPrefix.extendLocalIndex
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 ≤ (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    (K.localPerfect j).Index := by
  by_cases hnew : j = nextEvenClusterOrdinal i hi
  · subst j
    exact (F.toNextSource hi).indexOfSourceTarget
      (K.localPerfect (nextEvenClusterOrdinal i hi)) a
  · have hval_ne : j.1 ≠ (nextEvenClusterOrdinal i hi).1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hji : j.1 ≤ i.1 := by
      simp [nextEvenClusterOrdinal] at hj hval_ne
      omega
    exact F.localIndex j hji a

theorem StitchedPrefix.extendLocalIndex_injective
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 ≤ (nextEvenClusterOrdinal i hi).1) :
    Function.Injective (F.extendLocalIndex hi j hj) := by
  by_cases hnew : j = nextEvenClusterOrdinal i hi
  · subst j
    intro a b hab
    apply perfect_indexOfSourceTarget_injective (F.toNextSource hi)
      (K.localPerfect (nextEvenClusterOrdinal i hi))
    simpa [StitchedPrefix.extendLocalIndex] using hab
  · have hval_ne : j.1 ≠ (nextEvenClusterOrdinal i hi).1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hji : j.1 ≤ i.1 := by
      simp [nextEvenClusterOrdinal] at hj hval_ne
      omega
    intro a b hab
    apply F.localIndex_injective j hji
    simpa [StitchedPrefix.extendLocalIndex, hnew] using hab

theorem StitchedPrefix.extendLocal_path_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 ≤ (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    ((K.localPerfect j).path (F.extendLocalIndex hi j hj a)).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  by_cases hnew : j = nextEvenClusterOrdinal i hi
  · subst j
    simpa [StitchedPrefix.extendLocalIndex] using
      F.nextLocal_path_subset_extendPacking hi a
  · have hval_ne : j.1 ≠ (nextEvenClusterOrdinal i hi).1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hji : j.1 ≤ i.1 := by
      simp [nextEvenClusterOrdinal] at hj hval_ne
      omega
    calc
      ((K.localPerfect j).path
          (F.extendLocalIndex hi j hj a)).vertexSet ⊆
          (F.packing.path a).vertexSet := by
        simpa [StitchedPrefix.extendLocalIndex, hnew] using
          F.local_path_subset j hji a
      _ ⊆ ((F.toNextSource hi).path a).vertexSet :=
        F.packing_path_subset_toNextSource hi a
      _ ⊆ ((F.extendPacking hi).path a).vertexSet :=
        F.toNextSource_path_subset_extendPacking hi a

theorem StitchedPrefix.extendLocal_trace_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 ≤ (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    ((F.extendPacking hi).path a).vertexSet ∩
        P.cluster (evenClusterIndex g j) ⊆
      ((K.localPerfect j).path (F.extendLocalIndex hi j hj a)).vertexSet := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvExtend, hvCluster⟩
  have hsplit :=
    (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
        (K.localPerfect (nextEvenClusterOrdinal i hi))
        (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
        (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
        (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
        a hvExtend
  by_cases hnew : j = nextEvenClusterOrdinal i hi
  · subst j
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · rcases F.toNextSource_internallyDisjoint_nextEvenCluster hi a
          hvHalf hvCluster with hsource | htarget
      · exact False.elim (Finset.disjoint_left.mp
          (K.startSource_disjoint_evenCluster
            (nextEvenClusterOrdinal i hi))
          ((F.toNextSource hi).source_mem a)
          (by simpa [hsource] using hvCluster))
      · have hglue :
            v = ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
              ((F.toNextSource hi).indexOfSourceTarget
                (K.localPerfect (nextEvenClusterOrdinal i hi)) a)).source :=
          htarget.trans
            ((F.toNextSource hi).source_indexOfSourceTarget
              (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
        simpa [StitchedPrefix.extendLocalIndex, hglue] using
          GraphPath.source_mem_vertexSet
            ((K.localPerfect (nextEvenClusterOrdinal i hi)).path
              ((F.toNextSource hi).indexOfSourceTarget
                (K.localPerfect (nextEvenClusterOrdinal i hi)) a))
    · simpa [StitchedPrefix.extendLocalIndex] using hvLocal
  · have hval_ne : j.1 ≠ (nextEvenClusterOrdinal i hi).1 := by
      intro hval
      exact hnew (Fin.ext hval)
    have hji : j.1 ≤ i.1 := by
      simp [nextEvenClusterOrdinal] at hj hval_ne
      omega
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · have hsplitHalf :=
        F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
            (K.between i hi) F.staysIn
            (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
            (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
      rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
      · simpa [StitchedPrefix.extendLocalIndex, hnew] using
          F.local_trace_subset j hji a
            (Finset.mem_inter.mpr ⟨hvOld, hvCluster⟩)
      · have hvPrefix :
            v ∈ stitchingPrefixRegion P (evenClusterIndex g i) := by
          rcases lt_or_eq_of_le hji with hlt | heq
          · exact Finset.mem_union_left _
              (cluster_subset_strictStitchingPrefixRegion P
                (evenClusterIndex_lt_of_lt hlt) hvCluster)
          · have hji_eq : j = i := Fin.ext heq
            subst j
            exact Finset.mem_union_right _ hvCluster
        rcases K.betweenPerfect_internallyDisjoint_prefixRegion i hi
            (F.packing.indexOfSourceTarget (K.between i hi) a)
            hvBetween hvPrefix with hsource | htarget
        · have hvOld : v ∈ (F.packing.path a).vertexSet := by
            have htarget_eq : v = (F.packing.path a).target :=
              hsource.trans
                (F.packing.source_indexOfSourceTarget (K.between i hi) a)
            rw [htarget_eq]
            exact GraphPath.target_mem_vertexSet (F.packing.path a)
          simpa [StitchedPrefix.extendLocalIndex, hnew] using
            F.local_trace_subset j hji a
              (Finset.mem_inter.mpr ⟨hvOld, hvCluster⟩)
        · exact False.elim (Finset.disjoint_left.mp
            (K.nextEvenSource_disjoint_prefixRegion i hi)
            ((K.between i hi).target_mem
              (F.packing.indexOfSourceTarget (K.between i hi) a))
            (by simpa [htarget] using hvPrefix))
    · have hvNext :
          v ∈ P.cluster
            (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
        K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
      have hne :
          evenClusterIndex g j ≠
            evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
        intro h
        exact hnew (evenClusterIndex_injective h)
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne)
          hvCluster hvNext)

/-- Between-piece provenance after one successor step. -/
noncomputable def StitchedPrefix.extendBetweenIndex
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 < (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    (K.between j (evenClusterOrdinal_succ_lt_of_lt hj)).Index := by
  by_cases hcurrent : j = i
  · subst j
    exact F.packing.indexOfSourceTarget (K.between i hi) a
  · have hval_ne : j.1 ≠ i.1 := by
      intro hval
      exact hcurrent (Fin.ext hval)
    have hji : j.1 < i.1 := by
      simp [nextEvenClusterOrdinal] at hj
      omega
    exact F.betweenIndex j hji a

theorem StitchedPrefix.extendBetweenIndex_injective
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 < (nextEvenClusterOrdinal i hi).1) :
    Function.Injective (F.extendBetweenIndex hi j hj) := by
  by_cases hcurrent : j = i
  · subst j
    intro a b hab
    apply perfect_indexOfSourceTarget_injective F.packing (K.between i hi)
    simpa [StitchedPrefix.extendBetweenIndex] using hab
  · have hval_ne : j.1 ≠ i.1 := by
      intro hval
      exact hcurrent (Fin.ext hval)
    have hji : j.1 < i.1 := by
      simp [nextEvenClusterOrdinal] at hj
      omega
    intro a b hab
    apply F.betweenIndex_injective j hji
    simpa [StitchedPrefix.extendBetweenIndex, hcurrent] using hab

theorem StitchedPrefix.extendBetween_path_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 < (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    ((K.between j (evenClusterOrdinal_succ_lt_of_lt hj)).path
        (F.extendBetweenIndex hi j hj a)).vertexSet ⊆
      ((F.extendPacking hi).path a).vertexSet := by
  by_cases hcurrent : j = i
  · subst j
    calc
      ((K.between i (evenClusterOrdinal_succ_lt_of_lt hj)).path
          (F.extendBetweenIndex hi i hj a)).vertexSet ⊆
          ((F.toNextSource hi).path a).vertexSet := by
        simpa [StitchedPrefix.extendBetweenIndex] using
          F.between_path_subset_toNextSource hi a
      _ ⊆ ((F.extendPacking hi).path a).vertexSet :=
        F.toNextSource_path_subset_extendPacking hi a
  · have hval_ne : j.1 ≠ i.1 := by
      intro hval
      exact hcurrent (Fin.ext hval)
    have hji : j.1 < i.1 := by
      simp [nextEvenClusterOrdinal] at hj
      omega
    calc
      ((K.between j (evenClusterOrdinal_succ_lt_of_lt hj)).path
          (F.extendBetweenIndex hi j hj a)).vertexSet ⊆
          (F.packing.path a).vertexSet := by
        simpa [StitchedPrefix.extendBetweenIndex, hcurrent] using
          F.between_path_subset j hji a
      _ ⊆ ((F.toNextSource hi).path a).vertexSet :=
        F.packing_path_subset_toNextSource hi a
      _ ⊆ ((F.extendPacking hi).path a).vertexSet :=
        F.toNextSource_path_subset_extendPacking hi a

/-- Exact odd-cluster exclusion after one successor step.  For the newly
completed odd cluster only the current between piece can contribute; for an
older odd cluster only the old prefix can contribute. -/
theorem StitchedPrefix.extendBetween_trace_subset
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1))
    (j : Fin (g * (g - 1)))
    (hj : j.1 < (nextEvenClusterOrdinal i hi).1)
    (a : (F.extendPacking hi).Index) :
    ((F.extendPacking hi).path a).vertexSet ∩
        P.cluster (oddClusterAfterEvenIndex g j
          (evenClusterOrdinal_succ_lt_of_lt hj)) ⊆
      ((K.between_provenance j
          (evenClusterOrdinal_succ_lt_of_lt hj)).middle.path
        ((K.between_provenance j
            (evenClusterOrdinal_succ_lt_of_lt hj)).indexEquiv
          (F.extendBetweenIndex hi j hj a))).vertexSet := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hvExtend, hvOdd⟩
  have hsplit :=
    (F.toNextSource hi).concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      (K.localPerfect (nextEvenClusterOrdinal i hi))
      (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
      (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi))
      a hvExtend
  by_cases hcurrent : j = i
  · subst j
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · have hsplitHalf :=
        F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          (K.between i hi) F.staysIn
          (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
          (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
      rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
      · have hvOldRegion := F.staysIn a hvOld
        exact False.elim (Finset.disjoint_left.mp
          (stitchingPrefixRegion_disjoint_cluster_of_lt P (by
            simp [evenClusterIndex, oddClusterAfterEvenIndex]))
          hvOldRegion hvOdd)
      · have hvTrace :
            v ∈ ((K.between i hi).path
                (F.packing.indexOfSourceTarget (K.between i hi) a)).vertexSet ∩
              P.cluster (oddClusterAfterEvenIndex g i hi) :=
          Finset.mem_inter.mpr ⟨hvBetween, hvOdd⟩
        rw [(K.between_provenance i hi).trace_eq] at hvTrace
        simpa [StitchedPrefix.extendBetweenIndex] using hvTrace
    · have hvNext :
          v ∈ P.cluster
            (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
        K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
      have hne :
          oddClusterAfterEvenIndex g i hi ≠
            evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
        intro h
        have hval := congrArg Fin.val h
        simp [oddClusterAfterEvenIndex, evenClusterIndex,
          nextEvenClusterOrdinal] at hval
        omega
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvOdd hvNext)
  · have hval_ne : j.1 ≠ i.1 := by
      intro hval
      exact hcurrent (Fin.ext hval)
    have hji : j.1 < i.1 := by
      simp [nextEvenClusterOrdinal] at hj
      omega
    rcases Finset.mem_union.mp hsplit with hvHalf | hvLocal
    · have hsplitHalf :=
        F.packing.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
          (K.between i hi) F.staysIn
          (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
          (K.nextEvenSource_disjoint_prefixRegion i hi) a hvHalf
      rcases Finset.mem_union.mp hsplitHalf with hvOld | hvBetween
      · simpa [StitchedPrefix.extendBetweenIndex, hcurrent] using
          F.between_trace_subset j hji a
            (Finset.mem_inter.mpr ⟨hvOld, hvOdd⟩)
      · have hvBetweenRegion : v ∈ betweenStitchingRegion P i hi :=
          K.betweenPerfect_staysIn i hi _ hvBetween
        have hvStrict :
            v ∈ strictStitchingPrefixRegion P (evenClusterIndex g i) :=
          cluster_subset_strictStitchingPrefixRegion P (by
            simp [oddClusterAfterEvenIndex, evenClusterIndex]
            omega) hvOdd
        exact False.elim (Finset.disjoint_left.mp
          (betweenStitchingRegion_disjoint_strictPrefixRegion P i hi)
          hvBetweenRegion hvStrict)
    · have hvNext :
          v ∈ P.cluster
            (evenClusterIndex g (nextEvenClusterOrdinal i hi)) :=
        K.localPerfect_staysIn (nextEvenClusterOrdinal i hi) _ hvLocal
      have hne :
          oddClusterAfterEvenIndex g j
              (evenClusterOrdinal_succ_lt_of_lt hj) ≠
            evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
        intro h
        have hval := congrArg Fin.val h
        simp [oddClusterAfterEvenIndex, evenClusterIndex,
          nextEvenClusterOrdinal] at hval
        omega
      exact False.elim
        (Finset.disjoint_left.mp (P.cluster_disjoint hne) hvOdd hvNext)

/-- Successor constructor for the all-even-cluster prefix invariant. -/
noncomputable def StitchedPrefix.extend
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    {K : StitchingPieces P E} {i : Fin (g * (g - 1))}
    (F : StitchedPrefix K i) (hi : i.1 + 1 < g * (g - 1)) :
    StitchedPrefix K (nextEvenClusterOrdinal i hi) where
  packing := F.extendPacking hi
  card_eq := F.extendPacking_card hi
  staysIn := F.extendPacking_staysIn hi
  next_cluster_disjoint := by
    intro hnext
    exact perfect_vertexSet_disjoint_futureCluster_of_staysIn
      (F.extendPacking hi) (F.extendPacking_staysIn hi)
      (evenClusterIndex_lt_of_lt (by simp [nextEvenClusterOrdinal]))
  startIndex := F.startIndex
  startIndex_injective := F.startIndex_injective
  start_path_subset := by
    intro a
    calc
      (K.startPerfect.path (F.startIndex a)).vertexSet ⊆
          (F.packing.path a).vertexSet := F.start_path_subset a
      _ ⊆ ((F.toNextSource hi).path a).vertexSet :=
        F.packing_path_subset_toNextSource hi a
      _ ⊆ ((F.extendPacking hi).path a).vertexSet :=
        F.toNextSource_path_subset_extendPacking hi a
  start_trace_eq := F.extendStart_trace_eq hi
  localIndex := F.extendLocalIndex hi
  localIndex_injective := F.extendLocalIndex_injective hi
  local_path_subset := F.extendLocal_path_subset hi
  local_trace_subset := F.extendLocal_trace_subset hi
  betweenIndex := F.extendBetweenIndex hi
  betweenIndex_injective := F.extendBetweenIndex_injective hi
  between_path_subset := F.extendBetween_path_subset hi
  between_trace_subset := F.extendBetween_trace_subset hi
  clusters_ordered := by
    intro a j k hjk hk u v hu hju hv hkv
    rcases clusterIndex_le_nextEven_cases i hi k hk with hold | hodd | hnew
    · have hjold : j.1 ≤ (evenClusterIndex g i).1 := by omega
      have huOld := F.mem_packing_of_mem_extendPacking_of_cluster_le hi a hu hju hjold
      have hvOld := F.mem_packing_of_mem_extendPacking_of_cluster_le hi a hv hkv hold
      have hOld := F.clusters_ordered a hjk hold huOld hju hvOld hkv
      have hInner :
          (F.packing.concatOfFirstStaysInSecondInternallyDisjoint
            (K.between i hi) F.staysIn
            (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
            (K.nextEvenSource_disjoint_prefixRegion i hi)).path a |>.Before u v := by
        exact GraphPath.before_appendWithEq_of_left _ _
          (F.packing.source_indexOfSourceTarget (K.between i hi) a).symm
          _ hOld
      simpa [StitchedPrefix.extendPacking, StitchedPrefix.toNextSource] using
        GraphPath.before_appendWithEq_of_left _ _
          ((F.toNextSource hi).source_indexOfSourceTarget
            (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
          (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
            (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
            (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
            (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
            (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a)
          hInner
    · have hjold : j.1 ≤ (evenClusterIndex g i).1 := by
        rw [hodd] at hjk
        simp [evenClusterIndex, oddClusterAfterEvenIndex] at hjk ⊢
        omega
      have huOld := F.mem_packing_of_mem_extendPacking_of_cluster_le hi a hu hju hjold
      have hvBetween := F.mem_between_of_mem_extendPacking_of_currentOdd hi a hv
        (by simpa [hodd] using hkv)
      have hOld : u ∈ ((F.toNextSource hi).path a).vertexSet :=
        F.packing_path_subset_toNextSource hi a huOld
      have hBetween : v ∈ ((F.toNextSource hi).path a).vertexSet :=
        F.between_path_subset_toNextSource hi a hvBetween
      have hInner :
          (F.packing.concatOfFirstStaysInSecondInternallyDisjoint
            (K.between i hi) F.staysIn
            (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
            (K.nextEvenSource_disjoint_prefixRegion i hi)).path a |>.Before u v := by
        exact GraphPath.before_appendWithEq_of_mem_left_of_mem_right _ _
          ((F.packing.source_indexOfSourceTarget (K.between i hi) a).symm)
          (PerfectPathPacking.concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
            F.packing (K.between i hi) F.staysIn
            (K.betweenPerfect_internallyDisjoint_prefixRegion i hi)
            (K.nextEvenSource_disjoint_prefixRegion i hi) a)
          (ha := huOld) (hb := hvBetween)
      simpa [StitchedPrefix.extendPacking, StitchedPrefix.toNextSource] using
        GraphPath.before_appendWithEq_of_left _ _
          ((F.toNextSource hi).source_indexOfSourceTarget
            (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
          (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
            (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
            (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
            (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
            (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a)
          hInner
    · have hjlt : j.1 <
          (evenClusterIndex g (nextEvenClusterOrdinal i hi)).1 := by
        simpa [hnew] using hjk
      rcases clusterIndex_lt_nextEven_cases i hi j hjlt with hjold | hjodd
      · have huOld := F.mem_packing_of_mem_extendPacking_of_cluster_le hi a hu hju hjold
        have hOld : u ∈ ((F.toNextSource hi).path a).vertexSet :=
          F.packing_path_subset_toNextSource hi a huOld
        have hLocal := F.mem_nextLocal_of_mem_extendPacking_of_nextEven hi a hv
          (by simpa [hnew] using hkv)
        simpa [StitchedPrefix.extendPacking] using
          GraphPath.before_appendWithEq_of_mem_left_of_mem_right _ _
            ((F.toNextSource hi).source_indexOfSourceTarget
              (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
            (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
              (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
              (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
              (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
              (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a)
            (ha := hOld) (hb := hLocal)
      · have huBetween := F.mem_between_of_mem_extendPacking_of_currentOdd hi a hu
          (by simpa [hjodd] using hju)
        have hLocal := F.mem_nextLocal_of_mem_extendPacking_of_nextEven hi a hv
          (by simpa [hnew] using hkv)
        have huNext : u ∈ ((F.toNextSource hi).path a).vertexSet :=
          F.between_path_subset_toNextSource hi a huBetween
        simpa [StitchedPrefix.extendPacking] using
          GraphPath.before_appendWithEq_of_mem_left_of_mem_right _ _
            ((F.toNextSource hi).source_indexOfSourceTarget
              (K.localPerfect (nextEvenClusterOrdinal i hi)) a).symm
            (PerfectPathPacking.concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
              (F.toNextSource hi) (K.localPerfect (nextEvenClusterOrdinal i hi))
              (F.toNextSource_internallyDisjoint_nextEvenCluster hi)
              (K.localPerfect_staysIn (nextEvenClusterOrdinal i hi))
              (K.startSource_disjoint_evenCluster (nextEvenClusterOrdinal i hi)) a)
            (ha := huNext) (hb := hLocal)

/-- Build the stitched prefix at a natural ordinal carrying its range proof. -/
noncomputable def stitchedPrefixNat
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (n : ℕ) (hn : n < g * (g - 1)) :
    StitchedPrefix K ⟨n, hn⟩ :=
  match n with
  | 0 => K.firstStitchedPrefix
  | n + 1 =>
      (stitchedPrefixNat K n (lt_trans (Nat.lt_succ_self n) hn)).extend hn

/-- The provenance-preserving stitched prefix through any even-cluster
ordinal. -/
noncomputable def stitchedPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    StitchedPrefix K i := by
  simpa using stitchedPrefixNat K i.1 i.2

@[simp] theorem stitchedPrefix_zero
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.stitchedPrefix ⟨0, K.hN⟩ = K.firstStitchedPrefix := by
  rfl

@[simp] theorem stitchedPrefix_succ
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    K.stitchedPrefix (nextEvenClusterOrdinal i hi) =
      (K.stitchedPrefix i).extend hi := by
  rfl

/-- The completed prefix through the last even one-based cluster. -/
noncomputable def finalStitchedPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    StitchedPrefix K (lastEvenClusterOrdinal K.hN) :=
  K.stitchedPrefix (lastEvenClusterOrdinal K.hN)

/-- The completed row packing with the terminal interface required by
`StitchedRows`.  Widening terminals changes neither paths nor indices. -/
noncomputable def stitchedRowPacking
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    PathPacking G (P.left P.firstIndex) (P.right P.lastIndex) :=
  K.finalStitchedPrefix.packing.toPathPacking.widenTerminals
    K.start.sourceSet_subset_left (by
      intro v hv
      rw [← evenClusterIndex_lastEven_eq_lastIndex P.toPathOfSetsSystem K.hN]
      exact (E.output (lastEvenClusterOrdinal K.hN)).paths.targetSet_subset_right hv)

@[simp] theorem stitchedRowPacking_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.stitchedRowPacking.card = q := by
  exact K.finalStitchedPrefix.card_eq

theorem stitchedRowPacking_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.stitchedRowPacking.StaysIn
      (stitchingPrefixRegion P P.lastIndex) := by
  intro a v hv
  have hvPrefix := K.finalStitchedPrefix.staysIn a (by
    simpa [stitchedRowPacking, PathPacking.widenTerminals] using hv)
  simpa [evenClusterIndex_lastEven_eq_lastIndex P.toPathOfSetsSystem K.hN]
    using hvPrefix

/-- Every even-cluster ordinal is at most the final ordinal. -/
theorem evenClusterOrdinal_le_last
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1))) :
    j.1 ≤ (lastEvenClusterOrdinal K.hN).1 := by
  simp [lastEvenClusterOrdinal]
  omega

/-- An even-cluster ordinal with a successor lies strictly before the final
ordinal, so its following odd cluster occurs in the completed prefix. -/
theorem evenClusterOrdinal_lt_last_of_succ_lt
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (hj : j.1 + 1 < g * (g - 1)) :
    j.1 < (lastEvenClusterOrdinal K.hN).1 := by
  simp [lastEvenClusterOrdinal]
  omega

/-- In the completed prefix, the first-cluster trace is exactly the retained
path from the initial full-width left-to-right linkage. -/
theorem finalStitchedPrefix_firstCluster_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).vertexSet ∩
        P.cluster P.firstIndex =
      (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex
          (K.finalStitchedPrefix.startIndex a))).vertexSet :=
  K.finalStitchedPrefix.start_trace_eq a

/-- Every completed-prefix row has a path-shaped trace in the first cluster. -/
theorem finalStitchedPrefix_traceOn_firstCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).TraceOn
      (P.cluster P.firstIndex) :=
  K.finalStitchedPrefix.traceOn_firstCluster a

/-- In the completed prefix, a row's intersection with every intervening odd
cluster is exactly the middle path selected by between-piece provenance. -/
theorem finalStitchedPrefix_between_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (hj : j.1 + 1 < g * (g - 1))
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).vertexSet ∩
        P.cluster (oddClusterAfterEvenIndex g j hj) =
      ((K.between_provenance j hj).middle.path
        ((K.between_provenance j hj).indexEquiv
          (K.finalStitchedPrefix.betweenIndex j
            (K.evenClusterOrdinal_lt_last_of_succ_lt j hj) a))).vertexSet := by
  simpa using K.finalStitchedPrefix.between_trace_eq j
    (K.evenClusterOrdinal_lt_last_of_succ_lt j hj) a

/-- Every completed-prefix row has a path-shaped trace in each intervening odd
cluster. -/
theorem finalStitchedPrefix_traceOn_oddClusterAfterEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (hj : j.1 + 1 < g * (g - 1))
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).TraceOn
      (P.cluster (oddClusterAfterEvenIndex g j hj)) := by
  simpa using K.finalStitchedPrefix.traceOn_oddClusterAfterEven j
    (K.evenClusterOrdinal_lt_last_of_succ_lt j hj) a

/-- In the completed prefix, a row's intersection with an even cluster is
exactly the corresponding local path. -/
theorem finalStitchedPrefix_local_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).vertexSet ∩
        P.cluster (evenClusterIndex g j) =
      ((K.localPerfect j).path
        (K.finalStitchedPrefix.localIndex j
          (K.evenClusterOrdinal_le_last j) a)).vertexSet := by
  exact K.finalStitchedPrefix.local_trace_eq j
    (K.evenClusterOrdinal_le_last j) a

/-- Every completed-prefix row has a path-shaped trace in every even
cluster. -/
theorem finalStitchedPrefix_traceOn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (a : K.finalStitchedPrefix.packing.Index) :
    (K.finalStitchedPrefix.packing.path a).TraceOn
      (P.cluster (evenClusterIndex g j)) := by
  exact K.finalStitchedPrefix.traceOn_evenCluster j
    (K.evenClusterOrdinal_le_last j) a

/-- Widening the terminal interface preserves the exact provenance-selected
trace in the first cluster. -/
theorem stitchedRowPacking_firstCluster_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).vertexSet ∩ P.cluster P.firstIndex =
      (K.start_provenance.leftRight.path
        (K.startFirstClusterIndex
          (K.finalStitchedPrefix.startIndex a))).vertexSet := by
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix_firstCluster_trace_eq a

/-- Every widened stitched row has a path-shaped trace in the first cluster. -/
theorem stitchedRowPacking_traceOn_firstCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).TraceOn (P.cluster P.firstIndex) := by
  refine ⟨K.start_provenance.leftRight.path
    (K.startFirstClusterIndex (K.finalStitchedPrefix.startIndex a)), ?_⟩
  exact (K.stitchedRowPacking_firstCluster_trace_eq a).symm

/-- Widening the terminal interface preserves the exact even-cluster trace of
each completed row. -/
theorem stitchedRowPacking_local_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).vertexSet ∩
        P.cluster (evenClusterIndex g j) =
      ((K.localPerfect j).path
        (K.finalStitchedPrefix.localIndex j
          (K.evenClusterOrdinal_le_last j) a)).vertexSet := by
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix_local_trace_eq j a

/-- Every stitched row has a path-shaped trace in every even cluster. -/
theorem stitchedRowPacking_traceOn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).TraceOn
      (P.cluster (evenClusterIndex g j)) := by
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix_traceOn_evenCluster j a

/-- Widening the terminal interface preserves the exact provenance-selected
trace in every intervening odd cluster. -/
theorem stitchedRowPacking_between_trace_eq
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (hj : j.1 + 1 < g * (g - 1))
    (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).vertexSet ∩
        P.cluster (oddClusterAfterEvenIndex g j hj) =
      ((K.between_provenance j hj).middle.path
        ((K.between_provenance j hj).indexEquiv
          (K.finalStitchedPrefix.betweenIndex j
            (K.evenClusterOrdinal_lt_last_of_succ_lt j hj) a))).vertexSet := by
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix_between_trace_eq j hj a

/-- Every widened stitched row has a path-shaped trace in each intervening odd
cluster. -/
theorem stitchedRowPacking_traceOn_oddClusterAfterEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1)))
    (hj : j.1 + 1 < g * (g - 1))
    (a : K.stitchedRowPacking.Index) :
    (K.stitchedRowPacking.path a).TraceOn
      (P.cluster (oddClusterAfterEvenIndex g j hj)) := by
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix_traceOn_oddClusterAfterEven j hj a

/-- Every stitched row has a path-shaped trace in every cluster. -/
theorem stitchedRowPacking_traceOn_cluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.stitchedRowPacking.Index)
    (i : Fin (2 * g * (g - 1))) :
    (K.stitchedRowPacking.path a).TraceOn (P.cluster i) := by
  rcases clusterIndex_cases P.toPathOfSetsSystem i with
    hfirst | ⟨j, heven⟩ | ⟨j, hj, hodd⟩
  · subst i
    exact K.stitchedRowPacking_traceOn_firstCluster a
  · subst i
    exact K.stitchedRowPacking_traceOn_evenCluster j a
  · subst i
    exact K.stitchedRowPacking_traceOn_oddClusterAfterEven j hj a

/-- The completed widened rows visit clusters in their natural order. -/
theorem stitchedRowPacking_clusters_ordered
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (a : K.stitchedRowPacking.Index)
    {j k : Fin (2 * g * (g - 1))} (hjk : j.1 < k.1)
    {u v : V}
    (hu : u ∈ (K.stitchedRowPacking.path a).vertexSet)
    (hju : u ∈ P.cluster j)
    (hv : v ∈ (K.stitchedRowPacking.path a).vertexSet)
    (hkv : v ∈ P.cluster k) :
    (K.stitchedRowPacking.path a).Before u v := by
  have hkLast : k.1 ≤
      (evenClusterIndex g (lastEvenClusterOrdinal K.hN)).1 := by
    rw [evenClusterIndex_lastEven_eq_lastIndex P.toPathOfSetsSystem K.hN]
    simp [PathOfSetsSystem.lastIndex]
    omega
  simpa [stitchedRowPacking, PathPacking.widenTerminals] using
    K.finalStitchedPrefix.clusters_ordered a hjk hkLast hu hju hv hkv

/-- The completed prefix inherits all pairwise bridges from every local even
cluster output. -/
theorem finalStitchedPrefix_hasPairwiseBridgesIn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1))) :
    K.finalStitchedPrefix.packing.toPathPacking.HasPairwiseBridgesIn
      (P.cluster (evenClusterIndex g j)) := by
  exact K.finalStitchedPrefix.hasPairwiseBridgesIn_evenCluster j
    (K.evenClusterOrdinal_le_last j)

/-- The final stitched row packing retains the local pairwise bridges in every
even cluster. -/
theorem stitchedRowPacking_hasPairwiseBridgesIn_evenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (j : Fin (g * (g - 1))) :
    K.stitchedRowPacking.HasPairwiseBridgesIn
      (P.cluster (evenClusterIndex g j)) := by
  unfold stitchedRowPacking
  apply PathPacking.widenTerminals_hasPairwiseBridgesIn
  exact K.finalStitchedPrefix_hasPairwiseBridgesIn_evenCluster j

end StitchingPieces

/-- Formal local input corresponding to Chekuri--Chuzhoy Theorem 3.1.

For linked equal-size terminal sets `A` and `B` inside a connected cluster `C`,
the theorem either produces an `h x h` grid minor in the ambient graph or
returns `q` disjoint `A`-to-`B` paths inside `C` with pairwise bridges inside
`C`. -/
def LocalRoutingInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          NodeLinkedIn G C A B →
            A.card = w →
              B.card = w →
                (16 * h + 10) * q ≤ w →
                  ContainsGridMinor G h ∨
                  ∃ P : PathPacking G A B,
                    P.card = q ∧ P.StaysIn C ∧ P.HasPairwiseBridgesIn C

/-- Faithful local input corresponding to Chekuri--Chuzhoy Theorem 3.1.

This version includes the connected-cluster hypothesis available in every
path-of-sets application.  It matches the paper/contract statement more
closely than `LocalRoutingInput`, which is a convenient stronger interface. -/
def LocalRoutingClusterInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          IsCluster G C →
            NodeLinkedIn G C A B →
              A.card = w →
                B.card = w →
                  (16 * h + 10) * q ≤ w →
                    ContainsGridMinor G h ∨
                      ∃ P : PathPacking G A B,
                        P.card = q ∧ P.StaysIn C ∧
                          P.HasPairwiseBridgesIn C

/-- Applying the local Chekuri--Chuzhoy routing theorem in each even
one-based cluster either already gives a grid minor, or gives local outputs for
all even one-based clusters.

This is the first proved part of Corollary 3.2: the remaining work is to
concatenate these local outputs through the intervening odd clusters and prove
the trace/order fields of `StitchedRows`. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingInput
    (hlocal : LocalRoutingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g w : ℕ}
    (hg : 2 ≤ g)
    (hw : (16 * g + 10) * g ≤ w)
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  classical
  by_cases hgrid : ContainsGridMinor G g
  · exact Or.inl hgrid
  · refine Or.inr ⟨{ output := ?_ }⟩
    intro i
    let e := evenClusterIndex g i
    have hgt : 1 < g := lt_of_lt_of_le (by decide : 1 < 2) hg
    have hleft : (P.left e).card = w := P.left_card e
    have hright : (P.right e).card = w := P.right_card e
    have hpaths_exists :
        ∃ Q : PathPacking G (P.left e) (P.right e),
          Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
            Q.HasPairwiseBridgesIn (P.cluster e) := by
      rcases hlocal G hgt hgt (P.left_right_nodeLinked e)
          hleft hright hw with hgrid' | hpaths
      · exact False.elim (hgrid hgrid')
      · exact hpaths
    let Q : PathPacking G (P.left e) (P.right e) :=
      Classical.choose hpaths_exists
    have hQspec :
        Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
          Q.HasPairwiseBridgesIn (P.cluster e) :=
      Classical.choose_spec hpaths_exists
    exact {
      paths := Q
      paths_card := hQspec.1
      paths_staysIn := by simpa [e] using hQspec.2.1
      pairwise_bridges := by simpa [e] using hQspec.2.2
    }

/-- Cluster-faithful version of
`gridMinor_or_evenClusterOutputs_of_localRoutingInput`.

The connected-cluster hypothesis is supplied by the strong path-of-sets system
itself. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput
    (hlocal : LocalRoutingClusterInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g w : ℕ}
    (hg : 2 ≤ g)
    (hw : (16 * g + 10) * g ≤ w)
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  classical
  by_cases hgrid : ContainsGridMinor G g
  · exact Or.inl hgrid
  · refine Or.inr ⟨{ output := ?_ }⟩
    intro i
    let e := evenClusterIndex g i
    have hgt : 1 < g := lt_of_lt_of_le (by decide : 1 < 2) hg
    have hleft : (P.left e).card = w := P.left_card e
    have hright : (P.right e).card = w := P.right_card e
    have hpaths_exists :
        ∃ Q : PathPacking G (P.left e) (P.right e),
          Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
            Q.HasPairwiseBridgesIn (P.cluster e) := by
      rcases hlocal G hgt hgt (P.cluster_connected e)
          (P.left_right_nodeLinked e) hleft hright hw with hgrid' | hpaths
      · exact False.elim (hgrid hgrid')
      · exact hpaths
    let Q : PathPacking G (P.left e) (P.right e) :=
      Classical.choose hpaths_exists
    have hQspec :
        Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
          Q.HasPairwiseBridgesIn (P.cluster e) :=
      Classical.choose_spec hpaths_exists
    exact {
      paths := Q
      paths_card := hQspec.1
      paths_staysIn := by simpa [e] using hQspec.2.1
      pairwise_bridges := by simpa [e] using hQspec.2.2
    }

/-- Specialization of `gridMinor_or_evenClusterOutputs_of_localRoutingInput`
to the width used in Chekuri--Chuzhoy Corollary 3.3. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingInput_corollary33Width
    (hlocal : LocalRoutingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ}
    (hg : 2 ≤ g)
    (P : StrongPathOfSetsSystem G
      (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  refine gridMinor_or_evenClusterOutputs_of_localRoutingInput hlocal G hg ?_ P
  have hwidth : (16 * g + 10) * g = 16 * g ^ 2 + 10 * g := by
    ring
  exact le_of_eq hwidth

/-- Cluster-faithful specialization of the local routing step to the width
used in Chekuri--Chuzhoy Corollary 3.3. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput_corollary33Width
    (hlocal : LocalRoutingClusterInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ}
    (hg : 2 ≤ g)
    (P : StrongPathOfSetsSystem G
      (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  refine gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput
    hlocal G hg ?_ P
  have hwidth : (16 * g + 10) * g = 16 * g ^ 2 + 10 * g := by
    ring
  exact le_of_eq hwidth

/-- The stitched rows returned by Chekuri--Chuzhoy Corollary 3.2, specialized
to the parameters used in Corollary 3.3.

The row packing connects the first left nail set to the last right nail set.
For each even one-based cluster, every pair of distinct row paths has a bridge
inside that cluster, internally disjoint from all rows.  The later Appendix C.1
assembly turns this data into a path-valued sparse-grid branch certificate. -/
structure StitchedRows {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g w : ℕ)
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w) where
  /-- The row paths. -/
  rows : PathPacking G (P.left P.firstIndex) (P.right P.lastIndex)
  /-- The number of row paths. -/
  rows_card : rows.card = g
  /-- Each row meets each cluster in a path-shaped trace. -/
  row_trace_cluster :
    ∀ (a : rows.Index) (i : Fin (2 * g * (g - 1))),
      (rows.path a).TraceOn (P.cluster i)
  /-- The cluster traces occur along each row in the cluster order. -/
  row_clusters_ordered :
    ∀ (a : rows.Index) ⦃i j : Fin (2 * g * (g - 1))⦄,
      i.1 < j.1 →
        ∀ ⦃u v : V⦄,
          u ∈ (rows.path a).vertexSet → u ∈ P.cluster i →
            v ∈ (rows.path a).vertexSet → v ∈ P.cluster j →
              (rows.path a).Before u v
  /-- Each even one-based cluster supplies all pairwise row bridges. -/
  bridge_in_even_cluster :
    ∀ i : Fin (g * (g - 1)),
      rows.HasPairwiseBridgesIn (P.cluster (evenClusterIndex g i))

/-- The remaining stitching input after the local Chekuri--Chuzhoy routing
theorem has been applied in every even one-based cluster.

It says that compatible local outputs can be concatenated through the
intervening odd clusters into the global stitched rows of Corollary 3.2.  The
canonical `StitchingPieces` argument supplies the start and between-cluster
linkages; this input is only responsible for the remaining global
concatenation, trace, and order proof. -/
def StitchingInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ},
      2 ≤ g →
        (P : StrongPathOfSetsSystem G
          (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) →
          (E : EvenClusterOutputs P.toPathOfSetsSystem g) →
            StitchingPieces P E →
            Nonempty
            (StitchedRows G g (16 * g ^ 2 + 10 * g)
                P.toPathOfSetsSystem)

theorem stitchingInput_proved : StitchingInput := by
  intro V instFintype instDecidable G g hg P E K
  classical
  let rows := K.stitchedRowPacking
  refine ⟨{
    rows := rows
    rows_card := K.stitchedRowPacking_card
    row_trace_cluster := by
      intro a i
      exact K.stitchedRowPacking_traceOn_cluster a i
    row_clusters_ordered := by
      intro a i j hij u v hu hUi hv hVj
      exact K.stitchedRowPacking_clusters_ordered a hij hu hUi hv hVj
    bridge_in_even_cluster := by
      intro i
      exact K.stitchedRowPacking_hasPairwiseBridgesIn_evenCluster i
  }⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
