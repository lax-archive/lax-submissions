import Lax17Proofs.Source.Exponent7.GlobalRowThreading
import Lax17Proofs.Source.Exponent7.CleanMatchingDichotomy

namespace Lax17Proofs

/-!
# Alternating matchings on globally threaded rows

The clean matching dichotomy is applied in the `2g` consecutive clusters used
by the short-wide construction. `GlobalRowThreading` supplies the global rows
and their local traces. The result assumes
`CleanMatchingDichotomyStatement reserve`.
-/

namespace SimpleGraph
namespace Exponent7

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {g w reserve : ℕ}

/-- The zero-based cluster carrying the matching
`(0,1),(2,3),...` for column `c`. -/
def oddMatchingCluster (c : Fin g) : Fin (2 * g) :=
  ⟨2 * c.1, by omega⟩

/-- The zero-based cluster carrying the matching
`(1,2),(3,4),...` for column `c`. -/
def evenMatchingCluster (c : Fin g) : Fin (2 * g) :=
  ⟨2 * c.1 + 1, by omega⟩

@[simp] theorem oddMatchingCluster_val (c : Fin g) :
    (oddMatchingCluster c).1 = 2 * c.1 := rfl

@[simp] theorem evenMatchingCluster_val (c : Fin g) :
    (evenMatchingCluster c).1 = 2 * c.1 + 1 := rfl

theorem oddMatchingCluster_lt_even (c : Fin g) :
    (oddMatchingCluster c).1 < (evenMatchingCluster c).1 := by
  simp

theorem evenMatchingCluster_lt_oddMatchingCluster
    {c d : Fin g} (hcd : c.1 < d.1) :
    (evenMatchingCluster c).1 < (oddMatchingCluster d).1 := by
  simp
  omega

/-- A named selection of `g` rows from the canonical full-width threaded
packing. -/
structure SelectedGlobalRows
    (g : ℕ) (P : StrongPathOfSetsSystem G (2 * g) w) where
  threading : GlobalRowPrefix P P.lastIndex
  row : Fin g ↪ threading.packing.Index

namespace SelectedGlobalRows

variable {P : StrongPathOfSetsSystem G (2 * g) w}

/-- The local path corresponding to a selected global row in cluster `i`. -/
noncomputable def localRow
    (T : SelectedGlobalRows g P) (i : Fin (2 * g)) :
    Fin g ↪ (StrongPathOfSetsSystem.clusterLinkage P i).Index where
  toFun r := T.threading.localIndex i (GlobalRowPrefix.index_le_last P i) (T.row r)
  inj' :=
    (T.threading.localIndex_injective i
      (GlobalRowPrefix.index_le_last P i)).comp
      T.row.injective

theorem local_path_subset_global
    (T : SelectedGlobalRows g P) (i : Fin (2 * g)) (r : Fin g) :
    ((StrongPathOfSetsSystem.clusterLinkage P i).path
      (T.localRow i r)).vertexSet ⊆
      (T.threading.packing.path (T.row r)).vertexSet :=
  T.threading.local_path_subset i (GlobalRowPrefix.index_le_last P i) (T.row r)

theorem global_trace_subset_local
    (T : SelectedGlobalRows g P) (i : Fin (2 * g)) (r : Fin g) :
    (T.threading.packing.path (T.row r)).vertexSet ∩ P.cluster i ⊆
      ((StrongPathOfSetsSystem.clusterLinkage P i).path
        (T.localRow i r)).vertexSet :=
  T.threading.local_trace_subset i (GlobalRowPrefix.index_le_last P i) (T.row r)

theorem global_clusters_ordered
    (T : SelectedGlobalRows g P) (r : Fin g)
    {i j : Fin (2 * g)} (hij : i.1 < j.1)
    {u v : V}
    (hu : u ∈ (T.threading.packing.path (T.row r)).vertexSet)
    (hui : u ∈ P.cluster i)
    (hv : v ∈ (T.threading.packing.path (T.row r)).vertexSet)
    (hvj : v ∈ P.cluster j) :
    (T.threading.packing.path (T.row r)).Before u v :=
  T.threading.clusters_ordered (T.row r) hij
    (GlobalRowPrefix.index_le_last P j)
    hu hui hv hvj

/-- Canonical selection of the first `g` global rows. -/
noncomputable def canonical
    (P : StrongPathOfSetsSystem G (2 * g) w) (hgw : g ≤ w) :
    SelectedGlobalRows g P where
  threading := GlobalRowPrefix.globalRows P
  row := (GlobalRowPrefix.globalRows P).selectedGlobalIndex g hgw

end SelectedGlobalRows

/-- Simultaneous realizations of the two alternating matchings in every
two-cluster column block. -/
structure AlternatingClusterRealizations
    (g : ℕ) (P : StrongPathOfSetsSystem G (2 * g) w) where
  threads : SelectedGlobalRows g P
  odd :
    ∀ c : Fin g,
      CleanMatchingRealization
        (StrongPathOfSetsSystem.clusterLinkage P
          (oddMatchingCluster c)).toPathPacking
        (threads.localRow (oddMatchingCluster c))
        (oddRowMatching g)
        (P.cluster (oddMatchingCluster c))
  even :
    ∀ c : Fin g,
      CleanMatchingRealization
        (StrongPathOfSetsSystem.clusterLinkage P
          (evenMatchingCluster c)).toPathPacking
        (threads.localRow (evenMatchingCluster c))
        (evenRowMatching g)
        (P.cluster (evenMatchingCluster c))

namespace AlternatingClusterRealizations

variable {P : StrongPathOfSetsSystem G (2 * g) w}

/-- A bridge internal to one local cluster is internally disjoint from every
selected *global* row, because the global trace in that cluster is exactly the
recorded local linkage path. -/
theorem odd_internallyDisjoint_globalRow
    (B : AlternatingClusterRealizations g P)
    (c : Fin g) (e : (oddRowMatching g).EdgeIndex) (r : Fin g) :
    (B.odd c).path e |>.InternallyDisjointFromSet
      ((B.threads.threading.packing.path (B.threads.row r)).vertexSet) := by
  intro v hvBridge hvGlobal
  have hvCluster : v ∈ P.cluster (oddMatchingCluster c) :=
    (B.odd c).staysIn e hvBridge
  have hvLocal :=
    B.threads.global_trace_subset_local (oddMatchingCluster c) r
      (Finset.mem_inter.mpr ⟨hvGlobal, hvCluster⟩)
  apply (B.odd c).internallyDisjoint_selectedRows e hvBridge
  apply (mem_selectedRowVertexSet
    (StrongPathOfSetsSystem.clusterLinkage P
      (oddMatchingCluster c)).toPathPacking
    ((Finset.univ : Finset (Fin g)).image
      (B.threads.localRow (oddMatchingCluster c)))).2
  exact ⟨B.threads.localRow (oddMatchingCluster c) r,
    Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, hvLocal⟩

theorem even_internallyDisjoint_globalRow
    (B : AlternatingClusterRealizations g P)
    (c : Fin g) (e : (evenRowMatching g).EdgeIndex) (r : Fin g) :
    (B.even c).path e |>.InternallyDisjointFromSet
      ((B.threads.threading.packing.path (B.threads.row r)).vertexSet) := by
  intro v hvBridge hvGlobal
  have hvCluster : v ∈ P.cluster (evenMatchingCluster c) :=
    (B.even c).staysIn e hvBridge
  have hvLocal :=
    B.threads.global_trace_subset_local (evenMatchingCluster c) r
      (Finset.mem_inter.mpr ⟨hvGlobal, hvCluster⟩)
  apply (B.even c).internallyDisjoint_selectedRows e hvBridge
  apply (mem_selectedRowVertexSet
    (StrongPathOfSetsSystem.clusterLinkage P
      (evenMatchingCluster c)).toPathPacking
    ((Finset.univ : Finset (Fin g)).image
      (B.threads.localRow (evenMatchingCluster c)))).2
  exact ⟨B.threads.localRow (evenMatchingCluster c) r,
    Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, hvLocal⟩

end AlternatingClusterRealizations

/-- Apply the prescribed matching dichotomy in all `2g` cluster slots. -/
theorem grid_or_alternatingClusterRealizations
    (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (P : StrongPathOfSetsSystem G (2 * g) w)
    (hg : 2 ≤ g)
    (hgw : g ≤ w)
    (hwidth : reserve * g ^ 2 ≤ w) :
    ContainsGridMinor G g ∨
      Nonempty (AlternatingClusterRealizations g P) := by
  classical
  by_cases hgrid : ContainsGridMinor G g
  · exact Or.inl hgrid
  · let T : SelectedGlobalRows g P := SelectedGlobalRows.canonical P hgw
    have hOdd :
        ∀ c : Fin g,
          Nonempty
            (CleanMatchingRealization
              (StrongPathOfSetsSystem.clusterLinkage P
                (oddMatchingCluster c)).toPathPacking
              (T.localRow (oddMatchingCluster c))
              (oddRowMatching g)
              (P.cluster (oddMatchingCluster c))) := by
      intro c
      let R :=
        (StrongPathOfSetsSystem.clusterLinkage P
          (oddMatchingCluster c)).toPathPacking
      have hRcard : R.card = w := by simp [R]
      have hsource : R.sourceSet = P.left (oddMatchingCluster c) := by
        apply R.sourceSet_eq_left_of_card_eq
        rw [hRcard, P.left_card]
      rcases cleanOddMatching_or_grid hD G g R
          (P.cluster (oddMatchingCluster c))
          (T.localRow (oddMatchingCluster c)) hg
          (by simpa [hRcard] using hwidth)
          (by
            simpa [R] using
              StrongPathOfSetsSystem.clusterLinkage_staysIn P
                (oddMatchingCluster c))
          (by
            rw [hsource]
            exact P.left_nodeWellLinked (oddMatchingCluster c)) with
        hgrid' | hreal
      · exact False.elim (hgrid hgrid')
      · exact hreal
    have hEven :
        ∀ c : Fin g,
          Nonempty
            (CleanMatchingRealization
              (StrongPathOfSetsSystem.clusterLinkage P
                (evenMatchingCluster c)).toPathPacking
              (T.localRow (evenMatchingCluster c))
              (evenRowMatching g)
              (P.cluster (evenMatchingCluster c))) := by
      intro c
      let R :=
        (StrongPathOfSetsSystem.clusterLinkage P
          (evenMatchingCluster c)).toPathPacking
      have hRcard : R.card = w := by simp [R]
      have hsource : R.sourceSet = P.left (evenMatchingCluster c) := by
        apply R.sourceSet_eq_left_of_card_eq
        rw [hRcard, P.left_card]
      rcases cleanEvenMatching_or_grid hD G g R
          (P.cluster (evenMatchingCluster c))
          (T.localRow (evenMatchingCluster c)) hg
          (by simpa [hRcard] using hwidth)
          (by
            simpa [R] using
              StrongPathOfSetsSystem.clusterLinkage_staysIn P
                (evenMatchingCluster c))
          (by
            rw [hsource]
            exact P.left_nodeWellLinked (evenMatchingCluster c)) with
        hgrid' | hreal
      · exact False.elim (hgrid hgrid')
      · exact hreal
    exact Or.inr ⟨{
      threads := T
      odd := fun c => Classical.choice (hOdd c)
      even := fun c => Classical.choice (hEven c)
    }⟩

end Exponent7
end SimpleGraph

end Lax17Proofs
