import Lax17Proofs.Source.ChekuriChuzhoySection5AuxiliaryTree
import Lax17Proofs.Source.ChekuriChuzhoySection5Superterminals
import Lax17Proofs.Source.ChekuriChuzhoySection5TreeAssembly

namespace Lax17Proofs

universe u v w

/-!
# Phase 2 tree-of-sets assembly

This module composes journal Theorem 5.10, Observation 5.18, Claim 5.19, and
the final group-transversal selection.  Exact pairwise direct boundary
packings produce a regular terminal skeleton; the Singh--Lau tree selects
heavy endpoint pairs; and the deterministic transversal retains width `w`
simultaneously on all auxiliary-tree edges.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase2Assembly


open ChekuriChuzhoySection5AuxiliaryTree
open ChekuriChuzhoySection5ClusterSkeleton
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5Superterminals
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem graph_edgeBundle_eq_skeleton_edgeBundleKey
    {m : Nat} {cluster : Fin m → Finset V}
    (S : ClusterPathSkeleton G cluster) (p : Sym2 (Fin m)) :
    S.graph.edgeBundle p = S.edgeBundleKey p := by
  classical
  ext e
  simp [FiniteEdgeIndexedGraph.edgeKey, ClusterPathSkeleton.edgeKey]

/-- Complete deterministic Phase 2 assembly, retaining the fact that the
output uses the supplied clusters.  The inequality `m^4 * w <= 2 * mu` is the
exact combined loss from the heavy-support threshold (`m^3`) and the
one-per-group transversal (`m`). -/
theorem
    exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings_with_same_clusters
    (G : _root_.SimpleGraph V)
    {m mu w cap alphaNum alphaDen : Nat}
    (cluster B : Fin m → Finset V)
    (hm : 2 ≤ m) (hmu : 1 ≤ mu) (hw : 0 < w)
    (hwidth : m ^ 4 * w ≤ 2 * mu)
    (hBcard : ∀ i : Fin m, (B i).card = mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆ interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j →
        ∃ P : PathPacking G (B i) (B j), P.card = mu)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    ∃ T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen,
      ∀ i : Fin m, T.cluster i = cluster i := by
  obtain ⟨S, hSconnected, hSgroups, hSdegree⟩ :=
    exists_regularClusterPathSkeleton_of_pairwise_direct_packings
      G cluster B mu hm hmu hBcard hinterface hdirect hpacking
  obtain ⟨T, _hTheavySupport, hTtree, hTdegree, hTheavy⟩ :=
    claim517_exists_boundedDegreeAuxiliarySpanningTree
      S.graph hm (by omega : 0 < 2 * mu) hSdegree hSconnected
  have hbundle :
      ∀ p ∈ T.edgeSet, m * w ≤ (S.edgeBundleKey p).card := by
    intro p hp
    induction p using Sym2.inductionOn with
    | _ i j =>
        have hij : T.Adj i j := by
          simpa [_root_.SimpleGraph.mem_edgeSet] using hp
        have hheavy :
            heavyThreshold m (2 * mu) ≤
              S.graph.bundleCapacity s(i, j) :=
          hTheavy i j hij
        have hcard :
            m * w ≤ (S.graph.edgeBundle s(i, j)).card :=
          mul_width_le_bundleCard_of_heavy
            S.graph s(i, j) (by omega) hwidth hheavy
        simpa [graph_edgeBundle_eq_skeleton_edgeBundleKey S s(i, j)]
          using hcard
  exact
    S.exists_bandwidthTreeOfSetsSystem_with_same_clusters T
      (by omega) hw hTtree hTdegree hSgroups hbundle
      hclusterConnected hclusterDisjoint hband hcap

/-- Compatibility wrapper for Phase 2 when the cluster identity is not
needed by the caller. -/
theorem exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings
    (G : _root_.SimpleGraph V)
    {m mu w cap alphaNum alphaDen : Nat}
    (cluster B : Fin m → Finset V)
    (hm : 2 ≤ m) (hmu : 1 ≤ mu) (hw : 0 < w)
    (hwidth : m ^ 4 * w ≤ 2 * mu)
    (hBcard : ∀ i : Fin m, (B i).card = mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆ interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j →
        ∃ P : PathPacking G (B i) (B j), P.card = mu)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap) :
    Nonempty
      (BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) := by
  obtain ⟨T, _hclusters⟩ :=
    exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings_with_same_clusters
      G cluster B hm hmu hw hwidth hBcard hinterface hdirect hpacking
      hclusterConnected hclusterDisjoint hband hcap
  exact ⟨T⟩

end ChekuriChuzhoySection5Phase2Assembly
end SimpleGraph

end Lax17Proofs
