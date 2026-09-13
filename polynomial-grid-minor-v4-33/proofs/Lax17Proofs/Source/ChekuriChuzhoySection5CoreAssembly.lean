import Lax17Proofs.Source.ChekuriChuzhoySection5GoodRouterProducer
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Concatenation
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase2Pruning
import Lax17Proofs.Source.ChekuriChuzhoySection5LongPathAssembly
import Lax17Proofs.Source.ChekuriChuzhoySection5RawLeafAssembly
import Lax17Proofs.Source.TreeOfSetsCoarseStrongification
import Lax17Proofs.Source.ChekuriChuzhoyPendantTransport

namespace Lax17Proofs

universe u v w

/-!
# Source-facing Section 5 core assembly

This module composes good-router production, the terminal skeleton, both
branches of Phase 1, Phase 2 pruning, source-sharp strongification, and
projection out of the pendant host.  Its hypotheses are only the explicit
integer and rational inequalities that remain to be discharged by the final
`m^23` arithmetic wrapper.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5CoreAssembly


open ChekuriChuzhoyPendantVertex
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5GoodRouterProducer
open ChekuriChuzhoySection5LongPathAssembly
open ChekuriChuzhoySection5Phase1Concatenation
open ChekuriChuzhoySection5Phase1Support
open ChekuriChuzhoySection5Phase2Pruning
open ChekuriChuzhoySection5RawLeafAssembly
open ChekuriChuzhoySection5RouterSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Full Section 5 assembly after all numerical parameters have been fixed.
The host maximum-degree parameter is conservatively enlarged from `Delta` to
`Delta + 3`, so every downstream theorem can use the uniform lower bound
three without a separate low-degree case. -/
theorem exists_strongTreeOfSetsSystem_of_parameters
    (G : _root_.SimpleGraph V) (X : Finset V)
    {m W n cap longWidth leafWidth mu eta replicas q groupSize groupedWidth
      carrierWidth outWidth ordinaryWidth Delta : Nat}
    {c : Rat}
    (hm : 2 ≤ m) (hW : 0 < W) (hn : 0 < n)
    (hrouterCount : m ^ 2 ≤ n)
    (hdegree : MaxDegreeAtMost G Delta)
    (hXcard : 2 ≤ X.card)
    (hXwell : NodeWellLinkedIn G Finset.univ X)
    (hdegreeCap :
      Delta + 1 <
        ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n)
    (hcapPos : 1 < cap)
    (hthresholdCap :
      ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
        X.card n ≤ cap)
    (hmuPos : 0 < mu)
    (hmuRoute :
      mu ≤
        (ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n / 2) / (8 * (Delta + 3)))
    (hsupportWidth :
      n ^ 2 * (4 * (Delta + 3) * leafWidth) ≤ 2 * mu)
    (hlongBundle :
      n * (8 * (Delta + 3) ^ 2 * longWidth) ≤
        4 * (Delta + 3) * leafWidth)
    (hlongWidthPos : 0 < longWidth)
    (hleafWidthPos : 0 < leafWidth)
    (hleafCap :
      2 * leafWidth ≤
        ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n / 2)
    (heta :
      n + (m - 1) *
          (16 * (20 * n) * (Nat.log 2 cap + 1) + n) ≤ eta)
    (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * leafWidth)
    (hcapacity :
      (m : Rat) * c *
          (1 + ((Delta + 3 : Nat) : Rat) * eta / 2) ≤ 1)
    (hthin : (Delta + 3) * q ≤ replicas)
    (hunionCap :
      m * q ≤
        ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n / 2)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale :
      16 * (20 * n) * (Nat.log 2 cap + 1) ≤ groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * (Delta + 3) * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * (Delta + 3) * outWidth ≤ carrierWidth)
    (hlongRetain :
      16 * (Delta + 3) * (m - 1) * ordinaryWidth +
          8 * (Delta + 3) ^ 2 * ordinaryWidth ≤
        8 * (Delta + 3) ^ 2 * longWidth)
    (hordinaryPos : 0 < ordinaryWidth)
    (hphase2Width : m ^ 4 * ordinaryWidth ≤ 2 * outWidth)
    (hordinaryCap :
      3 * ordinaryWidth ≤
        ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n / 2)
    (hcoarse :
      BandwidthTreeOfSetsSystem.coarseStrongificationWidth
        (16 * (20 * n) * (Nat.log 2 cap + 1))
        (Delta + 3) W ≤ ordinaryWidth) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  classical
  rcases exists_goodRouterFamily_of_pendantHost Delta cap n hdegree
      hdegreeCap hn hcapPos hthresholdCap hXcard hXwell with ⟨M, ⟨R⟩⟩
  have hMdegreeSmall : MaxDegreeAtMost M.H (Delta + 1) :=
    maxDegreeAtMost_of_le (maxDegreeAtMost_succ hdegree) M.le_original
  have hMdegree : MaxDegreeAtMost M.H (Delta + 3) :=
    maxDegreeAtMost_mono hMdegreeSmall (by omega)
  have hDeltaHost : 3 ≤ Delta + 3 := by omega
  rcases exists_routerPathSkeleton_of_goodRouterFamily R M.nodeWellLinked
      hMdegree (by omega) hmuRoute with
    ⟨S, hSconnected, hSgroups, hSload⟩
  have hrouterConnected : ∀ i, IsCluster M.H (R.router i) :=
    fun i => (R.good i).connected
  have hrouterDisjoint : ∀ {i j : Fin n}, i ≠ j →
      Disjoint (R.router i) (R.router j) :=
    fun {_ _} hij => R.pairwise_disjoint hij
  have hrouterBand : ∀ i,
      TruncatedScaledBandwidth M.H (R.router i)
        (ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph.claim59SourceDegreeCap
          X.card n / 2) 1
        (16 * (20 * n) * (Nat.log 2 cap + 1)) :=
    fun i => (R.good i).bandwidth
  rcases exists_phase1Support_spanningTree_with_bundle_lower_bound
      S.graph hn (by omega : 0 < 2 * mu) hSconnected hsupportWidth with
    ⟨T, hTsupport, hTtree, hTbundle⟩
  have hrawBundle : ∀ i j, T.Adj i j →
      4 * (Delta + 3) * leafWidth ≤ (S.edgeBundle i j).card := by
    intro i j hij
    simpa [S.edgeBundle_eq_edgeBundleKey i j] using hTbundle i j hij
  rcases exists_bufferedSupportPath_or_leafSelection
      T hTtree hm hrouterCount with hpath | hleaf
  · rcases hpath with ⟨order, horderInjective, horderAdj⟩
    have hbundle : ∀ p ∈ T.edgeSet,
        n * (8 * (Delta + 3) ^ 2 * longWidth) ≤
          (S.edgeBundleKey p).card := by
      intro p hp
      induction p using Sym2.inductionOn with
      | _ i j =>
          have hij : T.Adj i j := by
            simpa [_root_.SimpleGraph.mem_edgeSet] using hp
          exact hlongBundle.trans <| by
            simpa [S.edgeBundle_eq_edgeBundleKey i j] using hTbundle i j hij
    rcases S.exists_supportBundleTransversal T hn hSgroups hbundle with ⟨B⟩
    rcases exists_bufferedPathAssemblyData S T order hm hordinaryPos hTtree
        horderInjective horderAdj hSload hMdegree (by omega) B
        hlongRetain hrouterConnected (fun i j h => hrouterDisjoint h)
        hrouterBand hordinaryCap with ⟨D⟩
    let TB := D.toBandwidthTreeOfSetsSystem
    rcases TB.exists_strongTreeOfSetsSystem_of_coarse_width_with_same_clusters
        hMdegree hDeltaHost (by positivity) hW hcoarse with
      ⟨U, hUcluster⟩
    let U' := U.mapLe M.le_original
    refine ⟨ChekuriChuzhoyPendantVertex.StrongTreeOfSetsSystem.projectOldOfDisjointLeaves
      U' ?_⟩
    intro i
    change Disjoint (U.cluster i) (leaves (V := V) (X := X))
    rw [hUcluster i]
    exact (R.good (bufferedRouter order i)).terminal_disjoint
  · rcases hleaf with ⟨L⟩
    rcases exists_leafPairRoutingPackage_of_rawSupportTree
        S T hTtree hSload hMdegree hDeltaHost
        (by
          have : 4 ≤ n := by nlinarith [hrouterCount]
          omega)
        hSgroups hrawBundle L.leafRouter L.leafRouter_injective
        L.leafRouter_degree_one L.rootRouter L.rootRouter_ne_leaf
        (fun {_ _} h => hrouterDisjoint h) hrouterConnected hrouterBand
        hleafCap (fun i => by
          have hstep : T.dist L.rootRouter (L.leafRouter i) - 1 ≤ m - 1 :=
            Nat.sub_le_sub_right (L.rootRouter_dist_le i) 1
          exact (Nat.add_le_add_left
            (Nat.mul_le_mul_right
              (16 * (20 * n) * (Nat.log 2 cap + 1) + n) hstep) n).trans heta)
        hc hreplicasPos hreplicaValue hcapacity hthin hunionCap
        hgroupSize hgroupSizeWidth hscale hgroupedWidth hcarrierWidth
        houtCarrier hlink with ⟨P⟩
    have houtWidthPos : 0 < outWidth := by
      have hleftPos : 0 < m ^ 4 * ordinaryWidth :=
        Nat.mul_pos (Nat.pow_pos (by omega)) hordinaryPos
      have hrightPos : 0 < 2 * outWidth :=
        lt_of_lt_of_le hleftPos hphase2Width
      omega
    rcases exists_bandwidthTreeOfSetsSystem_of_rootCleanLeafPackingFamily
        P.cleaned P.extraction hm houtWidthPos hordinaryPos hphase2Width
        (fun i => hrouterConnected (L.leafRouter i))
        (fun {_ _} hij =>
          hrouterDisjoint (fun h => hij (L.leafRouter_injective h)))
        (fun i => hrouterBand (L.leafRouter i)) hordinaryCap with
      ⟨TB, hTBcluster⟩
    rcases TB.exists_strongTreeOfSetsSystem_of_coarse_width_with_same_clusters
        hMdegree hDeltaHost (by positivity) hW hcoarse with
      ⟨U, hUcluster⟩
    let U' := U.mapLe M.le_original
    refine ⟨ChekuriChuzhoyPendantVertex.StrongTreeOfSetsSystem.projectOldOfDisjointLeaves
      U' ?_⟩
    intro i
    change Disjoint (U.cluster i) (leaves (V := V) (X := X))
    rw [hUcluster i, hTBcluster i]
    exact (R.good (L.leafRouter i)).terminal_disjoint

end ChekuriChuzhoySection5CoreAssembly
end SimpleGraph

end Lax17Proofs
