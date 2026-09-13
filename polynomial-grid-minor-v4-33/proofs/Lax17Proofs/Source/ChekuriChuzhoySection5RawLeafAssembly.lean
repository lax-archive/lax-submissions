import Lax17Proofs.Source.ChekuriChuzhoySection5RawBundle
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Concatenation

namespace Lax17Proofs

universe u v w

/-!
# Source-faithful many-leaves Phase 1 assembly

This module restores the integral leaf packing produced from unsampled
terminal-skeleton bundles, thins its host endpoints, and performs the existing
root extraction and all-pairs concatenation.  It removes the extra factor
`n` that arose when the many-leaves branch was routed through a global group
transversal.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RawLeafAssembly


open ChekuriChuzhoySection5Phase1Concatenation
open ChekuriChuzhoySection5Phase1Restoration
open ChekuriChuzhoySection5RawBundle
open ChekuriChuzhoySection5RouterSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n m Delta q : Nat} {router : Fin n → Finset V}

/-- Restore and endpoint-thin the raw Claims 5.14/5.15 packing. -/
theorem exists_restoredLeafPackingFamily_of_rawSupportTree
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    {k width cap routerDen eta replicas : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : ∀ i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n) (hrootLeaf : ∀ i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (router i) (router j))
    (hband : ∀ i : Fin n,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta : ∀ i,
      k + (T.dist rootRouter (leafRouter i) - 1) * (routerDen + k) ≤ eta)
    {c : Rat} (hc : 0 ≤ c) (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas) :
    Nonempty
      (RestoredLeafPackingFamily G
        (fun i => router (leafRouter i))
        (ChekuriChuzhoySection5Clustering.interfaceVertices
          G (router rootRouter)) q) := by
  rcases claim514_claim515_of_rawSupportTree_leafFamily_interfaceRoot
      S T hT hload hdegree hDelta hk hgroups hbundle leafRouter hleaf
      rootRouter hrootLeaf hrouterDisjoint hband hcap heta hc
      hreplicasPos hreplicaValue hcapacity with
    ⟨P, _hPcard, hsourceSet, _holdRegion⟩
  have hselectedDisjoint : ∀ ⦃i j : Fin m⦄, i ≠ j →
      Disjoint (router (leafRouter i)) (router (leafRouter j)) := by
    intro i j hij
    exact hrouterDisjoint (fun h => hij (hleafInjective h))
  exact exists_restoredLeafPackingFamily_of_fullSourcePacking
    P hsourceSet hdegree hDelta hthin hselectedDisjoint

/-- Complete Case-2 routing package from raw support-tree bundles. -/
theorem exists_leafPairRoutingPackage_of_rawSupportTree
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    {k width cap routerDen eta replicas groupSize groupedWidth
      carrierWidth outWidth : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : ∀ i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n) (hrootLeaf : ∀ i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (router i) (router j))
    (hrouterCluster : ∀ i, IsCluster G (router i))
    (hband : ∀ i : Fin n,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta : ∀ i,
      k + (T.dist rootRouter (leafRouter i) - 1) * (routerDen + k) ≤ eta)
    {c : Rat} (hc : 0 ≤ c) (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize) (hgroupSizeWidth : groupSize ≤ q)
    (hscale : routerDen ≤ groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth : carrierWidth ≤
      (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty
      (LeafPairRoutingPackage G (fun i => router (leafRouter i))
        (router rootRouter) q outWidth) := by
  rcases exists_restoredLeafPackingFamily_of_rawSupportTree
      S T hT hload hdegree (by omega) hk hgroups hbundle leafRouter
      hleafInjective hleaf rootRouter hrootLeaf hrouterDisjoint hband hcap
      heta hc hreplicasPos hreplicaValue hcapacity hthin with ⟨R⟩
  exact exists_leafPairRoutingPackage_of_restored R
    (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
      G (router rootRouter))
    (fun i => hrouterDisjoint (hrootLeaf i))
    (hrouterCluster rootRouter) hdegree hDelta (hband rootRouter)
    hunionCap hgroupSize hgroupSizeWidth (by simpa using hscale)
    hgroupedWidth hcarrierWidth houtCarrier hlink

end ChekuriChuzhoySection5RawLeafAssembly
end SimpleGraph

end Lax17Proofs
