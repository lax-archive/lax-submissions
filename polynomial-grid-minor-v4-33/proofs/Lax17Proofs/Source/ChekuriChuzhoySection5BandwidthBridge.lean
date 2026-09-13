import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Section 5 truncated-bandwidth bridge

The routers in Chekuri--Chuzhoy Section 5 satisfy bandwidth only up to the
truncation cap.  The tree-of-sets construction uses at most that many boundary
vertices at a router.  This file records the exact implication from the
truncated router predicate to the scaled cut-well-linkedness certificate
stored by `BandwidthTreeOfSetsSystem`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Clustering


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace TruncatedScaledBandwidth

/-- Any subset of the interface whose total cardinality is at most the
truncation cap is scaled edge-well-linked in the cluster. -/
theorem scaledEdgeWellLinkedIn_of_subset_interface
    {C T : Finset V} {cap alphaNum alphaDen : Nat}
    (hband : TruncatedScaledBandwidth G C cap alphaNum alphaDen)
    (hTinterface : T ⊆ interfaceVertices G C)
    (hTcard : T.card ≤ cap) :
    Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen := by
  classical
  refine ⟨hband.1, hband.2.1,
    hTinterface.trans (interfaceVertices_subset G C), ?_⟩
  intro X Y hXC hYC hcover hdisjoint
  have hleft :
      (X ∩ T).card ≤ (X ∩ interfaceVertices G C).card := by
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hv).1, hTinterface (Finset.mem_inter.mp hv).2⟩
  have hright :
      (Y ∩ T).card ≤ (Y ∩ interfaceVertices G C).card := by
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hv).1, hTinterface (Finset.mem_inter.mp hv).2⟩
  have hminInterface :
      min (X ∩ T).card (Y ∩ T).card ≤
        min (X ∩ interfaceVertices G C).card
          (Y ∩ interfaceVertices G C).card :=
    min_le_min hleft hright
  have hleftT : (X ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hminCap : min (X ∩ T).card (Y ∩ T).card ≤ cap :=
    (Nat.min_le_left _ _).trans (hleftT.trans hTcard)
  have hdemand :
      min (X ∩ T).card (Y ∩ T).card ≤
        truncatedInterfaceDemand G C X Y cap := by
    exact le_min hminInterface hminCap
  exact (Nat.mul_le_mul_left alphaNum hdemand).trans
    (hband.2.2 X Y hXC hYC hcover hdisjoint)

end TruncatedScaledBandwidth
end ChekuriChuzhoySection5Clustering
end SimpleGraph

end Lax17Proofs
