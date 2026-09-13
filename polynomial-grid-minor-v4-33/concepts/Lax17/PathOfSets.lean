import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lax17.Linkedness

/-!
---
title: Strong and hairy path-of-sets systems
type: definition
---
A path-of-sets system is an ordered sequence of pairwise disjoint connected
clusters.  Each cluster has equally large, disjoint left and right interfaces,
and consecutive interfaces are joined by disjoint path families that otherwise
avoid every cluster.  It is strong when the two interfaces are well-linked and
mutually linked inside each cluster.

A hairy path-of-sets system adds one disjoint connected hair cluster at every
position and a disjoint linkage from the base cluster to that hair.  Its
hair-side endpoints are well-linked in the hair cluster.
-/

namespace Lax17.PathOfSets

universe u

open Lax17.Linkedness
open Lax17.Paths

/-- A finite vertex set inducing a connected graph. -/
def IsCluster {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C : Finset V) : Prop :=
  (G.induce {v : V | v ∈ C}).Connected

/-- A path-of-sets system of length `ℓ` and width `w`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (ℓ w : ℕ) where
  length_pos : 0 < ℓ
  width_pos : 0 < w
  cluster : Fin ℓ → Finset V
  cluster_connected : ∀ i : Fin ℓ, IsCluster G (cluster i)
  cluster_disjoint :
    ∀ ⦃i j : Fin ℓ⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  left : Fin ℓ → Finset V
  right : Fin ℓ → Finset V
  left_subset : ∀ i : Fin ℓ, left i ⊆ cluster i
  right_subset : ∀ i : Fin ℓ, right i ⊆ cluster i
  interfaces_disjoint : ∀ i : Fin ℓ, Disjoint (left i) (right i)
  left_card : ∀ i : Fin ℓ, (left i).card = w
  right_card : ∀ i : Fin ℓ, (right i).card = w
  connector :
    (i : Fin ℓ) → (hi : i.1 + 1 < ℓ) →
      VertexLinkage G (right i) (left ⟨i.1 + 1, hi⟩) w
  connector_avoids_clusters :
    ∀ (i : Fin ℓ) (hi : i.1 + 1 < ℓ) (j : Fin ℓ)
      (a : Fin w),
        (connector i hi).path a |>.InternallyAvoids (cluster j)
  connectors_disjoint :
    ∀ ⦃i j : Fin ℓ⦄ (hi : i.1 + 1 < ℓ) (hj : j.1 + 1 < ℓ),
      i ≠ j → ∀ a b : Fin w,
        Disjoint ((connector i hi).path a).vertices
          ((connector j hj).path b).vertices

namespace System

/-- The first cluster index. -/
def firstIndex {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {ℓ w : ℕ}
    (P : System G ℓ w) : Fin ℓ :=
  ⟨0, P.length_pos⟩

/-- The last cluster index. -/
def lastIndex {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {ℓ w : ℕ}
    (P : System G ℓ w) : Fin ℓ :=
  ⟨ℓ - 1, Nat.sub_lt P.length_pos Nat.zero_lt_one⟩

end System

/-- A strong path-of-sets system. -/
structure StrongSystem {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (ℓ w : ℕ) extends System G ℓ w where
  left_well_linked :
    ∀ i : Fin ℓ, NodeWellLinkedIn G (cluster i) (left i)
  right_well_linked :
    ∀ i : Fin ℓ, NodeWellLinkedIn G (cluster i) (right i)
  interfaces_linked :
    ∀ i : Fin ℓ, NodeLinkedIn G (cluster i) (left i) (right i)

/-- A hairy path-of-sets system. -/
structure HairySystem {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (ℓ w : ℕ) where
  base : StrongSystem G ℓ w
  hairCluster : Fin ℓ → Finset V
  hair_connected : ∀ i : Fin ℓ, IsCluster G (hairCluster i)
  hair_disjoint :
    ∀ ⦃i j : Fin ℓ⦄, i ≠ j → Disjoint (hairCluster i) (hairCluster j)
  hair_disjoint_base :
    ∀ i j : Fin ℓ, Disjoint (hairCluster i) (base.cluster j)
  hair_disjoint_connectors :
    ∀ i j : Fin ℓ, ∀ (hj : j.1 + 1 < ℓ), ∀ a : Fin w,
      Disjoint (hairCluster i) ((base.connector j hj).path a).vertices
  baseEndpoint : Fin ℓ → Finset V
  hairEndpoint : Fin ℓ → Finset V
  baseEndpoint_subset :
    ∀ i : Fin ℓ, baseEndpoint i ⊆ base.cluster i
  hairEndpoint_subset :
    ∀ i : Fin ℓ, hairEndpoint i ⊆ hairCluster i
  baseEndpoint_card : ∀ i : Fin ℓ, (baseEndpoint i).card = w
  hairEndpoint_card : ∀ i : Fin ℓ, (hairEndpoint i).card = w
  baseEndpoint_avoids_interfaces :
    ∀ i : Fin ℓ,
      Disjoint (baseEndpoint i) (base.left i ∪ base.right i)
  hairEndpoint_well_linked :
    ∀ i : Fin ℓ,
      NodeWellLinkedIn G (hairCluster i) (hairEndpoint i)
  baseEndpoint_linked :
    ∀ i : Fin ℓ,
      NodeLinkedIn G (base.cluster i) (base.left i) (baseEndpoint i)
  hairLinkage :
    ∀ i : Fin ℓ,
      VertexLinkage G (baseEndpoint i) (hairEndpoint i) w
  hair_linkages_disjoint :
    ∀ ⦃i j : Fin ℓ⦄, i ≠ j → ∀ a b : Fin w,
      Disjoint ((hairLinkage i).path a).vertices
        ((hairLinkage j).path b).vertices
  hair_linkages_disjoint_connectors :
    ∀ i j : Fin ℓ, ∀ (hj : j.1 + 1 < ℓ), ∀ a b : Fin w,
      Disjoint ((hairLinkage i).path a).vertices
        ((base.connector j hj).path b).vertices
  hair_linkages_avoid_base :
    ∀ i j : Fin ℓ, ∀ a : Fin w,
      ((hairLinkage i).path a).InternallyAvoids (base.cluster j)
  hair_linkages_avoid_hair :
    ∀ i j : Fin ℓ, ∀ a : Fin w,
      ((hairLinkage i).path a).InternallyAvoids (hairCluster j)

/-- The output of splitting one connected cluster into three disjoint
connected subclusters while retaining prescribed terminal subsets. -/
structure ThreeWayClusterSplit {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B X : Finset V) (q : ℕ) where
  firstCluster : Finset V
  secondCluster : Finset V
  thirdCluster : Finset V
  first_subset : firstCluster ⊆ C
  second_subset : secondCluster ⊆ C
  third_subset : thirdCluster ⊆ C
  first_connected : IsCluster G firstCluster
  second_connected : IsCluster G secondCluster
  third_connected : IsCluster G thirdCluster
  first_second_disjoint : Disjoint firstCluster secondCluster
  first_third_disjoint : Disjoint firstCluster thirdCluster
  second_third_disjoint : Disjoint secondCluster thirdCluster
  firstTerminals : Finset V
  secondTerminals : Finset V
  thirdTerminals : Finset V
  firstTerminals_subset :
    firstTerminals ⊆ A ∩ firstCluster
  secondTerminals_subset :
    secondTerminals ⊆ B ∩ secondCluster
  thirdTerminals_subset :
    thirdTerminals ⊆ X ∩ thirdCluster
  first_card : firstTerminals.card = q
  second_card : secondTerminals.card = q
  third_card : thirdTerminals.card = q
  first_well_linked :
    NodeWellLinkedIn G firstCluster firstTerminals
  second_well_linked :
    NodeWellLinkedIn G secondCluster secondTerminals
  third_well_linked :
    NodeWellLinkedIn G thirdCluster thirdTerminals

/-- The Appendix A.3 split of one cluster into a new base cluster and a
disjoint hair cluster, together with the retained interfaces and hair
linkage. -/
structure HairyClusterSplit {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) (w : ℕ) where
  baseCluster : Finset V
  hairCluster : Finset V
  left : Finset V
  right : Finset V
  baseEndpoint : Finset V
  hairEndpoint : Finset V
  base_subset : baseCluster ⊆ C
  hair_subset : hairCluster ⊆ C
  base_connected : IsCluster G baseCluster
  hair_connected : IsCluster G hairCluster
  clusters_disjoint : Disjoint baseCluster hairCluster
  left_subset_base : left ⊆ baseCluster
  right_subset_base : right ⊆ baseCluster
  baseEndpoint_subset : baseEndpoint ⊆ baseCluster
  hairEndpoint_subset : hairEndpoint ⊆ hairCluster
  left_subset_original : left ⊆ A
  right_subset_original : right ⊆ B
  left_card : left.card = w
  right_card : right.card = w
  baseEndpoint_card : baseEndpoint.card = w
  hairEndpoint_card : hairEndpoint.card = w
  interfaces_disjoint : Disjoint left right
  baseEndpoint_disjoint_interfaces :
    Disjoint baseEndpoint (left ∪ right)
  left_well_linked : NodeWellLinkedIn G baseCluster left
  right_well_linked : NodeWellLinkedIn G baseCluster right
  interfaces_linked : NodeLinkedIn G baseCluster left right
  left_baseEndpoint_linked :
    NodeLinkedIn G baseCluster left baseEndpoint
  hairEndpoint_well_linked :
    NodeWellLinkedIn G hairCluster hairEndpoint
  hairLinkage :
    VertexLinkage G baseEndpoint hairEndpoint w
  hairLinkage_stays_in_cluster :
    ∀ i : Fin w, (hairLinkage.path i).StaysIn C
  hairLinkage_avoids_base :
    ∀ i : Fin w, (hairLinkage.path i).InternallyAvoids baseCluster
  hairLinkage_avoids_hair :
    ∀ i : Fin w, (hairLinkage.path i).InternallyAvoids hairCluster

end Lax17.PathOfSets
