import Lax17Proofs.Source.ScaledLinkedSubsets
import Lax17Proofs.Source.Theorem214Nonconstructive
import Lax17Proofs.Source.TreeOfSetsBandwidth
import Lax17Proofs.Source.TreeOfSetsRestriction

namespace Lax17Proofs

universe u v w

/-!
# Strongifying a bandwidth tree-of-sets system

This module formalizes the connector-restriction part of Chekuri--Chuzhoy
Lemma 4.2 (Lemma 4.5 in the journal version).  Each unoriented meta-edge is
processed in its increasing `Fin` orientation.  A node-well-linked carrier is
first selected at the source endpoint, the connector is restricted to it, and
a second carrier is selected at the target endpoint.  A final restriction to
the requested common width therefore uses the same path indices at both ends.
-/

namespace SimpleGraph


open scoped Classical

namespace BandwidthTreeOfSetsSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {m w alphaNum alphaDen Delta b c W : ℕ}

/-- The coherent choices made on one increasing orientation of a meta-edge.
The two carrier sets retain the node-well-linked supersets used later to prove
linkedness between final interfaces incident with the same cluster. -/
structure EdgeStrongificationChoice
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (i j : Fin m) (hij : T.metaTree.Adj i j) where
  indexSet : Finset (T.connector i j hij).Index
  sourceCarrier : Finset V
  targetCarrier : Finset V
  sourceCarrier_subset : sourceCarrier ⊆ T.interface i j hij
  targetCarrier_subset : targetCarrier ⊆ T.interface j i (T.metaTree.symm hij)
  sourceCarrier_card : sourceCarrier.card = b
  targetCarrier_card : targetCarrier.card = c
  sourceCarrier_nodeWellLinked :
    NodeWellLinkedIn G (T.cluster i) sourceCarrier
  targetCarrier_nodeWellLinked :
    NodeWellLinkedIn G (T.cluster j) targetCarrier
  indexSet_card : indexSet.card = W
  finalSource_subset_carrier :
    (T.connector i j hij).sourceSet indexSet ⊆ sourceCarrier
  finalTarget_subset_carrier :
    (T.connector i j hij).targetSet indexSet ⊆ targetCarrier

/-- One connector admits the two-stage restriction used in Lemma 4.2.

The first displayed floor bound boosts the original source interface.  After
restricting to `b` paths, the second bound boosts the corresponding target
interface.  The last subset choice equalizes every connector at width `W`. -/
theorem exists_edgeStrongificationChoice
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hb : b ≤ (3 * alphaNum * w) / (10 * Delta * alphaDen))
    (hc : c ≤ (3 * alphaNum * b) / (10 * Delta * alphaDen))
    (hWc : W ≤ c)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    Nonempty (EdgeStrongificationChoice (b := b) (c := c) (W := W) T i j hij) := by
  classical
  let P := T.connector i j hij
  rcases ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := G) (C := T.cluster i) (T := T.interface i j hij)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Delta) (κ := w)
      (T.cluster_connected i) hdegree hDelta halpha_pos halpha_le
      (T.interface_card i j hij) (T.interface_scaledEdgeWellLinked i j hij) with
    ⟨Sbig, hSbig, hSbig_card, hSbig_node⟩
  have hbSbig : b ≤ Sbig.card := hb.trans hSbig_card
  rcases Finset.exists_subset_card_eq hbSbig with ⟨S, hSSbig, hScard⟩
  have hSinterface : S ⊆ T.interface i j hij := subset_trans hSSbig hSbig
  have hSnode : NodeWellLinkedIn G (T.cluster i) S :=
    hSbig_node.mono_terminals hSSbig
  let I₁ : Finset P.Index := P.sourceIndexSetOfSubset S
  have hI₁card : I₁.card = b := by
    simpa [I₁, P, hScard] using P.sourceIndexSetOfSubset_card hSinterface
  let U : Finset V := P.targetSet I₁
  have hUcard : U.card = b := by simp [U, hI₁card]
  have hUinterface : U ⊆ T.interface j i (T.metaTree.symm hij) := by
    exact P.targetSet_subset_right I₁
  have hUwell :
      Section46.ScaledEdgeWellLinkedIn G (T.cluster j) U alphaNum alphaDen :=
    Section46.ScaledEdgeWellLinkedIn.mono_terminals
      (T.interface_scaledEdgeWellLinked j i (T.metaTree.symm hij)) hUinterface
  rcases ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := G) (C := T.cluster j) (T := U)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Delta) (κ := b)
      (T.cluster_connected j) hdegree hDelta halpha_pos halpha_le hUcard hUwell with
    ⟨Tbig, hTbig, hTbig_card, hTbig_node⟩
  have hcTbig : c ≤ Tbig.card := hc.trans hTbig_card
  rcases Finset.exists_subset_card_eq hcTbig with ⟨R, hRTbig, hRcard⟩
  have hRU : R ⊆ U := subset_trans hRTbig hTbig
  have hRnode : NodeWellLinkedIn G (T.cluster j) R :=
    hTbig_node.mono_terminals hRTbig
  have hWR : W ≤ R.card := by simpa [hRcard] using hWc
  rcases Finset.exists_subset_card_eq hWR with ⟨Rfinal, hRfinalR, hRfinalcard⟩
  let I : Finset P.Index := P.targetIndexSetOfSubset Rfinal
  have hRfinalU : Rfinal ⊆ U := subset_trans hRfinalR hRU
  have hII₁ : I ⊆ I₁ := by
    exact P.targetIndexSetOfSubset_subset_indexSet hRfinalU
  have hIcard : I.card = W := by
    simpa [I, P, hRfinalcard] using
      P.targetIndexSetOfSubset_card (subset_trans hRfinalU hUinterface)
  refine ⟨{
    indexSet := I
    sourceCarrier := S
    targetCarrier := R
    sourceCarrier_subset := hSinterface
    targetCarrier_subset := subset_trans hRU hUinterface
    sourceCarrier_card := hScard
    targetCarrier_card := hRcard
    sourceCarrier_nodeWellLinked := hSnode
    targetCarrier_nodeWellLinked := hRnode
    indexSet_card := hIcard
    finalSource_subset_carrier := ?_
    finalTarget_subset_carrier := ?_ }⟩
  · have hsource_mono := P.sourceSet_mono hII₁
    simpa [I₁, P, P.sourceSet_sourceIndexSetOfSubset hSinterface] using hsource_mono
  · have htarget_eq : P.targetSet I = Rfinal :=
      P.targetSet_targetIndexSetOfSubset (subset_trans hRfinalU hUinterface)
    change P.targetSet I ⊆ R
    rw [htarget_eq]
    exact hRfinalR

/-- One coherent strongification choice for every unordered meta-edge, stored
in the increasing orientation. -/
abbrev StrongificationChoices
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) :=
  (i j : Fin m) → (hij : T.metaTree.Adj i j) → i < j →
    EdgeStrongificationChoice (b := b) (c := c) (W := W) T i j hij

/-- The family of edge choices supplied by the two-stage producer. -/
noncomputable def strongificationChoices
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hb : b ≤ (3 * alphaNum * w) / (10 * Delta * alphaDen))
    (hc : c ≤ (3 * alphaNum * b) / (10 * Delta * alphaDen))
    (hWc : W ≤ c) : StrongificationChoices (b := b) (c := c) (W := W) T :=
  fun i j hij _hij_lt => Classical.choice <|
    T.exists_edgeStrongificationChoice hdegree hDelta halpha_pos halpha_le
      hb hc hWc i j hij

namespace StrongificationChoices

variable {T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen}

/-- Forget the carrier certificates and retain the canonical connector index
sets consumed by `TreeOfSetsSystem.StrongRestrictionData`. -/
noncomputable def indexSets
    (D : StrongificationChoices (b := b) (c := c) (W := W) T) :
    T.toTreeOfSetsSystem.CanonicalIndexSets :=
  fun i j hij hij_lt => (D i j hij hij_lt).indexSet

/-- The node-well-linked carrier at an oriented connector endpoint. -/
noncomputable def endpointCarrier
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) : Finset V := by
  classical
  by_cases h : i < j
  · exact (D i j hij h).sourceCarrier
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    exact (D j i (T.metaTree.symm hij) hji).targetCarrier

/-- Every endpoint carrier lies in the original interface. -/
theorem endpointCarrier_subset_interface
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    D.endpointCarrier i j hij ⊆ T.interface i j hij := by
  classical
  by_cases h : i < j
  · simpa [endpointCarrier, h] using (D i j hij h).sourceCarrier_subset
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [endpointCarrier, h, hji] using
      (D j i (T.metaTree.symm hij) hji).targetCarrier_subset

/-- Every endpoint carrier is node-well-linked in its cluster. -/
theorem endpointCarrier_nodeWellLinked
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    NodeWellLinkedIn G (T.cluster i) (D.endpointCarrier i j hij) := by
  classical
  by_cases h : i < j
  · simpa [endpointCarrier, h] using
      (D i j hij h).sourceCarrier_nodeWellLinked
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [endpointCarrier, h, hji] using
      (D j i (T.metaTree.symm hij) hji).targetCarrier_nodeWellLinked

/-- Every endpoint carrier has at least the smaller second-stage size `c`. -/
theorem c_le_endpointCarrier_card
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (hcb : c ≤ b) (i j : Fin m) (hij : T.metaTree.Adj i j) :
    c ≤ (D.endpointCarrier i j hij).card := by
  classical
  by_cases h : i < j
  · simpa [endpointCarrier, h, (D i j hij h).sourceCarrier_card] using hcb
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simp [endpointCarrier, h,
      (D j i (T.metaTree.symm hij) hji).targetCarrier_card]

/-- The final coherent restricted interface lies in its node-well-linked
carrier. -/
theorem restrictedInterface_subset_endpointCarrier
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    T.toTreeOfSetsSystem.restrictedInterface D.indexSets i j hij ⊆
      D.endpointCarrier i j hij := by
  classical
  by_cases h : i < j
  · simpa [TreeOfSetsSystem.restrictedInterface, endpointCarrier, indexSets, h]
      using (D i j hij h).finalSource_subset_carrier
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [TreeOfSetsSystem.restrictedInterface, endpointCarrier, indexSets, h, hji]
      using (D j i (T.metaTree.symm hij) hji).finalTarget_subset_carrier

/-- Every final coherent restricted interface has the requested width. -/
theorem restrictedInterface_card
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    (T.toTreeOfSetsSystem.restrictedInterface D.indexSets i j hij).card = W := by
  classical
  by_cases h : i < j
  · simpa [TreeOfSetsSystem.restrictedInterface, indexSets, h] using
      (D i j hij h).indexSet_card
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [TreeOfSetsSystem.restrictedInterface, indexSets, h, hji] using
      (D j i (T.metaTree.symm hij) hji).indexSet_card

/-- The carrier union for two incident meta-edges inherits the cluster's
scaled bandwidth. -/
theorem endpointCarrier_union_scaledEdgeWellLinked
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    {i j k : Fin m} (hij : T.metaTree.Adj i j)
    (hik : T.metaTree.Adj i k) :
    Section46.ScaledEdgeWellLinkedIn G (T.cluster i)
      (D.endpointCarrier i j hij ∪ D.endpointCarrier i k hik)
      alphaNum alphaDen := by
  apply Section46.ScaledEdgeWellLinkedIn.mono_terminals
    (T.boundaryReserve_scaledEdgeWellLinked i)
  exact Finset.union_subset
    (subset_trans (D.endpointCarrier_subset_interface i j hij)
      (T.interface_subset_boundaryReserve i j hij))
    (subset_trans (D.endpointCarrier_subset_interface i k hik)
      (T.interface_subset_boundaryReserve i k hik))

/-- The two-stage choices provide all non-inherited fields needed to build a
strong restriction of the original tree-of-sets system. -/
noncomputable def toStrongRestrictionData
    (D : StrongificationChoices (b := b) (c := c) (W := W) T)
    (hdegree : MaxDegreeAtMost G Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hcb : c ≤ b) (hWpos : 0 < W)
    (hlinked : 2 * Delta * alphaDen * W ≤ alphaNum * c) :
    TreeOfSetsSystem.StrongRestrictionData T.toTreeOfSetsSystem W where
  width_pos := hWpos
  indexSet := D.indexSets
  indexSet_card := fun i j hij hij_lt => (D i j hij hij_lt).indexSet_card
  interface_nodeWellLinked := by
    intro i j hij
    exact (D.endpointCarrier_nodeWellLinked i j hij).mono_terminals
      (D.restrictedInterface_subset_endpointCarrier i j hij)
  interface_pair_nodeLinked := by
    intro i j k hij hik hjk
    have hcarrier_disj :
        Disjoint (D.endpointCarrier i j hij) (D.endpointCarrier i k hik) :=
      (T.interface_disjoint hij hik hjk).mono
        (D.endpointCarrier_subset_interface i j hij)
        (D.endpointCarrier_subset_interface i k hik)
    apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked
      hdegree halpha_pos halpha_le hcarrier_disj
      (D.c_le_endpointCarrier_card hcb i j hij)
      (D.c_le_endpointCarrier_card hcb i k hik)
      (D.endpointCarrier_union_scaledEdgeWellLinked hij hik)
      (D.endpointCarrier_nodeWellLinked i j hij)
      (D.endpointCarrier_nodeWellLinked i k hik)
      (D.restrictedInterface_subset_endpointCarrier i j hij)
      (D.restrictedInterface_subset_endpointCarrier i k hik)
      (by rw [D.restrictedInterface_card i j hij,
        D.restrictedInterface_card i k hik])
      (by simpa [D.restrictedInterface_card i j hij] using hlinked)

end StrongificationChoices

/-- Source-faithful, axiom-free strongification of a bandwidth tree-of-sets
system, with all integer rounding losses exposed as inequalities. -/
theorem exists_strongTreeOfSetsSystem_of_bandwidth
    (T : BandwidthTreeOfSetsSystem G m w alphaNum alphaDen)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (halpha_pos : 0 < alphaNum) (halpha_le : alphaNum ≤ alphaDen)
    (hb : b ≤ (3 * alphaNum * w) / (10 * Delta * alphaDen))
    (hc : c ≤ (3 * alphaNum * b) / (10 * Delta * alphaDen))
    (hcb : c ≤ b) (hWpos : 0 < W) (hWc : W ≤ c)
    (hlinked : 2 * Delta * alphaDen * W ≤ alphaNum * c) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  classical
  let D := T.strongificationChoices hdegree hDelta halpha_pos halpha_le hb hc hWc
  exact ⟨(D.toStrongRestrictionData
    hdegree halpha_pos halpha_le hcb hWpos hlinked).toStrongTreeOfSetsSystem⟩

end BandwidthTreeOfSetsSystem
end SimpleGraph

end Lax17Proofs
