import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthBridge
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Leaves
import Lax17Proofs.Source.FlowDegree
import Lax17Proofs.Source.ScaledLinkedSubsets
import Lax17Proofs.Source.ScaledWellLinkedPathFlow

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1: Claim 5.14 flow chains

This module formalizes the deterministic flow-chain part of preprint
Claim 5.14 (journal Claim 5.16).  A support-tree edge supplies a family of
direct host paths with distinct endpoints.  At every internal router, a
bounded-congestion integral routing joins the incoming and outgoing boundary
sets.  The routings are synchronized on one finite token type and concatenated
with cycle erasure.  Consequently values are preserved, while edge congestion
adds along the chain.

The last theorem scales one such root-to-leaf routing for every selected leaf
and feeds the resulting `OrientedPathFlow` family directly to the proved
Claim 5.15 extraction theorem.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Flow


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace GraphPath

/-- Concatenate two paths with matching endpoints and erase any cycles in the
resulting walk.  This is the path operation needed for Claim 5.14: distinct
support-tree segments need not be internally vertex-disjoint. -/
noncomputable def concatErase
    (P Q : Lax17Proofs.SimpleGraph.GraphPath G) (h : P.target = Q.source) :
    Lax17Proofs.SimpleGraph.GraphPath G where
  source := P.source
  target := Q.target
  walk := (P.walk.append (Q.walk.copy h.symm rfl)).toPath.val
  isPath := (P.walk.append (Q.walk.copy h.symm rfl)).toPath.property

@[simp] theorem concatErase_source
    (P Q : Lax17Proofs.SimpleGraph.GraphPath G) (h : P.target = Q.source) :
    (concatErase P Q h).source = P.source :=
  rfl

@[simp] theorem concatErase_target
    (P Q : Lax17Proofs.SimpleGraph.GraphPath G) (h : P.target = Q.source) :
    (concatErase P Q h).target = Q.target :=
  rfl

theorem concatErase_vertexSet_subset
    (P Q : Lax17Proofs.SimpleGraph.GraphPath G) (h : P.target = Q.source) :
    (concatErase P Q h).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  classical
  intro v hv
  have hvPath :
      v ∈ ((P.walk.append (Q.walk.copy h.symm rfl)).toPath :
        G.Walk P.source Q.target).support := by
    simpa [concatErase, Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using hv
  have hvWalk :
      v ∈ (P.walk.append (Q.walk.copy h.symm rfl)).support :=
    _root_.SimpleGraph.Walk.support_toPath_subset _ hvPath
  simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] using hvWalk

theorem concatErase_edgeSet_subset
    (P Q : Lax17Proofs.SimpleGraph.GraphPath G) (h : P.target = Q.source) :
    (concatErase P Q h).edgeSet ⊆ P.edgeSet ∪ Q.edgeSet := by
  classical
  intro e he
  have hePath :
      e ∈ ((P.walk.append (Q.walk.copy h.symm rfl)).toPath :
        G.Walk P.source Q.target).edges := by
    simpa [concatErase, Lax17Proofs.SimpleGraph.GraphPath.edgeSet] using he
  have heWalk :
      e ∈ (P.walk.append (Q.walk.copy h.symm rfl)).edges :=
    _root_.SimpleGraph.Walk.edges_toPath_subset _ hePath
  simpa [Lax17Proofs.SimpleGraph.GraphPath.edgeSet,
    _root_.SimpleGraph.Walk.edges_append] using heWalk

end GraphPath

/-- An integral unit routing on a fixed token type.

The token index is retained across every support-tree segment.  Injectivity of
both endpoint maps is exactly the distinct-boundary-endpoint invariant in the
proof of Claim 5.14. -/
structure SynchronizedRouting
    (G : _root_.SimpleGraph V) (S T : Finset V) (ι : Type*)
    [Fintype ι] [DecidableEq ι] where
  path : ι → Lax17Proofs.SimpleGraph.GraphPath G
  source_mem : ∀ i, (path i).source ∈ S
  target_mem : ∀ i, (path i).target ∈ T
  source_injective : Function.Injective fun i => (path i).source
  target_injective : Function.Injective fun i => (path i).target

namespace SynchronizedRouting

variable {S T U : Finset V} {ι : Type}
variable [Fintype ι] [DecidableEq ι]

/-- Number of routed tokens using an edge. -/
noncomputable def edgeLoadNat
    (R : SynchronizedRouting G S T ι) (e : Sym2 V) : Nat :=
  (Finset.univ.filter fun i => e ∈ (R.path i).edgeSet).card

/-- Integral edge-congestion bound. -/
def EdgeCongestionAtMost
    (R : SynchronizedRouting G S T ι) (η : Nat) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → R.edgeLoadNat e ≤ η

/-- Every routed path avoids `A` internally. -/
def InternallyDisjointFromSet
    (R : SynchronizedRouting G S T ι) (A : Finset V) : Prop :=
  ∀ i, (R.path i).InternallyDisjointFromSet A

/-- Reverse every path in a synchronized routing. -/
noncomputable def reverse (R : SynchronizedRouting G S T ι) :
    SynchronizedRouting G T S ι where
  path := fun i => (R.path i).reverse
  source_mem := R.target_mem
  target_mem := R.source_mem
  source_injective := R.target_injective
  target_injective := R.source_injective

@[simp] theorem reverse_path (R : SynchronizedRouting G S T ι) (i : ι) :
    (R.reverse.path i) = (R.path i).reverse :=
  rfl

@[simp] theorem reverse_edgeLoadNat
    (R : SynchronizedRouting G S T ι) (e : Sym2 V) :
    R.reverse.edgeLoadNat e = R.edgeLoadNat e := by
  classical
  simp [edgeLoadNat]

theorem reverse_edgeCongestionAtMost
    (R : SynchronizedRouting G S T ι) {η : Nat}
    (hη : R.EdgeCongestionAtMost η) :
    R.reverse.EdgeCongestionAtMost η := by
  intro e he
  simpa using hη e he

theorem reverse_internallyDisjointFromSet
    (R : SynchronizedRouting G S T ι) {A : Finset V}
    (hA : R.InternallyDisjointFromSet A) :
    R.reverse.InternallyDisjointFromSet A := by
  intro i
  intro v hvPath hvA
  have hvPath' : v ∈ (R.path i).vertexSet := by
    simpa using hvPath
  rcases hA i hvPath' hvA with hvSource | hvTarget
  · exact Or.inr hvSource
  · exact Or.inl hvTarget

/-- Reindex a synchronized routing by an equivalent finite token type. -/
noncomputable def reindex
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G S T ι) (e : κ ≃ ι) :
    SynchronizedRouting G S T κ where
  path := fun i => R.path (e i)
  source_mem := fun i => R.source_mem (e i)
  target_mem := fun i => R.target_mem (e i)
  source_injective := fun _ _ h => e.injective (R.source_injective h)
  target_injective := fun _ _ h => e.injective (R.target_injective h)

@[simp] theorem reindex_path
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G S T ι) (e : κ ≃ ι) (i : κ) :
    (R.reindex e).path i = R.path (e i) :=
  rfl

theorem reindex_edgeCongestionAtMost
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : SynchronizedRouting G S T ι) (e : κ ≃ ι) {η : Nat}
    (hη : R.EdgeCongestionAtMost η) :
    (R.reindex e).EdgeCongestionAtMost η := by
  classical
  intro edge hedge
  have hcard :
      ((Finset.univ : Finset κ).filter fun i =>
          edge ∈ (R.path (e i)).edgeSet).card =
        ((Finset.univ : Finset ι).filter fun i =>
          edge ∈ (R.path i).edgeSet).card := by
    apply Finset.card_bij (fun i _ => e i)
    · intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i₁ hi₁ i₂ hi₂ hij
      exact e.injective hij
    · intro j hj
      refine ⟨e.symm j, ?_, by simp⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hj).2⟩
  exact hcard.le.trans (hη edge hedge)

/-- View a synchronized routing in a same-vertex supergraph. -/
noncomputable def mapLe
    (R : SynchronizedRouting G S T ι)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    SynchronizedRouting H S T ι where
  path := fun i => (R.path i).mapLe hGH
  source_mem := R.source_mem
  target_mem := R.target_mem
  source_injective := R.source_injective
  target_injective := R.target_injective

@[simp] theorem mapLe_path
    (R : SynchronizedRouting G S T ι)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) (i : ι) :
    (R.mapLe hGH).path i = (R.path i).mapLe hGH :=
  rfl

theorem mapLe_edgeCongestionAtMost
    (R : SynchronizedRouting G S T ι)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) {η : Nat}
    (hη : R.EdgeCongestionAtMost η) :
    (R.mapLe hGH).EdgeCongestionAtMost η := by
  intro edge hedge
  by_cases hedgeG : edge ∈ G.edgeSet
  · simpa [edgeLoadNat, mapLe, GraphPath.mapLe_edgeSet] using hη edge hedgeG
  · have hnot : ∀ i : ι, edge ∉ (R.path i).edgeSet := by
      intro i hi
      exact hedgeG ((R.path i).edgeSet_subset_edgeSet hi)
    simp [edgeLoadNat, mapLe, GraphPath.mapLe_edgeSet, hnot]

/-- Concatenate two token-synchronized routings.  Cycle erasure permits
arbitrary intersections away from the matching intermediate endpoint. -/
noncomputable def concat
    (R : SynchronizedRouting G S T ι)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (R.path i).target = (Q.path i).source) :
    SynchronizedRouting G S U ι where
  path := fun i => GraphPath.concatErase (R.path i) (Q.path i) (hmatch i)
  source_mem := R.source_mem
  target_mem := Q.target_mem
  source_injective := R.source_injective
  target_injective := Q.target_injective

@[simp] theorem concat_path
    (R : SynchronizedRouting G S T ι)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (R.path i).target = (Q.path i).source)
    (i : ι) :
    (R.concat Q hmatch).path i =
      GraphPath.concatErase (R.path i) (Q.path i) (hmatch i) :=
  rfl

theorem concat_edgeLoadNat_le
    (R : SynchronizedRouting G S T ι)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (R.path i).target = (Q.path i).source)
    (e : Sym2 V) :
    (R.concat Q hmatch).edgeLoadNat e ≤
      R.edgeLoadNat e + Q.edgeLoadNat e := by
  classical
  let A := Finset.univ.filter fun i => e ∈ (R.path i).edgeSet
  let B := Finset.univ.filter fun i => e ∈ (Q.path i).edgeSet
  have hsubset :
      (Finset.univ.filter fun i =>
          e ∈ ((R.concat Q hmatch).path i).edgeSet) ⊆ A ∪ B := by
    intro i hi
    have hiEdge :
        e ∈ (R.path i).edgeSet ∪ (Q.path i).edgeSet :=
      GraphPath.concatErase_edgeSet_subset
        (R.path i) (Q.path i) (hmatch i) (Finset.mem_filter.mp hi).2
    rcases Finset.mem_union.mp hiEdge with hiR | hiQ
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨by simp, hiR⟩)
    · exact Finset.mem_union_right A (Finset.mem_filter.mpr ⟨by simp, hiQ⟩)
  calc
    (R.concat Q hmatch).edgeLoadNat e ≤ (A ∪ B).card :=
      Finset.card_le_card hsubset
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ = R.edgeLoadNat e + Q.edgeLoadNat e := rfl

/-- Congestion adds under concatenation along one support-tree path. -/
theorem concat_edgeCongestionAtMost
    (R : SynchronizedRouting G S T ι)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (R.path i).target = (Q.path i).source)
    {ηR ηQ : Nat}
    (hR : R.EdgeCongestionAtMost ηR)
    (hQ : Q.EdgeCongestionAtMost ηQ) :
    (R.concat Q hmatch).EdgeCongestionAtMost (ηR + ηQ) := by
  intro e he
  exact (concat_edgeLoadNat_le R Q hmatch e).trans
    (Nat.add_le_add (hR e he) (hQ e he))

/-- Internal avoidance is preserved by loop-erased concatenation when the
outer endpoints are outside the forbidden set. -/
theorem concat_internallyDisjointFromSet
    (R : SynchronizedRouting G S T ι)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (R.path i).target = (Q.path i).source)
    {A : Finset V}
    (hR : R.InternallyDisjointFromSet A)
    (hQ : Q.InternallyDisjointFromSet A)
    (hT : Disjoint T A) :
    (R.concat Q hmatch).InternallyDisjointFromSet A := by
  intro i v hvPath hvA
  have hvUnion :
      v ∈ (R.path i).vertexSet ∪ (Q.path i).vertexSet :=
    GraphPath.concatErase_vertexSet_subset
      (R.path i) (Q.path i) (hmatch i) hvPath
  rcases Finset.mem_union.mp hvUnion with hvR | hvQ
  · rcases hR i hvR hvA with hvSource | hvTarget
    · exact Or.inl hvSource
    · exact False.elim
        (Finset.disjoint_left.mp hT
          (hvTarget ▸ R.target_mem i) hvA)
  · rcases hQ i hvQ hvA with hvSource | hvTarget
    · exact False.elim
        (Finset.disjoint_left.mp hT
          (hvSource ▸ Q.source_mem i) hvA)
    · exact Or.inr hvTarget

/-- Regard a synchronized integral routing as the concrete rational path flow
used by Claim 5.15. -/
noncomputable def toOrientedPathFlow
    (R : SynchronizedRouting G S T ι) :
    OrientedPathFlow G S T where
  Index := ι
  path := R.path
  source_mem := R.source_mem
  target_mem := R.target_mem
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

@[simp] theorem toOrientedPathFlow_value
    (R : SynchronizedRouting G S T ι) :
    R.toOrientedPathFlow.value = Fintype.card ι := by
  classical
  change (∑ _i : ι, (1 : Rat)) = Fintype.card ι
  simp

theorem toOrientedPathFlow_sourceLoadExactlyOne
    (R : SynchronizedRouting G S T ι)
    (hsource : S.card = Fintype.card ι) :
    R.toOrientedPathFlow.SourceLoadExactlyOne := by
  classical
  intro v hvS
  have hRangeEq :
      (Finset.univ.image fun i => (R.path i).source) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact R.source_mem i
    · rw [Finset.card_image_of_injective _ R.source_injective, hsource]
      simp
  have hvRange : v ∈ Finset.univ.image fun i => (R.path i).source := by
    rw [hRangeEq]
    exact hvS
  rcases Finset.mem_image.mp hvRange with ⟨i, _hi, hi⟩
  change (∑ j : ι, if (R.path j).source = v then (1 : Rat) else 0) = 1
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _hj hji
    have hne : (R.path j).source ≠ v := by
      intro hj
      exact hji (R.source_injective (hj.trans hi.symm))
    simp [hne]
  · simp

theorem toOrientedPathFlow_targetLoadExactlyOne
    (R : SynchronizedRouting G S T ι)
    (htarget : T.card = Fintype.card ι) :
    R.toOrientedPathFlow.TargetLoadExactlyOne := by
  classical
  intro v hvT
  have hRangeEq :
      (Finset.univ.image fun i => (R.path i).target) = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact R.target_mem i
    · rw [Finset.card_image_of_injective _ R.target_injective, htarget]
      simp
  have hvRange : v ∈ Finset.univ.image fun i => (R.path i).target := by
    rw [hRangeEq]
    exact hvT
  rcases Finset.mem_image.mp hvRange with ⟨i, _hi, hi⟩
  change (∑ j : ι, if (R.path j).target = v then (1 : Rat) else 0) = 1
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _hj hji
    have hne : (R.path j).target ≠ v := by
      intro hj
      exact hji (R.target_injective (hj.trans hi.symm))
    simp [hne]
  · simp

theorem toOrientedPathFlow_isUnitFlow
    (R : SynchronizedRouting G S T ι)
    (hsource : S.card = Fintype.card ι)
    (htarget : T.card = Fintype.card ι) :
    R.toOrientedPathFlow.IsUnitFlow :=
  ⟨R.toOrientedPathFlow_sourceLoadExactlyOne hsource,
    R.toOrientedPathFlow_targetLoadExactlyOne htarget⟩

theorem toOrientedPathFlow_edgeLoad
    (R : SynchronizedRouting G S T ι) (e : Sym2 V) :
    R.toOrientedPathFlow.edgeLoad e = R.edgeLoadNat e := by
  classical
  change
    (∑ i : ι, if e ∈ (R.path i).edgeSet then (1 : Rat) else 0) =
      ((Finset.univ.filter fun i => e ∈ (R.path i).edgeSet).card : Rat)
  rw [Finset.sum_boole]

theorem toOrientedPathFlow_edgeCongestionAtMost
    (R : SynchronizedRouting G S T ι) {η : Nat}
    (hη : R.EdgeCongestionAtMost η) :
    R.toOrientedPathFlow.EdgeCongestionAtMost η := by
  intro e he
  rw [toOrientedPathFlow_edgeLoad]
  exact_mod_cast hη e he

theorem toOrientedPathFlow_flowsDirect
    {m : Nat} {cluster : Fin m → Finset V} {root : Finset V}
    (i : Fin m)
    (R : SynchronizedRouting G (cluster i) root ι)
    (hdirect :
      R.InternallyDisjointFromSet
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion cluster)) :
    ∀ a : R.toOrientedPathFlow.Index,
      (R.toOrientedPathFlow.path a).InternallyDisjointFromSet
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion cluster) :=
  by
    intro a
    exact hdirect a

/-- The synchronized integral routing underlying the capacity-expansion unit
flow. -/
noncomputable def ofCapacityExpansionPacking
    [DecidableRel G.Adj] {D : Nat}
    (P : EdgePathPacking
      (ScaledWellLinkedPathFlow.CapacityExpansion.graph G S T D)
      (ScaledWellLinkedPathFlow.CapacityExpansion.sourceLeaves
        (G := G) S T D)
      (ScaledWellLinkedPathFlow.CapacityExpansion.targetLeaves
        (G := G) S T D)) :
    SynchronizedRouting G S T P.Index where
  path := fun i =>
    ScaledWellLinkedPathFlow.CapacityExpansion.projectPath (G := G)
      ((P.path i).orient (P.connects i))
  source_mem := fun i =>
    (ScaledWellLinkedPathFlow.CapacityExpansion.projectedFlow
      (G := G) P).source_mem i
  target_mem := fun i =>
    (ScaledWellLinkedPathFlow.CapacityExpansion.projectedFlow
      (G := G) P).target_mem i
  source_injective :=
    ScaledWellLinkedPathFlow.CapacityExpansion.projectedFlow_source_injective P
  target_injective :=
    ScaledWellLinkedPathFlow.CapacityExpansion.projectedFlow_target_injective P

theorem ofCapacityExpansionPacking_edgeCongestionAtMost
    [DecidableRel G.Adj] {D : Nat}
    (P : EdgePathPacking
      (ScaledWellLinkedPathFlow.CapacityExpansion.graph G S T D)
      (ScaledWellLinkedPathFlow.CapacityExpansion.sourceLeaves
        (G := G) S T D)
      (ScaledWellLinkedPathFlow.CapacityExpansion.targetLeaves
        (G := G) S T D)) :
    (ofCapacityExpansionPacking (G := G) P).EdgeCongestionAtMost D := by
  intro edge hedge
  exact
    ScaledWellLinkedPathFlow.CapacityExpansion.projected_edge_users_card_le
      P edge hedge

end SynchronizedRouting

/-! ## Numerator-one scaled-bandwidth routing -/

/-- Equal-size subsets of a numerator-one scaled edge-well-linked terminal set
have a synchronized integral routing.  The capacity expansion realizes the
factor `D` as `D` parallel edge channels; projecting the resulting
edge-disjoint paths gives congestion at most `D` in the original graph.

This is the local routing consequence used at the internal routers in
Chekuri--Chuzhoy Section 5.4.1. -/
theorem exists_synchronizedRouting_of_scaledEdgeWellLinkedIn_one
    {C Terminals S T : Finset V} {D width : Nat}
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals 1 D)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hSCard : S.card = width) (hTCard : T.card = width) :
    ∃ R : SynchronizedRouting G S T (Fin width),
      R.EdgeCongestionAtMost D ∧
      ∀ i : Fin width, (R.path i).vertexSet ⊆ C := by
  classical
  let H := inducedOnFinset G C
  have hwellH :
      ScaledEdgeWellLinked H Terminals 1 D := by
    simpa [H] using hwell.toScaledEdgeWellLinked_induced
  have hcard : S.card = T.card := hSCard.trans hTCard.symm
  rcases
      ScaledWellLinkedPathFlow.CapacityExpansion.exists_full_pathPacking
        (G := H) hwellH hS hT hcard with
    ⟨P, hPCard⟩
  let R₀ : SynchronizedRouting H S T P.Index :=
    SynchronizedRouting.ofCapacityExpansionPacking (G := H) P
  let R₁ : SynchronizedRouting G S T P.Index :=
    R₀.mapLe (inducedOnFinset_le (G := G) (C := C))
  have hIndexCard : Fintype.card P.Index = width := by
    simpa [EdgePathPacking.card] using hPCard.trans hSCard
  let e : Fin width ≃ P.Index :=
    (Fintype.equivFinOfCardEq hIndexCard).symm
  let R : SynchronizedRouting G S T (Fin width) := R₁.reindex e
  refine ⟨R, ?_, ?_⟩
  · apply SynchronizedRouting.reindex_edgeCongestionAtMost R₁ e
    apply SynchronizedRouting.mapLe_edgeCongestionAtMost R₀
      (inducedOnFinset_le (G := G) (C := C))
    exact
      SynchronizedRouting.ofCapacityExpansionPacking_edgeCongestionAtMost
        (G := H) P
  · intro i
    have hSC : S ⊆ C := hS.trans hwell.2.2.1
    have hTC : T ⊆ C := hT.trans hwell.2.2.1
    have hsubset :
        (R₀.path (e i)).vertexSet ⊆ C := by
      apply Section46.InducedOnFinset.graphPath_vertexSet_subset_of_connects
        (G := G) (C := C) (A := S) (B := T)
      · exact Or.inl ⟨R₀.source_mem (e i), R₀.target_mem (e i)⟩
      · exact hSC
      · exact hTC
    simpa [R, R₁, SynchronizedRouting.reindex, SynchronizedRouting.mapLe] using
      hsubset

/-- The preceding synchronized routing is available directly from a
truncated-bandwidth router whenever the selected boundary union fits below
the truncation cap. -/
theorem exists_synchronizedRouting_of_truncatedScaledBandwidth_one
    {C S T : Finset V} {cap D width : Nat}
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth G C cap 1 D)
    (hS : S ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G C)
    (hT : T ⊆ ChekuriChuzhoySection5Clustering.interfaceVertices G C)
    (hcard : (S ∪ T).card ≤ cap)
    (hSCard : S.card = width) (hTCard : T.card = width) :
    ∃ R : SynchronizedRouting G S T (Fin width),
      R.EdgeCongestionAtMost D ∧
      ∀ i : Fin width, (R.path i).vertexSet ⊆ C := by
  have hwell :
      Section46.ScaledEdgeWellLinkedIn G C (S ∪ T) 1 D :=
    hband.scaledEdgeWellLinkedIn_of_subset_interface
      (Finset.union_subset hS hT) hcard
  exact exists_synchronizedRouting_of_scaledEdgeWellLinkedIn_one
    hwell Finset.subset_union_left Finset.subset_union_right hSCard hTCard

/-! ## Arbitrary support-tree path chains -/

/-- A fully composed nonempty support-tree path chain, together with the sum
of the segment congestion budgets. -/
structure BoundedRoutingChain (G : _root_.SimpleGraph V) (ι : Type)
    [Fintype ι] [DecidableEq ι]
    (S T : Finset V) (η : Nat) where
  toRouting : SynchronizedRouting G S T ι
  bounded : toRouting.EdgeCongestionAtMost η

namespace BoundedRoutingChain

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S T U : Finset V} {η : Nat}

/-- Start a bounded chain with one support-tree segment. -/
def single
    (R : SynchronizedRouting G S T ι)
    (hR : R.EdgeCongestionAtMost η) :
    BoundedRoutingChain G ι S T η :=
  ⟨R, hR⟩

/-- Enlarge the recorded congestion budget without changing the routing. -/
def weaken
    (chain : BoundedRoutingChain G ι S T η)
    {η' : Nat} (hη : η ≤ η') :
    BoundedRoutingChain G ι S T η' where
  toRouting := chain.toRouting
  bounded := fun e he => (chain.bounded e he).trans hη

@[simp] theorem weaken_toRouting
    (chain : BoundedRoutingChain G ι S T η)
    {η' : Nat} (hη : η ≤ η') :
    (chain.weaken hη).toRouting = chain.toRouting :=
  rfl

/-- Extend a bounded root-to-router chain by one synchronized segment.  This
constructor can be iterated along every edge and internal router on a rooted
support-tree path. -/
noncomputable def snoc
    (chain : BoundedRoutingChain G ι S T η)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (chain.toRouting.path i).target = (Q.path i).source)
    {ηQ : Nat} (hQ : Q.EdgeCongestionAtMost ηQ) :
    BoundedRoutingChain G ι S U (η + ηQ) where
  toRouting := chain.toRouting.concat Q hmatch
  bounded :=
    SynchronizedRouting.concat_edgeCongestionAtMost
      chain.toRouting Q hmatch chain.bounded hQ

@[simp] theorem single_toRouting
    (R : SynchronizedRouting G S T ι)
    (hR : R.EdgeCongestionAtMost η) :
    (single R hR).toRouting = R :=
  rfl

@[simp] theorem snoc_toRouting
    (chain : BoundedRoutingChain G ι S T η)
    (Q : SynchronizedRouting G T U ι)
    (hmatch : ∀ i, (chain.toRouting.path i).target = (Q.path i).source)
    {ηQ : Nat} (hQ : Q.EdgeCongestionAtMost ηQ) :
    (snoc chain Q hmatch hQ).toRouting =
      chain.toRouting.concat Q hmatch :=
  rfl

end BoundedRoutingChain

/-! ## Scaled-bandwidth flow producer -/

namespace OrientedPathFlow

/-- An edge-disjoint path packing induces edge congestion one. -/
theorem ofEdgePathPacking_edgeCongestionAtMost_one
    {S T : Finset V} (P : EdgePathPacking G S T) :
    (OrientedPathFlow.ofEdgePathPacking P).EdgeCongestionAtMost 1 := by
  classical
  intro e heG
  by_cases hused : ∃ i : P.Index, e ∈ (P.path i).edgeSet
  · rcases hused with ⟨i, hi⟩
    unfold OrientedPathFlow.edgeLoad
    change
      (∑ j : P.Index,
        if e ∈ ((P.path j).orient (P.connects j)).edgeSet
        then (1 : Rat) else 0) ≤ 1
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _hj hji
      have hjNot : e ∉ (P.path j).edgeSet := by
        intro hj
        exact Finset.disjoint_left.mp (P.edge_disjoint hji) hj hi
      simp [hjNot]
    · simp
  · unfold OrientedPathFlow.edgeLoad
    change
      (∑ j : P.Index,
        if e ∈ ((P.path j).orient (P.connects j)).edgeSet
        then (1 : Rat) else 0) ≤ 1
    have hnot : ∀ j : P.Index, e ∉ (P.path j).edgeSet := by
      intro j hj
      exact hused ⟨j, hj⟩
    simp [hnot]

/-- The exact path-flow consequence currently available from local scaled
edge-well-linkedness.

The ratio hypothesis is the natural-number ceiling condition for the exact
edge-Menger theorem.  The resulting object is the concrete
`OrientedPathFlow` consumed by the later Claim 5.14/5.15 layer, has exact value
`r`, stays in the router, and has edge congestion one. -/
theorem exists_of_scaledEdgeWellLinkedIn
    {C Terminals S T : Finset V} {alphaNum alphaDen r : Nat}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn
        G C Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hdisj : Disjoint S T)
    (hratio : alphaDen * (r - 1) <
      alphaNum * min S.card T.card) :
    ∃ F : OrientedPathFlow G S T,
      F.value = r ∧
      F.EdgeCongestionAtMost 1 ∧
      ∀ i : F.Index, (F.path i).vertexSet ⊆ C := by
  rcases hwell.exists_exact_edgePathPacking
      hS hT hdisj hratio with ⟨P, hPcard, hPstay⟩
  let F := OrientedPathFlow.ofEdgePathPacking P
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa [F] using hPcard
  · exact ofEdgePathPacking_edgeCongestionAtMost_one P
  · intro i
    change
      ((P.path i).orient (P.connects i)).vertexSet ⊆ C
    simpa using hPstay i

/-- Truncated scaled bandwidth supplies the preceding exact flow whenever the
chosen boundary terminal union fits below the truncation cap. -/
theorem exists_of_truncatedScaledBandwidth
    {C S T : Finset V} {cap alphaNum alphaDen r : Nat}
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G C cap alphaNum alphaDen)
    (hS : S ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G C)
    (hT : T ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G C)
    (hcard : (S ∪ T).card ≤ cap)
    (hdisj : Disjoint S T)
    (hratio : alphaDen * (r - 1) <
      alphaNum * min S.card T.card) :
    ∃ F : OrientedPathFlow G S T,
      F.value = r ∧
      F.EdgeCongestionAtMost 1 ∧
      ∀ i : F.Index, (F.path i).vertexSet ⊆ C := by
  have hwell :
      Section46.ScaledEdgeWellLinkedIn
        G C (S ∪ T) alphaNum alphaDen :=
    hband.scaledEdgeWellLinkedIn_of_subset_interface
      (Finset.union_subset hS hT) hcard
  exact exists_of_scaledEdgeWellLinkedIn
    hwell Finset.subset_union_left Finset.subset_union_right hdisj hratio

end OrientedPathFlow

/-! ## Claim 5.14 to Claim 5.15 -/

open ChekuriChuzhoySection5Phase1Leaves

/-- Regard a path flow as ending in a larger target set.  This changes only
the target-membership certificate. -/
def widenFlowTarget
    {S T U : Finset V} (F : OrientedPathFlow G S T) (hTU : T ⊆ U) :
    OrientedPathFlow G S U where
  Index := F.Index
  path := F.path
  source_mem := F.source_mem
  target_mem := fun i => hTU (F.target_mem i)
  weight := F.weight
  weight_nonneg := F.weight_nonneg

@[simp] theorem widenFlowTarget_path
    {S T U : Finset V} (F : OrientedPathFlow G S T) (hTU : T ⊆ U)
    (i : F.Index) :
    (widenFlowTarget F hTU).path i = F.path i :=
  rfl

@[simp] theorem widenFlowTarget_weight
    {S T U : Finset V} (F : OrientedPathFlow G S T) (hTU : T ⊆ U)
    (i : F.Index) :
    (widenFlowTarget F hTU).weight i = F.weight i :=
  rfl

@[simp] theorem widenFlowTarget_value
    {S T U : Finset V} (F : OrientedPathFlow G S T) (hTU : T ⊆ U) :
    (widenFlowTarget F hTU).value = F.value :=
  rfl

@[simp] theorem widenFlowTarget_vertexLoad
    {S T U : Finset V} (F : OrientedPathFlow G S T) (hTU : T ⊆ U)
    (v : V) :
    (widenFlowTarget F hTU).vertexLoad v = F.vertexLoad v :=
  rfl

/-- Source-facing flow endpoint of Claim 5.14.

Each selected leaf has a synchronized integral routing of `width` paths from
the root router.  The preceding chain API constructs these routings by
alternating support-tree bundles and internal-router routings; its recorded
budget is `eta`.  Reversal and scaling by `c` produce exactly the family of
`OrientedPathFlow`s expected by Claim 5.15.

The final rational inequality is the explicit vertex-capacity calculation:
one flow contributes at most `c * (1 + Delta * eta / 2)` at a vertex, and
there are `m` selected leaves. -/
theorem claim514_scaled_leaf_flows
    {m width quota Delta eta : Nat}
    {cluster : Fin m → Finset V} {root : Finset V}
    (R : ∀ i : Fin m,
      SynchronizedRouting G root (cluster i) (Fin width))
    (hrootCard : root.card = width)
    (hclusterCard : ∀ i, (cluster i).card = width)
    (hrootCluster : ∀ i, Disjoint root (cluster i))
    (hdirect : ∀ i,
      (R i).InternallyDisjointFromSet (selectedUnion cluster))
    (hdegree : MaxDegreeAtMost G Delta)
    (hcongestion : ∀ i, (R i).EdgeCongestionAtMost eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ F : ∀ i : Fin m, OrientedPathFlow G (cluster i) root,
      (∀ i, (quota : Rat) ≤ (F i).value) ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.FlowsDirect F ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.AggregateVertexCongestionAtMostOne F := by
  let F : ∀ i : Fin m, OrientedPathFlow G (cluster i) root :=
    fun i => (R i).reverse.toOrientedPathFlow.scale c hc
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    calc
      (quota : Rat) ≤ c * width := hquota
      _ = (F i).value := by
        simp [F, SynchronizedRouting.toOrientedPathFlow_value]
  · intro i a
    change
      Lax17Proofs.SimpleGraph.GraphPath.InternallyDisjointFromSet
        (((R i).reverse.toOrientedPathFlow.scale c hc).path a)
        (selectedUnion cluster)
    change
      ((R i).reverse.path a).InternallyDisjointFromSet
        (selectedUnion cluster)
    exact (R i).reverse_internallyDisjointFromSet (hdirect i) a
  · intro v
    let B : Rat := 1 + (Delta : Rat) * eta / 2
    have hbase :
        ∀ i : Fin m,
          (R i).reverse.toOrientedPathFlow.vertexLoad v ≤ B := by
      intro i
      exact
        OrientedPathFlow.vertexLoad_le_one_add_half_maxDegree_mul_of_edgeCongestion
          (F := (R i).reverse.toOrientedPathFlow)
          hdegree (by positivity)
          ((R i).reverse.toOrientedPathFlow_edgeCongestionAtMost
            ((R i).reverse_edgeCongestionAtMost (hcongestion i)))
          ((R i).reverse.toOrientedPathFlow_isUnitFlow
            (by simpa using hclusterCard i)
            (by simpa using hrootCard))
          (hrootCluster i).symm v
    calc
      (∑ i : Fin m, (F i).vertexLoad v) =
          ∑ i : Fin m,
            c * (R i).reverse.toOrientedPathFlow.vertexLoad v := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [F]
      _ ≤ ∑ _i : Fin m, c * B := by
        exact Finset.sum_le_sum fun i _hi =>
          mul_le_mul_of_nonneg_left (hbase i) hc
      _ = (m : Rat) * c * B := by
        simp [B]
        ring
      _ ≤ 1 := by
        simpa [B] using hcapacity

/-- Claim 5.14 stated directly from one bounded composed support-tree chain
per selected leaf.  The chain's `eta` index is the explicit sum of all bundle
and internal-router congestion bounds on that rooted path. -/
theorem claim514_scaled_leaf_flows_of_boundedRoutingChains
    {m width quota Delta eta : Nat}
    {cluster : Fin m → Finset V} {root : Finset V}
    (chain : ∀ i : Fin m,
      BoundedRoutingChain G (Fin width) root (cluster i) eta)
    (hrootCard : root.card = width)
    (hclusterCard : ∀ i, (cluster i).card = width)
    (hrootCluster : ∀ i, Disjoint root (cluster i))
    (hdirect : ∀ i,
      (chain i).toRouting.InternallyDisjointFromSet
        (selectedUnion cluster))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ F : ∀ i : Fin m, OrientedPathFlow G (cluster i) root,
      (∀ i, (quota : Rat) ≤ (F i).value) ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.FlowsDirect F ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.AggregateVertexCongestionAtMostOne F :=
  claim514_scaled_leaf_flows
    (fun i => (chain i).toRouting)
    hrootCard hclusterCard hrootCluster hdirect hdegree
    (fun i => (chain i).bounded) hc hquota hcapacity

/-- Chekuri--Chuzhoy preprint Claim 5.14 composed directly with the semantic
Claim 5.15 extraction theorem.

The conclusion is the exact source-replicated, selected-router-pruned path
packing from `claim515_exists_integral_leaf_paths_in_prunedNetwork`. -/
theorem claim514_claim515_exists_integral_leaf_paths
    {m width quota Delta eta : Nat}
    {cluster : Fin m → Finset V} {root : Finset V}
    (R : ∀ i : Fin m,
      SynchronizedRouting G root (cluster i) (Fin width))
    (hroot : Disjoint root (selectedUnion cluster))
    (hrootCard : root.card = width)
    (hclusterCard : ∀ i, (cluster i).card = width)
    (hrootCluster : ∀ i, Disjoint root (cluster i))
    (hdirect : ∀ i,
      (R i).InternallyDisjointFromSet (selectedUnion cluster))
    (hdegree : MaxDegreeAtMost G Delta)
    (hcongestion : ∀ i, (R i).EdgeCongestionAtMost eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G cluster)
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) root),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases claim514_scaled_leaf_flows R hrootCard hclusterCard hrootCluster
      hdirect hdegree hcongestion hc hquota hcapacity with
    ⟨F, hvalue, hflowsDirect, haggregate⟩
  exact
    ChekuriChuzhoySection5Phase1Leaves.Vertex.claim515_exists_integral_leaf_paths_in_prunedNetwork
        F hroot hflowsDirect hquotaPos hvalue haggregate

/-- The strongest chain-facing endpoint in this module: bounded concatenated
root-to-leaf support-tree routings are scaled and passed all the way through
Claim 5.15 to the integral pruned-network packing. -/
theorem claim514_claim515_exists_integral_leaf_paths_of_boundedRoutingChains
    {m width quota Delta eta : Nat}
    {cluster : Fin m → Finset V} {root : Finset V}
    (chain : ∀ i : Fin m,
      BoundedRoutingChain G (Fin width) root (cluster i) eta)
    (hroot : Disjoint root (selectedUnion cluster))
    (hrootCard : root.card = width)
    (hclusterCard : ∀ i, (cluster i).card = width)
    (hrootCluster : ∀ i, Disjoint root (cluster i))
    (hdirect : ∀ i,
      (chain i).toRouting.InternallyDisjointFromSet
        (selectedUnion cluster))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G cluster)
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) root),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) :=
  claim514_claim515_exists_integral_leaf_paths
    (fun i => (chain i).toRouting)
    hroot hrootCard hclusterCard hrootCluster hdirect hdegree
    (fun i => (chain i).bounded) hc hquotaPos hquota hcapacity

/-! ## Source-faithful boundary-subset form -/

/-- Claim 5.14 with the width-sized flow terminals separated from the full
selected leaf routers.  This is the paper-faithful form: the routing ends at
the matching endpoints inside each leaf router, while directness and pruning
refer to the whole router family. -/
theorem claim514_scaled_leaf_boundary_flows
    {m width quota Delta eta : Nat}
    {terminal router : Fin m → Finset V} {root : Finset V}
    (R : ∀ i : Fin m,
      SynchronizedRouting G root (terminal i) (Fin width))
    (hrootCard : root.card = width)
    (hterminalCard : ∀ i, (terminal i).card = width)
    (hrootTerminal : ∀ i, Disjoint root (terminal i))
    (hdirect : ∀ i,
      (R i).InternallyDisjointFromSet (selectedUnion router))
    (hdegree : MaxDegreeAtMost G Delta)
    (hcongestion : ∀ i, (R i).EdgeCongestionAtMost eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ F : ∀ i : Fin m, OrientedPathFlow G (terminal i) root,
      (∀ i, (quota : Rat) ≤ (F i).value) ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.FlowsDirectToRouters
        router F ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.AggregateVertexCongestionAtMostOne
        F := by
  let F : ∀ i : Fin m, OrientedPathFlow G (terminal i) root :=
    fun i => (R i).reverse.toOrientedPathFlow.scale c hc
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    calc
      (quota : Rat) ≤ c * width := hquota
      _ = (F i).value := by
        simp [F, SynchronizedRouting.toOrientedPathFlow_value]
  · intro i a
    change
      ((R i).reverse.path a).InternallyDisjointFromSet
        (selectedUnion router)
    exact (R i).reverse_internallyDisjointFromSet (hdirect i) a
  · intro v
    let B : Rat := 1 + (Delta : Rat) * eta / 2
    have hbase :
        ∀ i : Fin m,
          (R i).reverse.toOrientedPathFlow.vertexLoad v ≤ B := by
      intro i
      exact
        OrientedPathFlow.vertexLoad_le_one_add_half_maxDegree_mul_of_edgeCongestion
          (F := (R i).reverse.toOrientedPathFlow)
          hdegree (by positivity)
          ((R i).reverse.toOrientedPathFlow_edgeCongestionAtMost
            ((R i).reverse_edgeCongestionAtMost (hcongestion i)))
          ((R i).reverse.toOrientedPathFlow_isUnitFlow
            (by simpa using hterminalCard i)
            (by simpa using hrootCard))
          (hrootTerminal i).symm v
    calc
      (∑ i : Fin m, (F i).vertexLoad v) =
          ∑ i : Fin m,
            c * (R i).reverse.toOrientedPathFlow.vertexLoad v := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [F]
      _ ≤ ∑ _i : Fin m, c * B := by
        exact Finset.sum_le_sum fun i _hi =>
          mul_le_mul_of_nonneg_left (hbase i) hc
      _ = (m : Rat) * c * B := by
        simp [B]
        ring
      _ ≤ 1 := by
        simpa [B] using hcapacity

/-- Paper-faithful Claim 5.14/5.15 composition from bounded root-to-boundary
chains.  The produced integral packing is in the network that prunes the full
selected leaf routers. -/
theorem
    claim514_claim515_exists_integral_leaf_paths_of_boundaryChains
    {m width quota Delta eta : Nat}
    {terminal router : Fin m → Finset V} {root : Finset V}
    (chain : ∀ i : Fin m,
      BoundedRoutingChain G (Fin width) root (terminal i) eta)
    (hterminalRouter : ∀ i, terminal i ⊆ router i)
    (hroot : Disjoint root (selectedUnion router))
    (hrootCard : root.card = width)
    (hterminalCard : ∀ i, (terminal i).card = width)
    (hrootTerminal : ∀ i, Disjoint root (terminal i))
    (hdirect : ∀ i,
      (chain i).toRouting.InternallyDisjointFromSet
        (selectedUnion router))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G router)
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) root),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases claim514_scaled_leaf_boundary_flows
      (fun i => (chain i).toRouting)
      hrootCard hterminalCard hrootTerminal hdirect hdegree
      (fun i => (chain i).bounded) hc hquota hcapacity with
    ⟨F, hvalue, hflowsDirect, haggregate⟩
  exact
    ChekuriChuzhoySection5Phase1Leaves.Vertex.claim515_exists_integral_leaf_paths_in_prunedNetwork_of_terminal_subsets
      F hterminalRouter hroot hflowsDirect hquotaPos hvalue haggregate

/-! ## Source-faithful varying root boundaries -/

/-- Claim 5.14 with a separate width-sized root boundary for every selected
leaf.  All those boundary sets lie in the same root router, exactly as in the
paper's independently thinned support-tree paths. -/
theorem claim514_scaled_leaf_flows_of_varying_root_boundaries
    {m width quota Delta eta : Nat}
    {rootTerminal terminal router : Fin m → Finset V}
    {rootRouter : Finset V}
    (R : ∀ i : Fin m,
      SynchronizedRouting G (rootTerminal i) (terminal i) (Fin width))
    (hrootTerminalRouter : ∀ i, rootTerminal i ⊆ rootRouter)
    (hrootTerminalCard : ∀ i, (rootTerminal i).card = width)
    (hterminalCard : ∀ i, (terminal i).card = width)
    (hrootTerminalDisjoint :
      ∀ i, Disjoint (rootTerminal i) (terminal i))
    (hdirect : ∀ i,
      (R i).InternallyDisjointFromSet (selectedUnion router))
    (hdegree : MaxDegreeAtMost G Delta)
    (hcongestion : ∀ i, (R i).EdgeCongestionAtMost eta)
    {c : Rat} (hc : 0 ≤ c)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ F : ∀ i : Fin m, OrientedPathFlow G (terminal i) rootRouter,
      (∀ i, (quota : Rat) ≤ (F i).value) ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.FlowsDirectToRouters
        router F ∧
      ChekuriChuzhoySection5Phase1Leaves.Vertex.AggregateVertexCongestionAtMostOne
        F := by
  let F : ∀ i : Fin m, OrientedPathFlow G (terminal i) rootRouter :=
    fun i =>
      widenFlowTarget ((R i).reverse.toOrientedPathFlow.scale c hc)
        (hrootTerminalRouter i)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    calc
      (quota : Rat) ≤ c * width := hquota
      _ = (F i).value := by
        simp [F, SynchronizedRouting.toOrientedPathFlow_value]
  · intro i a
    change
      ((R i).reverse.path a).InternallyDisjointFromSet
        (selectedUnion router)
    exact (R i).reverse_internallyDisjointFromSet (hdirect i) a
  · intro v
    let B : Rat := 1 + (Delta : Rat) * eta / 2
    have hbase :
        ∀ i : Fin m,
          (R i).reverse.toOrientedPathFlow.vertexLoad v ≤ B := by
      intro i
      exact
        OrientedPathFlow.vertexLoad_le_one_add_half_maxDegree_mul_of_edgeCongestion
          (F := (R i).reverse.toOrientedPathFlow)
          hdegree (by positivity)
          ((R i).reverse.toOrientedPathFlow_edgeCongestionAtMost
            ((R i).reverse_edgeCongestionAtMost (hcongestion i)))
          ((R i).reverse.toOrientedPathFlow_isUnitFlow
            (by simpa using hterminalCard i)
            (by simpa using hrootTerminalCard i))
          (hrootTerminalDisjoint i).symm v
    calc
      (∑ i : Fin m, (F i).vertexLoad v) =
          ∑ i : Fin m,
            c * (R i).reverse.toOrientedPathFlow.vertexLoad v := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [F]
      _ ≤ ∑ _i : Fin m, c * B := by
        exact Finset.sum_le_sum fun i _hi =>
          mul_le_mul_of_nonneg_left (hbase i) hc
      _ = (m : Rat) * c * B := by
        simp [B]
        ring
      _ ≤ 1 := by
        simpa [B] using hcapacity

/-- Paper-faithful Claim 5.14/5.15 composition.  Every chain may begin at a
different boundary subset of the common root router and ends at a boundary
subset of its selected leaf router. -/
theorem
    claim514_claim515_exists_integral_leaf_paths_of_varying_root_boundaryChains
    {m width quota Delta eta : Nat}
    {rootTerminal terminal router : Fin m → Finset V}
    {rootRouter : Finset V}
    (chain : ∀ i : Fin m,
      BoundedRoutingChain G (Fin width)
        (rootTerminal i) (terminal i) eta)
    (hrootTerminalRouter : ∀ i, rootTerminal i ⊆ rootRouter)
    (hterminalRouter : ∀ i, terminal i ⊆ router i)
    (hrootRouter : Disjoint rootRouter (selectedUnion router))
    (hrootTerminalCard : ∀ i, (rootTerminal i).card = width)
    (hterminalCard : ∀ i, (terminal i).card = width)
    (hrootTerminalDisjoint :
      ∀ i, Disjoint (rootTerminal i) (terminal i))
    (hdirect : ∀ i,
      (chain i).toRouting.InternallyDisjointFromSet
        (selectedUnion router))
    (hdegree : MaxDegreeAtMost G Delta)
    {c : Rat} (hc : 0 ≤ c)
    (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G router)
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota) rootRouter),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ k : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path k)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases claim514_scaled_leaf_flows_of_varying_root_boundaries
      (fun i => (chain i).toRouting)
      hrootTerminalRouter hrootTerminalCard hterminalCard
      hrootTerminalDisjoint hdirect hdegree
      (fun i => (chain i).bounded) hc hquota hcapacity with
    ⟨F, hvalue, hflowsDirect, haggregate⟩
  exact
    ChekuriChuzhoySection5Phase1Leaves.Vertex.claim515_exists_integral_leaf_paths_in_prunedNetwork_of_terminal_subsets
      F hterminalRouter hrootRouter hflowsDirect hquotaPos hvalue haggregate

end ChekuriChuzhoySection5Phase1Flow
end SimpleGraph

end Lax17Proofs
