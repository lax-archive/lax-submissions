import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma78
import Lax17Proofs.Source.ChekuriChuzhoySection5EndpointThinning
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Flow

namespace Lax17Proofs

universe u v w

/-!
# Endpoint thinning for Appendix A.3

An edge-disjoint path family in a graph of maximum degree `Delta` uses any
fixed endpoint at most `Delta` times.  The generic named-edge matching lemma
then extracts a subfamily with distinct endpoints on both sides.
-/

namespace SimpleGraph
namespace AppendixA3EndpointMatching


open Finset
open ChekuriChuzhoySection5Phase1Flow
open ChekuriChuzhoySection5EndpointThinning

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

private theorem endpointFiber_card_le_degree
    {S T : Finset V} {Delta : ℕ}
    (P : EdgePathPacking G S T)
    (hdisjoint : Disjoint S T)
    (hdegree : MaxDegreeAtMost G Delta)
    (endpoint : P.Index → V)
    (hendpoint :
      ∀ i, endpoint i =
        ((P.path i).orient (P.connects i)).source ∨
        endpoint i =
          ((P.path i).orient (P.connects i)).target)
    (v : V) :
    ((Finset.univ : Finset P.Index).filter fun i => endpoint i = v).card ≤
      Delta := by
  classical
  let I :=
    (Finset.univ : Finset P.Index).filter fun i => endpoint i = v
  have hnontrivial (i : P.Index) :
      ((P.path i).orient (P.connects i)).source ≠
        ((P.path i).orient (P.connects i)).target := by
    intro heq
    have hs :=
      GraphPath.orient_source_mem (P.path i) (P.connects i)
    have ht :=
      GraphPath.orient_target_mem (P.path i) (P.connects i)
    exact Finset.disjoint_left.mp hdisjoint hs (heq ▸ ht)
  have hexists (i : {i : P.Index // i ∈ I}) :
      ∃ e : Sym2 V,
        e ∈ (P.path i.1).edgeSet ∧
          e ∈ incidentEdgeFinset G v := by
    let O := (P.path i.1).orient (P.connects i.1)
    have hiEndpoint : endpoint i.1 = v :=
      (Finset.mem_filter.mp i.2).2
    rcases hendpoint i.1 with hsource | htarget
    · have hvO : v = O.source := by
        simpa [O] using hiEndpoint.symm.trans hsource
      have hvVertex : v ∈ O.vertexSet := by
        rw [hvO]
        exact GraphPath.source_mem_vertexSet O
      obtain ⟨e, heO, hve⟩ :=
        O.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          (hnontrivial i.1) hvVertex
      refine ⟨e, ?_, ?_⟩
      · simpa [O, GraphPath.orient_edgeSet] using heO
      · apply (mem_incidentEdgeFinset G v e).2
        refine ⟨?_, hve⟩
        exact (P.path i.1).edgeSet_subset_edgeSet
          (by simpa [O, GraphPath.orient_edgeSet] using heO)
    · have hvO : v = O.target := by
        simpa [O] using hiEndpoint.symm.trans htarget
      have hvVertex : v ∈ O.vertexSet := by
        rw [hvO]
        exact GraphPath.target_mem_vertexSet O
      obtain ⟨e, heO, hve⟩ :=
        O.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          (hnontrivial i.1) hvVertex
      refine ⟨e, ?_, ?_⟩
      · simpa [O, GraphPath.orient_edgeSet] using heO
      · apply (mem_incidentEdgeFinset G v e).2
        refine ⟨?_, hve⟩
        exact (P.path i.1).edgeSet_subset_edgeSet
          (by simpa [O, GraphPath.orient_edgeSet] using heO)
  let chosen : {i : P.Index // i ∈ I} → Sym2 V :=
    fun i => Classical.choose (hexists i)
  have hchosenPath (i : {i : P.Index // i ∈ I}) :
      chosen i ∈ (P.path i.1).edgeSet :=
    (Classical.choose_spec (hexists i)).1
  have hchosenIncident (i : {i : P.Index // i ∈ I}) :
      chosen i ∈ incidentEdgeFinset G v :=
    (Classical.choose_spec (hexists i)).2
  let toIncident :
      {i : P.Index // i ∈ I} →
        {e : Sym2 V // e ∈ incidentEdgeFinset G v} :=
    fun i => ⟨chosen i, hchosenIncident i⟩
  have hinjective : Function.Injective toIncident := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hedge : chosen i = chosen j :=
      congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (P.edge_disjoint hne)
      (hchosenPath i) (by simpa [hedge] using hchosenPath j)
  have hcard :=
    Fintype.card_le_of_injective toIncident hinjective
  calc
    ((Finset.univ : Finset P.Index).filter fun i => endpoint i = v).card =
        Fintype.card {i : P.Index // i ∈ I} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card
        {e : Sym2 V // e ∈ incidentEdgeFinset G v} := hcard
    _ = (incidentEdgeFinset G v).card := Fintype.card_coe _
    _ ≤ Delta := incidentEdgeFinset_card_le_maxDegree (G := G) hdegree v

/-- Source endpoint multiplicity in an edge-disjoint packing. -/
theorem sourceFiber_card_le_degree
    {S T : Finset V} {Delta : ℕ}
    (P : EdgePathPacking G S T)
    (hdisjoint : Disjoint S T)
    (hdegree : MaxDegreeAtMost G Delta)
    (v : V) :
    ((Finset.univ : Finset P.Index).filter fun i =>
      ((P.path i).orient (P.connects i)).source = v).card ≤ Delta :=
  endpointFiber_card_le_degree P hdisjoint hdegree
    (fun i => ((P.path i).orient (P.connects i)).source)
    (fun _ => Or.inl rfl) v

/-- Target endpoint multiplicity in an edge-disjoint packing. -/
theorem targetFiber_card_le_degree
    {S T : Finset V} {Delta : ℕ}
    (P : EdgePathPacking G S T)
    (hdisjoint : Disjoint S T)
    (hdegree : MaxDegreeAtMost G Delta)
    (v : V) :
    ((Finset.univ : Finset P.Index).filter fun i =>
      ((P.path i).orient (P.connects i)).target = v).card ≤ Delta :=
  endpointFiber_card_le_degree P hdisjoint hdegree
    (fun i => ((P.path i).orient (P.connects i)).target)
    (fun _ => Or.inr rfl) v

/-- Convert an endpoint-matching subfamily to a synchronized routing on its
actual endpoint sets. -/
noncomputable def toSynchronizedRouting
    {S T : Finset V}
    (P : EdgePathPacking G S T)
    (I : Finset P.Index)
    (hsource : Set.InjOn
      (fun i => ((P.path i).orient (P.connects i)).source) I)
    (htarget : Set.InjOn
      (fun i => ((P.path i).orient (P.connects i)).target) I) :
    let sourceSet :=
      I.image fun i => ((P.path i).orient (P.connects i)).source
    let targetSet :=
      I.image fun i => ((P.path i).orient (P.connects i)).target
    SynchronizedRouting G sourceSet targetSet {i : P.Index // i ∈ I} := by
  let sourceSet :=
    I.image fun i => ((P.path i).orient (P.connects i)).source
  let targetSet :=
    I.image fun i => ((P.path i).orient (P.connects i)).target
  exact
    { path := fun i => (P.path i.1).orient (P.connects i.1)
      source_mem := fun i =>
        Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
      target_mem := fun i =>
        Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
      source_injective := by
        intro i j hij
        apply Subtype.ext
        exact hsource i.2 j.2 hij
      target_injective := by
        intro i j hij
        apply Subtype.ext
        exact htarget i.2 j.2 hij }

/-- The synchronized routing inherited from an edge-disjoint packing has
edge congestion one. -/
theorem toSynchronizedRouting_edgeCongestionAtMost_one
    {S T : Finset V}
    (P : EdgePathPacking G S T)
    (I : Finset P.Index)
    (hsource : Set.InjOn
      (fun i => ((P.path i).orient (P.connects i)).source) I)
    (htarget : Set.InjOn
      (fun i => ((P.path i).orient (P.connects i)).target) I) :
    (toSynchronizedRouting P I hsource htarget).EdgeCongestionAtMost 1 := by
  classical
  intro e heG
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply Subtype.ext
  by_contra hne
  have hie :
      e ∈ (P.path i.1).edgeSet := by
    simpa [SynchronizedRouting.edgeLoadNat, toSynchronizedRouting,
      GraphPath.orient_edgeSet] using (Finset.mem_filter.mp hi).2
  have hje :
      e ∈ (P.path j.1).edgeSet := by
    simpa [SynchronizedRouting.edgeLoadNat, toSynchronizedRouting,
      GraphPath.orient_edgeSet] using (Finset.mem_filter.mp hj).2
  exact Finset.disjoint_left.mp (P.edge_disjoint hne) hie hje

/-- Degree-bounded endpoint thinning to any requested exact width. -/
theorem exists_synchronizedRouting_of_edgePathPacking
    {S T : Finset V} {Delta width : ℕ}
    (P : EdgePathPacking G S T)
    (hdisjoint : Disjoint S T)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (hwidth : 2 * Delta * width ≤ P.card) :
    ∃ (S' T' : Finset V) (I : Finset P.Index)
      (hsource : Set.InjOn
        (fun i => ((P.path i).orient (P.connects i)).source) I)
      (htarget : Set.InjOn
        (fun i => ((P.path i).orient (P.connects i)).target) I),
      I.card = width ∧
      S' ⊆ S ∧ T' ⊆ T ∧
      S' = I.image
        (fun i => ((P.path i).orient (P.connects i)).source) ∧
      T' = I.image
        (fun i => ((P.path i).orient (P.connects i)).target) ∧
      (toSynchronizedRouting P I hsource htarget).EdgeCongestionAtMost 1 := by
  classical
  let source := fun i : P.Index =>
    ((P.path i).orient (P.connects i)).source
  let target := fun i : P.Index =>
    ((P.path i).orient (P.connects i)).target
  obtain ⟨matching, hmatching, hsource, htarget, hcard⟩ :=
    exists_boundedDegreeBipartiteMatching
      (Finset.univ : Finset P.Index) source target Delta
      (by
        intro v
        simpa [source] using
          sourceFiber_card_le_degree P hdisjoint hdegree v)
      (by
        intro v
        simpa [target] using
          targetFiber_card_le_degree P hdisjoint hdegree v)
  have hmatchingWidth : width ≤ matching.card := by
    have hPcard : P.card ≤ 2 * Delta * matching.card := by
      simpa [EdgePathPacking.card] using hcard
    exact Nat.le_of_mul_le_mul_left
      (hwidth.trans hPcard) (Nat.mul_pos (by decide) hDelta)
  obtain ⟨I, hImatching, hIcard⟩ :=
    Finset.exists_subset_card_eq hmatchingWidth
  have hsourceI : Set.InjOn source I :=
    hsource.mono hImatching
  have htargetI : Set.InjOn target I :=
    htarget.mono hImatching
  let S' := I.image source
  let T' := I.image target
  refine ⟨S', T', I, hsourceI, htargetI, hIcard, ?_, ?_, rfl, rfl, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact GraphPath.orient_source_mem (P.path i) (P.connects i)
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact GraphPath.orient_target_mem (P.path i) (P.connects i)
  · exact toSynchronizedRouting_edgeCongestionAtMost_one
      P I hsourceI htargetI

/-! ## Perfect packings as synchronized routings -/

/-- Forget the node-disjointness of a perfect packing while retaining its
oriented endpoint bijections as a synchronized routing. -/
noncomputable def synchronizedRoutingOfPerfect
    {S T : Finset V} (P : PerfectPathPacking G S T) :
    SynchronizedRouting G S T P.Index where
  path := P.path
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_injective := fun _ _ h =>
    P.source_bijective.1 (Subtype.ext h)
  target_injective := fun _ _ h =>
    P.target_bijective.1 (Subtype.ext h)

/-- Node-disjoint paths have integral edge congestion at most one. -/
theorem synchronizedRoutingOfPerfect_edgeCongestionAtMost_one
    {S T : Finset V} (P : PerfectPathPacking G S T) :
    (synchronizedRoutingOfPerfect P).EdgeCongestionAtMost 1 := by
  classical
  intro e heG
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  have hie : e ∈ (P.path i).edgeSet := by
    simpa [SynchronizedRouting.edgeLoadNat,
      synchronizedRoutingOfPerfect] using (Finset.mem_filter.mp hi).2
  have hje : e ∈ (P.path j).edgeSet := by
    simpa [SynchronizedRouting.edgeLoadNat,
      synchronizedRoutingOfPerfect] using (Finset.mem_filter.mp hj).2
  exact Finset.disjoint_left.mp
    (GraphPath.edgeDisjoint_of_nodeDisjoint
      (P.toPathPacking.node_disjoint hne)) hie hje

/-- If every source is used, the injective source map of a synchronized
routing is an equivalence with the source finset. -/
noncomputable def SynchronizedRouting.sourceEquivOfCard
    {S T : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G S T ι)
    (hcard : S.card = Fintype.card ι) :
    ι ≃ {v : V // v ∈ S} := by
  apply Equiv.ofBijective
    (fun i => ⟨(R.path i).source, R.source_mem i⟩)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    exact R.source_injective (congrArg Subtype.val hij)
  · rw [Fintype.card_coe, hcard]

/-- The analogous equivalence for the target map. -/
noncomputable def SynchronizedRouting.targetEquivOfCard
    {S T : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G S T ι)
    (hcard : T.card = Fintype.card ι) :
    ι ≃ {v : V // v ∈ T} := by
  apply Equiv.ofBijective
    (fun i => ⟨(R.path i).target, R.target_mem i⟩)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    exact R.target_injective (congrArg Subtype.val hij)
  · rw [Fintype.card_coe, hcard]

/-- Restrict every path of a synchronized routing to the same-vertex graph
induced by a region containing all of its path vertices. -/
noncomputable def synchronizedRoutingInInducedOnFinset
    {S T C : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G S T ι)
    (hstay : ∀ i, (R.path i).vertexSet ⊆ C) :
    SynchronizedRouting (inducedOnFinset G C) S T ι where
  path := fun i => (R.path i).inInducedOnFinset (hstay i)
  source_mem := R.source_mem
  target_mem := R.target_mem
  source_injective := R.source_injective
  target_injective := R.target_injective

@[simp] theorem synchronizedRoutingInInducedOnFinset_path_vertexSet
    {S T C : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G S T ι)
    (hstay : ∀ i, (R.path i).vertexSet ⊆ C) (i : ι) :
    ((synchronizedRoutingInInducedOnFinset R hstay).path i).vertexSet =
      (R.path i).vertexSet := by
  simp [synchronizedRoutingInInducedOnFinset]

/-- Passing a synchronized routing to an induced graph preserves its edge
congestion bound. -/
theorem synchronizedRoutingInInducedOnFinset_edgeCongestionAtMost
    {S T C : Finset V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : SynchronizedRouting G S T ι)
    (hstay : ∀ i, (R.path i).vertexSet ⊆ C)
    {eta : ℕ} (hcongestion : R.EdgeCongestionAtMost eta) :
    (synchronizedRoutingInInducedOnFinset R hstay).EdgeCongestionAtMost eta := by
  classical
  intro e he
  have heG : e ∈ G.edgeSet :=
    _root_.SimpleGraph.edgeSet_mono inducedOnFinset_le he
  simpa only [SynchronizedRouting.edgeLoadNat,
    synchronizedRoutingInInducedOnFinset,
    GraphPath.inInducedOnFinset_edgeSet] using
      hcongestion e heG

end
end AppendixA3EndpointMatching
end SimpleGraph

end Lax17Proofs
