import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Bundle
import Lax17Proofs.Source.ChekuriChuzhoySection5Selection

namespace Lax17Proofs

universe u v w

/-!
# Unsampled Phase 1 router bundles

The many-leaves branch of Chekuri--Chuzhoy Section 5.4.1 uses all paths in
the terminal skeleton.  Paths in one history group may overlap, but the group
has at most `n` members; paths from distinct groups are internally disjoint.
Consequently the unsampled family has edge congestion at most `n`.  Keeping
this congestion is essential for the source `m^19` loss: sampling one edge
from every group at this point would introduce one unnecessary factor `n`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RawBundle


open ChekuriChuzhoySection5EndpointThinning
open ChekuriChuzhoySection5Phase1Bundle
open ChekuriChuzhoySection5Phase1Flow
open ChekuriChuzhoySection5RouterSkeleton
open ChekuriChuzhoySection5Selection

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n Delta : Nat} {cluster : Fin n → Finset V}

namespace RouterPathSkeleton

/-- The finite type of history groups in a router skeleton. -/
abbrev GroupIndex (S : RouterPathSkeleton G cluster) :=
  {U : Finset S.graph.Edge // U ∈ S.groups.parts}

/-- The unique history group containing an abstract skeleton edge. -/
noncomputable def groupOf (S : RouterPathSkeleton G cluster)
    (e : S.graph.Edge) : S.GroupIndex := by
  classical
  exact ⟨S.groups.part e, S.groups.part_mem.mpr (by simp)⟩

theorem mem_groupOf (S : RouterPathSkeleton G cluster)
    (e : S.graph.Edge) : e ∈ (S.groupOf e).1 := by
  classical
  exact S.groups.mem_part (by simp)

theorem groupOf_eq_iff_mem (S : RouterPathSkeleton G cluster)
    (e : S.graph.Edge) (U : S.GroupIndex) :
    S.groupOf e = U ↔ e ∈ U.1 := by
  classical
  constructor
  · intro h
    rw [← h]
    exact mem_groupOf S e
  · intro he
    apply Subtype.ext
    exact S.groups.part_eq_of_mem U.2 he

theorem groupOf_fiber_card_le
    (S : RouterPathSkeleton G cluster) {k : Nat}
    (hgroups : S.GroupSizeAtMost k) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U).card ≤ k := by
  classical
  have heq :
      (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U) = U.1 := by
    ext e
    simp [S.groupOf_eq_iff_mem e U]
  rw [heq]
  exact hgroups U.1 U.2

/-- A group-label exact transversal is a native one-per-part selection. -/
theorem isGroupTransversal_of_exact
    (S : RouterPathSkeleton G cluster) {selected : Finset S.graph.Edge}
    (hselected :
      IsExactGroupTransversal Finset.univ S.groupOf selected) :
    S.IsGroupTransversal selected := by
  classical
  intro U hU
  let g : S.GroupIndex := ⟨U, hU⟩
  have hgImage :
      g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf := by
    rcases S.groups.nonempty_of_mem_parts hU with ⟨e, he⟩
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_univ e, (S.groupOf_eq_iff_mem e g).2 he⟩
  rcases hselected.existsUnique_mem_group hgImage with
    ⟨e, he, hunique⟩
  have heU : e ∈ U := (S.groupOf_eq_iff_mem e g).1 he.2
  apply Finset.card_eq_one.mpr
  refine ⟨e, Finset.Subset.antisymm ?_ ?_⟩
  · intro f hf
    have hf' := Finset.mem_inter.mp hf
    have hfg : S.groupOf f = g :=
      (S.groupOf_eq_iff_mem f g).2 hf'.2
    have hfe : f = e := hunique f ⟨hf'.1, hfg⟩
    simpa [hfe]
  · intro f hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    subst f
    exact Finset.mem_inter.mpr ⟨he.1, heU⟩

/-- Distinct history groups can be represented simultaneously in a full
one-per-group transversal. -/
theorem exists_groupTransversal_containing_pair
    (S : RouterPathSkeleton G cluster) {e f : S.graph.Edge}
    (hgroup : S.groupOf e ≠ S.groupOf f) :
    ∃ selected : Finset S.graph.Edge,
      S.IsGroupTransversal selected ∧ e ∈ selected ∧ f ∈ selected := by
  classical
  let initial : Finset S.graph.Edge := {e, f}
  have hef : e ≠ f := by
    intro hef
    exact hgroup (congrArg S.groupOf hef)
  have hinitial :
      IsPartialGroupTransversal Finset.univ S.groupOf initial := by
    refine ⟨by simp [initial], ?_⟩
    intro a ha b hb hab
    have ha' : a = e ∨ a = f := by simpa [initial] using ha
    have hb' : b = e ∨ b = f := by simpa [initial] using hb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact ha'.trans hb'.symm
    · subst a; subst b
      exact (hgroup hab).elim
    · subst a; subst b
      exact (hgroup hab.symm).elim
    · exact ha'.trans hb'.symm
  rcases hinitial.exists_exact_superset with
    ⟨selected, hselected, hinitialSubset⟩
  exact ⟨selected, isGroupTransversal_of_exact S hselected,
    hinitialSubset (by simp [initial]), hinitialSubset (by simp [initial])⟩

end RouterPathSkeleton

/-- Orient an endpoint-matched raw bundle as a synchronized routing.  No
path-disjointness premise is needed by this data structure. -/
noncomputable def rawSelectedRouting
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (selected : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected) :
    SynchronizedRouting G
      (endpointSetAt S i selected) (endpointSetAt S j selected) selected where
  path e := orientedHostPathAt S i e.1
  source_mem e := (mem_endpointSetAt S i selected _).2
    ⟨e.1, e.2, (orientedHostPathAt_source S i e.1).symm⟩
  target_mem e := (mem_endpointSetAt S j selected _).2
    ⟨e.1, e.2,
      (orientedHostPathAt_target S hij e.1 (hjoins e.1 e.2)).symm⟩
  source_injective := by
    intro a b hab
    apply Subtype.ext
    exact hinjI a.2 b.2 (by simpa using hab)
  target_injective := by
    intro a b hab
    apply Subtype.ext
    apply hinjJ a.2 b.2
    change (orientedHostPathAt S i a.1).target =
      (orientedHostPathAt S i b.1).target at hab
    rw [orientedHostPathAt_target S hij a.1 (hjoins a.1 a.2),
      orientedHostPathAt_target S hij b.1 (hjoins b.1 b.2)] at hab
    exact hab

/-- A shared host edge away from every router forces two distinct skeleton
paths into the same history group. -/
theorem groupOf_eq_of_shared_nonincident_edge
    (S : RouterPathSkeleton G cluster)
    {e f : S.graph.Edge} (hef : e ≠ f) {a : Sym2 V}
    (hea : a ∈ (S.hostPath e).edgeSet)
    (hfa : a ∈ (S.hostPath f).edgeSet)
    (hnonincident :
      ¬ RouterPathSkeleton.HostEdgeIncidentToRouters
        (cluster := cluster) a) :
    S.groupOf e = S.groupOf f := by
  classical
  by_contra hgroup
  rcases RouterPathSkeleton.exists_groupTransversal_containing_pair S hgroup with
    ⟨selected, htransversal, heSelected, hfSelected⟩
  induction a using Sym2.ind with
  | _ x y =>
      have hxE : x ∈ (S.hostPath e).vertexSet := by
        have hwalk : s(x, y) ∈ (S.hostPath e).walk.edges := by
          simpa [GraphPath.edgeSet] using hea
        simpa [GraphPath.vertexSet] using
          (S.hostPath e).walk.fst_mem_support_of_mem_edges hwalk
      have hxF : x ∈ (S.hostPath f).vertexSet := by
        have hwalk : s(x, y) ∈ (S.hostPath f).walk.edges := by
          simpa [GraphPath.edgeSet] using hfa
        simpa [GraphPath.vertexSet] using
          (S.hostPath f).walk.fst_mem_support_of_mem_edges hwalk
      have hxEndpoint := S.one_per_group_internally_node_disjoint
        selected htransversal heSelected hfSelected hef hxE hxF
      rcases hxEndpoint.1 with hxSource | hxTarget
      · exact hnonincident
          ⟨S.graph.left e, x, hxSource ▸ S.host_source_mem e, by simp⟩
      · exact hnonincident
          ⟨S.graph.right e, x, hxTarget ▸ S.host_target_mem e, by simp⟩

/-- Every raw subfamily has host-edge congestion at most the skeleton group
size (with the endpoint load `2` absorbed by `2 ≤ k`). -/
theorem rawSelectedHostEdgeUsers_card_le
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    {k : Nat} (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (selected : Finset S.graph.Edge) (a : Sym2 V)
    (haG : a ∈ G.edgeSet) :
    (routerSelectedHostEdgeUsers S selected a).card ≤ k := by
  classical
  by_cases hincident :
      RouterPathSkeleton.HostEdgeIncidentToRouters
        (cluster := cluster) a
  · exact (routerSelectedHostEdgeUsers_card_le_two
      S hload selected a haG hincident).trans hk
  · by_cases hempty : routerSelectedHostEdgeUsers S selected a = ∅
    · simp [hempty]
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hsubset :
          routerSelectedHostEdgeUsers S selected a ⊆
            Finset.univ.filter fun f : S.graph.Edge =>
              S.groupOf f = S.groupOf e := by
        intro f hf
        have hfa := (Finset.mem_filter.mp hf).2
        have hea := (Finset.mem_filter.mp he).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ f, ?_⟩
        by_cases hfe : f = e
        · simpa [hfe]
        · exact groupOf_eq_of_shared_nonincident_edge S hfe hfa hea hincident
      exact (Finset.card_le_card hsubset).trans
        (RouterPathSkeleton.groupOf_fiber_card_le S hgroups (S.groupOf e))

/-- The raw endpoint-matched bundle is a synchronized routing with the
source-faithful group-size congestion bound. -/
theorem rawSelectedRouting_edgeCongestionAtMost
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    {k : Nat} (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    {i j : Fin n} (hij : i ≠ j)
    (selected : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected) :
    (rawSelectedRouting S hij selected hjoins hinjI hinjJ).EdgeCongestionAtMost k := by
  classical
  intro a haG
  rw [SynchronizedRouting.edgeLoadNat]
  change
    (selected.attach.filter fun e =>
      a ∈ (orientedHostPathAt S i e.1).edgeSet).card ≤ k
  have heq :
      (selected.attach.filter fun e =>
        a ∈ (orientedHostPathAt S i e.1).edgeSet).card =
        (routerSelectedHostEdgeUsers S selected a).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      refine ⟨e.2, ?_⟩
      by_cases hleft : S.graph.left e.1 = i <;>
        simpa [orientedHostPathAt, hleft] using he'.2
    · intro e he f hf hef
      exact Subtype.ext hef
    · intro e he
      refine ⟨⟨e, (Finset.mem_filter.mp he).1⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach _ _, ?_⟩
      by_cases hleft : S.graph.left e = i <;>
        simpa [orientedHostPathAt, hleft] using (Finset.mem_filter.mp he).2
  rw [heq]
  exact rawSelectedHostEdgeUsers_card_le S hload hk hgroups selected a haG

/-- Raw support paths remain direct with respect to any chosen union of
router clusters. -/
theorem rawSelectedRouting_internallyDisjoint_selectedUnion
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (selected : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {m : Nat} (leafRouter : Fin m → Fin n) :
    SynchronizedRouting.InternallyDisjointFromSet
      (rawSelectedRouting S hij selected hjoins hinjI hinjJ)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))) := by
  intro e v hvPath hvSelected
  rcases ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp hvSelected with
    ⟨r, hvr⟩
  have hvHost : v ∈ (S.hostPath e.1).vertexSet := by
    by_cases hleft : S.graph.left e.1 = i <;>
      simpa [rawSelectedRouting, orientedHostPathAt, hleft] using hvPath
  have hvEndpoint : (S.hostPath e.1).IsEndpoint v :=
    S.internally_disjoint_clusters e.1 (leafRouter r) hvHost hvr
  exact (orientedHostPathAt_isEndpoint_iff_hostPath S i e.1 v).2 hvEndpoint

/-- Exact unsampled support-bundle data, including its reindexed routing. -/
structure RawExactBundle
    (S : RouterPathSkeleton G cluster) (i j : Fin n)
    (width congestion : Nat) where
  selected : Finset S.graph.Edge
  selected_card : selected.card = width
  joins : ∀ e ∈ selected, S.graph.Joins e i j
  left_injective : Set.InjOn (routerEndpointAt S i) selected
  right_injective : Set.InjOn (routerEndpointAt S j) selected
  routing : SynchronizedRouting G
    (endpointSetAt S i selected) (endpointSetAt S j selected) (Fin width)
  routing_congestion : routing.EdgeCongestionAtMost congestion
  routing_direct : ∀ {m : Nat} (leafRouter : Fin m → Fin n),
    routing.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
        (fun r => cluster (leafRouter r)))

/-- Produce an exact raw bundle directly from one large router-pair bundle.
No group-size factor occurs in the cardinality premise. -/
theorem exists_rawExactBundle
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    {k : Nat} (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (candidate : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ candidate, S.graph.Joins e i j)
    {width : Nat} (hlarge : 4 * Delta * width ≤ candidate.card) :
    Nonempty (RawExactBundle S i j width k) := by
  classical
  rcases exists_routerBundle_exact_endpoint_matching
      S hload hdegree hDelta hij hclusterDisjoint candidate hjoins hlarge with
    ⟨selected, hselected, hcard, hinjI, hinjJ, _hmemI, _hmemJ⟩
  let R₀ := rawSelectedRouting S hij selected
    (fun e he => hjoins e (hselected he)) hinjI hinjJ
  have hR₀congestion : R₀.EdgeCongestionAtMost k :=
    rawSelectedRouting_edgeCongestionAtMost S hload hk hgroups hij selected
      (fun e he => hjoins e (hselected he)) hinjI hinjJ
  have hIndexCard : Fintype.card selected = width := by
    simpa using hcard
  let equiv : Fin width ≃ selected :=
    (Fintype.equivFinOfCardEq hIndexCard).symm
  let R := R₀.reindex equiv
  refine ⟨{
    selected := selected
    selected_card := hcard
    joins := fun e he => hjoins e (hselected he)
    left_injective := hinjI
    right_injective := hinjJ
    routing := R
    routing_congestion :=
      SynchronizedRouting.reindex_edgeCongestionAtMost R₀ equiv hR₀congestion
    routing_direct := ?_ }⟩
  intro m leafRouter e
  exact rawSelectedRouting_internallyDisjoint_selectedUnion
    S hij selected (fun a ha => hjoins a (hselected ha)) hinjI hinjJ
      leafRouter (equiv e)

/-! ## Raw root-to-leaf prefix recursion -/

/-- Start a direct root-to-leaf prefix with an unsampled support bundle. -/
theorem exists_rawDirectSelectedSupportPrefix
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    {k width m : Nat} (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (hlarge : 4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n) :
    Nonempty
      (DirectSelectedSupportPrefix S (cluster i)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        i j width k) := by
  rcases exists_rawExactBundle S hload hdegree hDelta hk hgroups hij
      hclusterDisjoint (S.edgeBundle i j)
      (fun e he => S.mem_edgeBundle.mp he) hlarge with
    ⟨D⟩
  have hsourceSubset : endpointSetAt S i D.selected ⊆ cluster i := by
    intro v hv
    rcases (mem_endpointSetAt S i D.selected v).mp hv with ⟨e, he, rfl⟩
    exact (routerEndpointAt_mem_cluster_of_joins S hij e (D.joins e he)).1
  have hsourceInterface :
      endpointSetAt S i D.selected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hij hclusterDisjoint D.selected D.joins
  exact ⟨{
    sourceBoundary := endpointSetAt S i D.selected
    sourceBoundary_subset_root := hsourceSubset
    sourceBoundary_subset_interfaceRoot := hsourceInterface
    sourceBoundary_card :=
      (endpointSetAt_card S i D.selected D.left_injective).trans
        D.selected_card
    previous_ne_current := hij
    incomingSelected := D.selected
    incomingJoins := D.joins
    incomingInjCurrent := D.right_injective
    incomingCard := D.selected_card
    routing := DirectBoundedRoutingChain.single D.routing
      D.routing_congestion (D.routing_direct leafRouter) }⟩

/-- Extend a raw prefix through one bandwidth router and one further
unsampled support bundle. -/
theorem exists_rawDirectSelectedSupportPrefix_snoc
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    {k width cap routerDen eta m : Nat}
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    {rootRouter : Finset V} {p i j : Fin n}
    (hpi : p ≠ i) (hij : i ≠ j)
    (hclusterPI : Disjoint (cluster p) (cluster i))
    (hclusterIJ : Disjoint (cluster i) (cluster j))
    (hlarge : 4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (prior :
      DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        p i width eta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate :
      Disjoint (cluster i)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))) :
    Nonempty
      (DirectSelectedSupportPrefix S rootRouter
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r)))
        i j width (eta + routerDen + k)) := by
  rcases exists_rawExactBundle S hload hdegree hDelta hk hgroups hij
      hclusterIJ (S.edgeBundle i j)
      (fun e he => S.mem_edgeBundle.mp he) hlarge with
    ⟨D⟩
  have hincomingInterface :
      endpointSetAt S i prior.incomingSelected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hpi.symm hclusterPI.symm prior.incomingSelected
        (fun e he => (S.graph.joins_comm e p i).mp
          (prior.incomingJoins e he))
  have houtgoingInterface :
      endpointSetAt S i D.selected ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i) :=
    endpointSetAt_subset_interfaceVertices
      S hij hclusterIJ D.selected D.joins
  have hincomingCard :
      (endpointSetAt S i prior.incomingSelected).card = width :=
    (endpointSetAt_card S i prior.incomingSelected
      prior.incomingInjCurrent).trans prior.incomingCard
  have houtgoingCard :
      (endpointSetAt S i D.selected).card = width :=
    (endpointSetAt_card S i D.selected D.left_injective).trans
      D.selected_card
  have hendpointCap :
      (endpointSetAt S i prior.incomingSelected ∪
        endpointSetAt S i D.selected).card ≤ cap := by
    calc
      _ ≤ (endpointSetAt S i prior.incomingSelected).card +
          (endpointSetAt S i D.selected).card := Finset.card_union_le _ _
      _ = 2 * width := by rw [hincomingCard, houtgoingCard]; omega
      _ ≤ cap := hcap
  rcases exists_directBoundedRoutingChain_snoc_router
      prior.routing D.routing D.routing_congestion
      (D.routing_direct leafRouter) hband hincomingInterface
      houtgoingInterface hendpointCap hincomingCard houtgoingCard
      hintermediate with ⟨routing⟩
  exact ⟨{
    sourceBoundary := prior.sourceBoundary
    sourceBoundary_subset_root := prior.sourceBoundary_subset_root
    sourceBoundary_subset_interfaceRoot :=
      prior.sourceBoundary_subset_interfaceRoot
    sourceBoundary_card := prior.sourceBoundary_card
    previous_ne_current := hij
    incomingSelected := D.selected
    incomingJoins := D.joins
    incomingInjCurrent := D.right_injective
    incomingCard := D.selected_card
    routing := routing }⟩

/-- Realize an injective support-tree order with unsampled bundles.  Every
support segment contributes congestion `k`; no factor `k` is lost from its
cardinality before the flow is formed. -/
theorem exists_rawDirectSelectedSupportPrefix_of_injective_order
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta k width cap routerDen m steps : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (order : Fin (steps + 2) → Fin n)
    (hinjective : Function.Injective order)
    (hadj : ∀ r : Fin (steps + 1),
      T.Adj (order ⟨r.1, by omega⟩)
        (order ⟨r.1 + 1, by omega⟩))
    (hclusterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (cluster i) (cluster j))
    (hband : ∀ r : Fin steps,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster (order ⟨r.1 + 1, by omega⟩)) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate : ∀ r : Fin steps,
      Disjoint (cluster (order ⟨r.1 + 1, by omega⟩))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))) :
    Nonempty
      (DirectSelectedSupportPrefix S
        (cluster (order ⟨0, by omega⟩))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (order ⟨steps, by omega⟩) (order ⟨steps + 1, by omega⟩)
        width (k + steps * (routerDen + k))) := by
  induction steps with
  | zero =>
      have hne : order ⟨0, by omega⟩ ≠ order ⟨1, by omega⟩ :=
        hinjective.ne (by simp)
      simpa using exists_rawDirectSelectedSupportPrefix
        S hload hdegree hDelta hk hgroups hne (hclusterDisjoint hne)
        (hbundle _ _ (hadj ⟨0, by omega⟩)) leafRouter
  | succ steps ih =>
      let shorter : Fin (steps + 2) → Fin n :=
        fun r => order ⟨r.1, by omega⟩
      have hshorterInjective : Function.Injective shorter := by
        intro a b hab
        apply Fin.ext
        have hcast := congrArg Fin.val
          (hinjective hab :
            (⟨a.1, by omega⟩ : Fin (steps + 3)) =
              ⟨b.1, by omega⟩)
        simpa using hcast
      have hshorterAdj : ∀ r : Fin (steps + 1),
          T.Adj (shorter ⟨r.1, by omega⟩)
            (shorter ⟨r.1 + 1, by omega⟩) := by
        intro r
        exact hadj ⟨r.1, by omega⟩
      have hshorterBand : ∀ r : Fin steps,
          ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
            G (cluster (shorter ⟨r.1 + 1, by omega⟩)) cap 1 routerDen := by
        intro r
        exact hband ⟨r.1, by omega⟩
      have hshorterIntermediate : ∀ r : Fin steps,
          Disjoint (cluster (shorter ⟨r.1 + 1, by omega⟩))
            (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
              (fun s => cluster (leafRouter s))) := by
        intro r
        exact hintermediate ⟨r.1, by omega⟩
      rcases ih shorter hshorterInjective hshorterAdj
          hshorterBand hshorterIntermediate with ⟨prior⟩
      have hpi : shorter ⟨steps, by omega⟩ ≠
          shorter ⟨steps + 1, by omega⟩ :=
        hshorterInjective.ne (by simp)
      have hij : order ⟨steps + 1, by omega⟩ ≠
          order ⟨steps + 2, by omega⟩ :=
        hinjective.ne (by simp)
      rcases exists_rawDirectSelectedSupportPrefix_snoc
          S hload hdegree hDelta hk hgroups hpi hij
          (hclusterDisjoint hpi) (hclusterDisjoint hij)
          (hbundle _ _ (hadj ⟨steps + 1, by omega⟩)) leafRouter prior
          (hband ⟨steps, by omega⟩) hcap
          (hintermediate ⟨steps, by omega⟩) with ⟨result⟩
      have hresult : Nonempty
          (DirectSelectedSupportPrefix S
            (cluster (shorter ⟨0, by omega⟩))
            (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
              (fun s => cluster (leafRouter s)))
            (shorter ⟨steps + 1, by omega⟩)
            (order ⟨steps + 2, by omega⟩) width
            ((k + steps * (routerDen + k)) + routerDen + k)) := ⟨result⟩
      have heta :
          (k + steps * (routerDen + k)) + routerDen + k =
            k + (steps + 1) * (routerDen + k) := by
        simp only [Nat.add_mul, one_mul]
        omega
      rw [heta] at hresult
      simpa [shorter] using hresult

/-- Uniform-budget raw realization of an explicit support-graph path. -/
theorem exists_rawDirectSelectedSupportPrefix_of_graphPath_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n))
    {Delta k width cap routerDen m steps eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (P : GraphPath T) (hlength : P.walk.length = steps + 1)
    (hclusterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (cluster i) (cluster j))
    (hband : ∀ r : Fin steps,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster (P.walk.getVert (r.1 + 1))) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (hintermediate : ∀ r : Fin steps,
      Disjoint (cluster (P.walk.getVert (r.1 + 1)))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s))))
    (heta : k + steps * (routerDen + k) ≤ eta) :
    ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster P.source)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous P.target width eta) := by
  let order : Fin (steps + 2) → Fin n := fun r => P.walk.getVert r.1
  have hinjective : Function.Injective order := by
    intro a b hab
    apply Fin.ext
    exact P.isPath.getVert_injOn
      (by simp; omega) (by simp; omega) hab
  have hadj : ∀ r : Fin (steps + 1),
      T.Adj (order ⟨r.1, by omega⟩)
        (order ⟨r.1 + 1, by omega⟩) := by
    intro r
    apply P.walk.adj_getVert_succ
    rw [hlength]
    exact r.isLt
  rcases exists_rawDirectSelectedSupportPrefix_of_injective_order
      S T hload hdegree hDelta hk hgroups hbundle leafRouter order
      hinjective hadj hclusterDisjoint (fun r => hband r) hcap
      (fun r => hintermediate r) with ⟨routePrefix⟩
  let widened := routePrefix.weaken heta
  refine ⟨order ⟨steps, by omega⟩, ?_⟩
  have hsource : order ⟨0, by omega⟩ = P.source := by simp [order]
  have htarget : order ⟨steps + 1, by omega⟩ = P.target := by
    change P.walk.getVert (steps + 1) = P.target
    rw [← hlength]
    exact P.walk.getVert_length
  rw [hsource, htarget] at widened
  exact ⟨widened⟩

/-- Raw realization of the canonical path from a root to one selected
degree-one leaf. -/
theorem exists_rawDirectSelectedSupportPrefix_of_supportTreePath_leafFamily_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    {Delta k width cap routerDen m eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n) (r : Fin m) (hrootLeaf : root ≠ leafRouter r)
    (hclusterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (cluster i) (cluster j))
    (hband : ∀ i : Fin n,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      k + (T.dist root (leafRouter r) - 1) * (routerDen + k) ≤ eta) :
    ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous (leafRouter r) width eta) := by
  let P := supportTreePath T hT root (leafRouter r)
  have hintermediate : ∀ a : Fin (T.dist root (leafRouter r) - 1),
      Disjoint (cluster (P.walk.getVert (a.1 + 1)))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s))) := by
    intro a
    have hnotLeaf : ∀ s : Fin m,
        P.walk.getVert (a.1 + 1) ≠ leafRouter s := by
      intro s heq
      apply graphPath_internal_vertex_not_degreeEquals_one P (a := a.1)
      · rw [supportTreePath_length]
        omega
      · rw [heq]
        exact hleaf s
    rw [Finset.disjoint_left]
    intro v hvInternal hvSelected
    rcases ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp
        hvSelected with ⟨s, hvLeaf⟩
    exact Finset.disjoint_left.mp (hclusterDisjoint (hnotLeaf s))
      hvInternal hvLeaf
  have hdistPos : 0 < T.dist root (leafRouter r) :=
    hT.connected.pos_dist_of_ne hrootLeaf
  have hlength : P.walk.length =
      (T.dist root (leafRouter r) - 1) + 1 := by
    rw [supportTreePath_length]
    omega
  simpa [P] using exists_rawDirectSelectedSupportPrefix_of_graphPath_bounded
    S T hload hdegree hDelta hk hgroups hbundle leafRouter P hlength
    hclusterDisjoint (fun a => hband _) hcap hintermediate heta

/-- Simultaneously choose the raw canonical prefix to every selected leaf. -/
theorem exists_rawDirectSelectedSupportPrefixFamily_of_leafFamily_bounded
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    {Delta k width cap routerDen m eta : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n) (hrootLeaf : ∀ r, root ≠ leafRouter r)
    (hclusterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (cluster i) (cluster j))
    (hband : ∀ i : Fin n,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta : ∀ r,
      k + (T.dist root (leafRouter r) - 1) * (routerDen + k) ≤ eta) :
    ∃ previous : Fin m → Fin n,
      Nonempty (∀ r : Fin m,
        DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          (previous r) (leafRouter r) width eta) := by
  classical
  have hpointwise : ∀ r : Fin m, ∃ previous : Fin n,
      Nonempty
        (DirectSelectedSupportPrefix S (cluster root)
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
            (fun s => cluster (leafRouter s)))
          previous (leafRouter r) width eta) := by
    intro r
    exact exists_rawDirectSelectedSupportPrefix_of_supportTreePath_leafFamily_bounded
      S T hT hload hdegree hDelta hk hgroups hbundle leafRouter hleaf root r
      (hrootLeaf r) hclusterDisjoint hband hcap (heta r)
  let previous : Fin m → Fin n := fun r => Classical.choose (hpointwise r)
  let family : ∀ r : Fin m,
      DirectSelectedSupportPrefix S (cluster root)
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun s => cluster (leafRouter s)))
        (previous r) (leafRouter r) width eta :=
    fun r => Classical.choice (Classical.choose_spec (hpointwise r))
  exact ⟨previous, ⟨family⟩⟩

/-- Source-faithful Claims 5.14/5.15 from the unsampled support skeleton,
with the common root target restricted to the root-router interface. -/
theorem claim514_claim515_of_rawSupportTree_leafFamily_interfaceRoot
    (S : RouterPathSkeleton G cluster)
    (T : _root_.SimpleGraph (Fin n)) (hT : T.IsTree)
    {Delta k width cap routerDen m eta quota : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 0 < Delta)
    (hk : 2 ≤ k) (hgroups : S.GroupSizeAtMost k)
    (hbundle : ∀ i j, T.Adj i j →
      4 * Delta * width ≤ (S.edgeBundle i j).card)
    (leafRouter : Fin m → Fin n)
    (hleaf : ∀ r, DegreeEquals T (leafRouter r) 1)
    (root : Fin n) (hrootLeaf : ∀ r, root ≠ leafRouter r)
    (hclusterDisjoint : ∀ ⦃i j : Fin n⦄, i ≠ j →
      Disjoint (cluster i) (cluster j))
    (hband : ∀ i : Fin n,
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G (cluster i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta : ∀ r,
      k + (T.dist root (leafRouter r) - 1) * (routerDen + k) ≤ eta)
    {c : Rat} (hc : 0 ≤ c) (hquotaPos : 0 < quota)
    (hquota : (quota : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1) :
    ∃ P : PathPacking
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.graph
          (q := quota) G (fun r => cluster (leafRouter r)))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota))
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.oldImage
          (m := m) (q := quota)
          (ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster root))),
      P.card = m * quota ∧
      P.sourceSet =
        ChekuriChuzhoySection5Phase1Leaves.Vertex.sources
          (V := V) (m := m) (q := quota) ∧
      ∀ a : P.Index,
        (ChekuriChuzhoySection5Phase1Leaves.Vertex.GraphPath.dropFirst
          (P.orient.path a)).vertexSet ⊆
          ChekuriChuzhoySection5Phase1Leaves.Vertex.oldRegion
            (V := V) (m := m) (q := quota) := by
  rcases exists_rawDirectSelectedSupportPrefixFamily_of_leafFamily_bounded
      S T hT hload hdegree hDelta hk hgroups hbundle leafRouter hleaf root
      hrootLeaf hclusterDisjoint hband hcap heta with ⟨previous, ⟨family⟩⟩
  have hrootInterfaceDisjoint :
      Disjoint
        (ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster root))
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion
          (fun r => cluster (leafRouter r))) := by
    rw [Finset.disjoint_left]
    intro v hvRoot hvSelected
    rcases ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp
        hvSelected with ⟨r, hvLeaf⟩
    exact Finset.disjoint_left.mp (hclusterDisjoint (hrootLeaf r))
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G (cluster root) hvRoot) hvLeaf
  exact claim514_claim515_of_directSelectedSupportPrefixes_to_rootTarget
    S family (fun r => (family r).sourceBoundary_subset_interfaceRoot)
    hrootInterfaceDisjoint hdegree hc hquotaPos hquota hcapacity

end ChekuriChuzhoySection5RawBundle
end SimpleGraph

end Lax17Proofs
