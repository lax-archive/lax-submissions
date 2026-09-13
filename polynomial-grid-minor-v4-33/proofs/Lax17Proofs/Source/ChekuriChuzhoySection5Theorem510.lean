import Lax17Proofs.Source.ChekuriChuzhoySection5HostSkeleton

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy journal Theorem 5.10

This file assembles the realized Hind--Oellermann reduction, grouped Mader
elimination, contraction-fiber lifting, and cycle erasure.  The result is the
full semantic terminal-skeleton theorem; only the source's algorithmic
running-time assertion is omitted.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {terminals : Finset V} {mu : Nat}

namespace FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore

variable [Fintype G.edgeSet]
variable
  (C : (hostEdgeIndexedGraph G).RealizedGroupedTerminalCore terminals mu)

/-- The final grouped core, interpreted as paths in the original host graph. -/
noncomputable def terminalPathSkeleton :
    TerminalPathSkeleton G terminals where
  graph := C.terminalGraph
  hostPath := fun e => (C.liftedNamedWalk e).toHostPath G
  host_source := by
    intro e
    exact NamedEdgeWalk.toHostPath_source G (C.liftedNamedWalk e)
  host_target := by
    intro e
    exact NamedEdgeWalk.toHostPath_target G (C.liftedNamedWalk e)
  groups :=
    SimpleGraph.ChekuriChuzhoySection5LabelPartition.partition
      C.core.grouped.label

@[simp] theorem terminalPathSkeleton_graph :
    C.terminalPathSkeleton.graph = C.terminalGraph :=
  rfl

@[simp] theorem terminalPathSkeleton_hostPath
    (e : C.core.graph.Edge) :
    C.terminalPathSkeleton.hostPath e =
      (C.liftedNamedWalk e).toHostPath G :=
  rfl

theorem terminalPathSkeleton_vertex_classification
    (e : C.core.graph.Edge) {v : V}
    (hv : v ∈ (C.terminalPathSkeleton.hostPath e).vertexSet) :
    v = (C.terminalGraph.left e).1 ∨
      v = (C.terminalGraph.right e).1 ∨
      ∃ s, C.core.grouped.label e = Sum.inr s ∧
        v ∈ C.reduction.fiber s := by
  apply C.liftedNamedWalk_vertex_classification e
  exact NamedEdgeWalk.toHostPath_vertexSet_subset G
    (C.liftedNamedWalk e) hv

theorem terminalPathSkeleton_edgeConnected :
    C.terminalPathSkeleton.TerminalEdgeConnected (2 * mu) :=
  C.quantitative.terminalGraph_edgeConnected

theorem terminalPathSkeleton_groupSize :
    C.terminalPathSkeleton.GroupSizeAtMost terminals.card := by
  intro U hU
  apply
    SimpleGraph.ChekuriChuzhoySection5LabelPartition.part_card_le_of_fiber_card_le
      (label := C.core.grouped.label) (bound := terminals.card)
      (U := U) ?_ hU
  intro key hkey
  exact C.label_fiber_card_le key

theorem terminalPathSkeleton_terminalDegree :
    C.terminalPathSkeleton.TerminalDegreeCongestionAtMost 2 := by
  intro t
  change C.quantitative.terminalGraph.degree t ≤
    2 * (G.neighborSet t.1).ncard
  rw [C.quantitative.terminalGraph_degree t]
  exact (C.quantitative.terminal_degree_le t).trans
    (Nat.mul_le_mul_left 2
      (hostEdgeIndexedGraph_degree_le_neighborNcard G t.1))

/-- An edge of a lifted named walk incident with an original terminal cannot
lie wholly inside one contraction fiber.  It therefore comes from a doubled
normal-form route atom. -/
private theorem exists_routeAtom_of_lifted_edge_incident_terminal
    (e : C.core.graph.Edge)
    (q : (hostEdgeIndexedGraph G).Edge)
    (hq : q ∈ (C.liftedNamedWalk e).edgeList)
    (hincident :
      TerminalPathSkeleton.HostEdgeIncidentToTerminals
        (terminals := terminals) (hostEdgeIndexedOrigin G q)) :
    ∃ a ∈ C.core.grouped.history.routeEdges e,
      q = C.reduction.edgeOrigin a.1 := by
  rcases C.liftedNamedWalk_isLift e q hq with horigin | hfiber
  · rcases horigin with ⟨a, ha, hqa⟩
    exact ⟨a, List.mem_toFinset.mpr ha, hqa⟩
  · rcases hfiber with ⟨z, hz, hleft, hright⟩
    rcases hincident with ⟨t, htTerminal, htEdge⟩
    rw [← hostEdgeIndexedOrigin_endpoints G q] at htEdge
    rcases Sym2.mem_iff.mp htEdge with htLeft | htRight
    · have hzTerminal :=
        C.reduction.terminal_of_mem_fiber hleft
          (htLeft ▸ htTerminal)
      have hrightEq : (hostEdgeIndexedGraph G).right q = t := by
        have h := hright
        rw [hzTerminal,
          C.reduction.terminal_fiber
            ⟨(hostEdgeIndexedGraph G).left q, htLeft ▸ htTerminal⟩] at h
        have hrightLeft :
            (hostEdgeIndexedGraph G).right q =
              (hostEdgeIndexedGraph G).left q := by
          simpa using h
        exact hrightLeft.trans htLeft.symm
      exact ((hostEdgeIndexedGraph G).end_ne q
        (htLeft.symm.trans hrightEq.symm)).elim
    · have hzTerminal :=
        C.reduction.terminal_of_mem_fiber hright
          (htRight ▸ htTerminal)
      have hleftEq : (hostEdgeIndexedGraph G).left q = t := by
        have h := hleft
        rw [hzTerminal,
          C.reduction.terminal_fiber
            ⟨(hostEdgeIndexedGraph G).right q, htRight ▸ htTerminal⟩] at h
        have hleftRight :
            (hostEdgeIndexedGraph G).left q =
              (hostEdgeIndexedGraph G).right q := by
          simpa using h
        exact hleftRight.trans htRight.symm
      exact ((hostEdgeIndexedGraph G).end_ne q
        (hleftEq.trans htRight)).elim

/-- Doubled atoms whose retained original edge is `q`. -/
noncomputable def originFiber
    (q : (hostEdgeIndexedGraph G).Edge) :
    Finset C.reduction.graph.doubleEdges.Edge :=
  Finset.univ.filter fun a => C.reduction.edgeOrigin a.1 = q

@[simp] theorem mem_originFiber
    {q : (hostEdgeIndexedGraph G).Edge}
    {a : C.reduction.graph.doubleEdges.Edge} :
    a ∈ C.originFiber q ↔ C.reduction.edgeOrigin a.1 = q := by
  simp [originFiber]

theorem originFiber_card_le_two
    (q : (hostEdgeIndexedGraph G).Edge) :
    (C.originFiber q).card ≤ 2 := by
  classical
  let tag : C.originFiber q → Bool := fun a => a.1.2
  have htag : Function.Injective tag := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · apply C.reduction.edgeOrigin_injective
      have ha : C.reduction.edgeOrigin a.1.1 = q :=
        C.mem_originFiber.mp a.2
      have hb : C.reduction.edgeOrigin b.1.1 = q :=
        C.mem_originFiber.mp b.2
      exact ha.trans hb.symm
    · exact hab
  have hcard := Fintype.card_le_of_injective tag htag
  simpa only [Fintype.card_coe] using hcard

theorem terminalPathSkeleton_endpointCongestion :
    C.terminalPathSkeleton.EndpointCongestionAtMost 2 := by
  classical
  intro hostEdge hhostEdge hincident
  have hhostFinset : hostEdge ∈ G.edgeFinset := by
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hhostEdge
  rcases exists_hostEdgeIndex G hhostFinset with ⟨q, hqOrigin⟩
  let items : Finset C.core.graph.Edge :=
    Finset.univ.filter fun e =>
      hostEdge ∈ (C.terminalPathSkeleton.hostPath e).edgeSet
  let support : C.core.graph.Edge →
      Finset C.reduction.graph.doubleEdges.Edge :=
    fun e => C.core.grouped.history.routeEdges e ∩ C.originFiber q
  have hnonempty : ∀ e ∈ items, (support e).Nonempty := by
    intro e he
    have hePath :
        hostEdge ∈ (C.terminalPathSkeleton.hostPath e).edgeSet := by
      simpa [items] using he
    have heNamed :=
      NamedEdgeWalk.toHostPath_edgeSet_subset G
        (C.liftedNamedWalk e) hePath
    have heList :
        hostEdge ∈
          ((C.liftedNamedWalk e).edgeList.map
            (hostEdgeIndexedOrigin G)).toFinset := by
      simpa [NamedEdgeWalk.hostEdgeSet] using heNamed
    rcases List.mem_map.mp (List.mem_toFinset.mp heList) with
      ⟨q', hq'List, hq'Origin⟩
    have hincident' :
        TerminalPathSkeleton.HostEdgeIncidentToTerminals
          (terminals := terminals) (hostEdgeIndexedOrigin G q') := by
      simpa [hq'Origin] using hincident
    rcases C.exists_routeAtom_of_lifted_edge_incident_terminal
        e q' hq'List hincident' with ⟨a, haRoute, hq'a⟩
    have hqq' : q' = q := by
      apply hostEdgeIndexedOrigin_injective G
      exact hq'Origin.trans hqOrigin.symm
    refine ⟨a, Finset.mem_inter.mpr ⟨haRoute, ?_⟩⟩
    apply C.mem_originFiber.mpr
    rw [← hq'a, hqq']
  have hpairwise :
      (↑items : Set C.core.graph.Edge).PairwiseDisjoint support := by
    intro e he f hf hef
    exact Finset.disjoint_of_subset_left
      (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right
        (Finset.inter_subset_left)
        (C.core.grouped.history.routeEdges_pairwise_disjoint hef))
  have hsubset : ∀ e ∈ items, support e ⊆ C.originFiber q := by
    intro e he
    exact Finset.inter_subset_right
  have hcard :=
    card_le_card_of_disjoint_nonempty_support items support
      (C.originFiber q) hnonempty hpairwise hsubset
  unfold TerminalPathSkeleton.hostEdgeLoad
  change items.card ≤ 2
  exact hcard.trans (C.originFiber_card_le_two q)

theorem terminalPathSkeleton_internalAvoidance :
    C.terminalPathSkeleton.InternallyAvoidsTerminals := by
  intro e v hv hvTerminal
  rcases C.terminalPathSkeleton_vertex_classification e hv with
    hleft | hright | ⟨s, hlabel, hvFiber⟩
  · rw [GraphPath.IsEndpoint]
    exact Or.inl (by simpa using hleft)
  · rw [GraphPath.IsEndpoint]
    exact Or.inr (by simpa using hright)
  · have hsNonterminal :=
      C.core.grouped.split_nonterminal e s hlabel
    exact (Finset.disjoint_left.mp
      (C.reduction.fiber_disjoint_terminals hsNonterminal)
      hvFiber hvTerminal).elim

theorem terminalPathSkeleton_onePerGroup :
    C.terminalPathSkeleton.OnePerGroupInternallyNodeDisjoint := by
  classical
  intro selected hselected e he f hf hef v hve hvf
  have hselected' :
      ∀ U ∈
          (SimpleGraph.ChekuriChuzhoySection5LabelPartition.partition
            C.core.grouped.label).parts,
        (selected ∩ U).card = 1 := hselected
  have hlabelNe :
      C.core.grouped.label e ≠ C.core.grouped.label f :=
    SimpleGraph.ChekuriChuzhoySection5LabelPartition.label_ne_of_mem_onePerPart
      hselected' he hf hef
  by_cases hvTerminal : v ∈ terminals
  · exact ⟨C.terminalPathSkeleton_internalAvoidance e hve hvTerminal,
      C.terminalPathSkeleton_internalAvoidance f hvf hvTerminal⟩
  · rcases C.terminalPathSkeleton_vertex_classification e hve with
      heLeft | heRight | ⟨s, hlabelE, hvS⟩
    · exact (hvTerminal (heLeft ▸ (C.terminalGraph.left e).2)).elim
    · exact (hvTerminal (heRight ▸ (C.terminalGraph.right e).2)).elim
    · rcases C.terminalPathSkeleton_vertex_classification f hvf with
        hfLeft | hfRight | ⟨r, hlabelF, hvR⟩
      · exact (hvTerminal (hfLeft ▸ (C.terminalGraph.left f).2)).elim
      · exact (hvTerminal (hfRight ▸ (C.terminalGraph.right f).2)).elim
      · have hsr : s ≠ r := by
          intro hsr
          apply hlabelNe
          rw [hlabelE, hlabelF, hsr]
        exact (Finset.disjoint_left.mp
          (C.reduction.fiber_pairwise_disjoint hsr) hvS hvR).elim

/-- All six semantic conclusions of journal Theorem 5.10. -/
theorem terminalPathSkeleton_isTheorem512Output :
    IsTheorem512Output G terminals mu C.terminalPathSkeleton where
  terminal_edge_connected := C.terminalPathSkeleton_edgeConnected
  group_size := C.terminalPathSkeleton_groupSize
  terminal_degree := C.terminalPathSkeleton_terminalDegree
  endpoint_congestion := C.terminalPathSkeleton_endpointCongestion
  internal_terminal_avoidance := C.terminalPathSkeleton_internalAvoidance
  one_per_group_node_disjoint := C.terminalPathSkeleton_onePerGroup

end FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore

/-- Chekuri--Chuzhoy journal Theorem 5.10, specialized to the semantic
existential output used in Section 5. -/
theorem theorem510
    (G : _root_.SimpleGraph V) (terminals : Finset V) (mu : Nat)
    (_hmu : 1 ≤ mu)
    (hconn : TerminalsElementConnectedAtLeast G terminals mu) :
    ∃ S : TerminalPathSkeleton G terminals,
      IsTheorem512Output G terminals mu S := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  have hnamed :
      (hostEdgeIndexedGraph G).TerminalElementConnectedAtLeast terminals mu :=
    hostEdgeIndexedGraph_terminalElementConnectedAtLeast hconn
  rcases (hostEdgeIndexedGraph G).exists_realizedGroupedTerminalCore
      terminals mu hnamed with ⟨C⟩
  exact ⟨C.terminalPathSkeleton,
    C.terminalPathSkeleton_isTheorem512Output⟩

/-- The previously documentary interface is now inhabited by the complete
proof-producing theorem. -/
theorem theorem512Statement : Theorem512Statement := by
  intro V instFintype instDecidableEq G terminals mu hmu hconn
  exact theorem510 G terminals mu hmu hconn

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
