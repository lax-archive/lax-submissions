import Lax17Proofs.Source.ChekuriChuzhoySection5GroupedElimination
import Lax17Proofs.Source.ChekuriChuzhoySection5HostLift
import Lax17Proofs.Source.ChekuriChuzhoySection5DisjointSupport
import Lax17Proofs.Source.ChekuriChuzhoySection5LabelPartition

namespace Lax17Proofs

universe u v w

/-!
# Host realization of the grouped terminal core

This module completes the nonalgorithmic content of Chekuri--Chuzhoy journal
Theorem 5.10 (numbered Theorem 5.12 in some project notes).  The final Mader
edges are lifted through the connected Hind--Oellermann contraction fibers,
cycle-erased in the original simple graph, and partitioned by their
construction labels.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}

namespace RealizedGroupedTerminalCore

/-- Forget provenance while retaining the already-proved quantitative core. -/
noncomputable def quantitative
    (C : H.RealizedGroupedTerminalCore terminals k) :
    H.HindMaderTerminalCore terminals k where
  Vertex := C.reduction.Vertex
  graph := C.core.graph
  terminalMap := C.reduction.terminalMap
  terminalMap_injective := C.reduction.terminalMap_injective
  edge_endpoints_terminal := C.core.edge_endpoints_terminal
  terminal_pairwise := by
    intro a b hab
    exact C.core.terminal_pairwise
      (mem_terminalMapImage.mpr ⟨a, rfl⟩)
      (mem_terminalMapImage.mpr ⟨b, rfl⟩)
      (C.reduction.terminalMap_injective.ne hab)
  terminal_degree_le := by
    intro t
    exact (C.core.terminal_degree_le (C.reduction.terminalMap t)
      (mem_terminalMapImage.mpr ⟨t, rfl⟩)).trans
        (Nat.mul_le_mul_left 2 (C.reduction.terminal_degree_le t))

/-- The final graph relabeled by the original terminals. -/
noncomputable def terminalGraph
    (C : H.RealizedGroupedTerminalCore terminals k) :
    FiniteEdgeIndexedGraph (TerminalVertex terminals) :=
  C.quantitative.terminalGraph

@[simp] theorem map_terminalGraph_left
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) :
    C.reduction.terminalMap (C.terminalGraph.left e) =
      C.core.graph.left e :=
  C.quantitative.map_terminalGraph_left e

@[simp] theorem map_terminalGraph_right
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) :
    C.reduction.terminalMap (C.terminalGraph.right e) =
      C.core.graph.right e :=
  C.quantitative.map_terminalGraph_right e

/-- Lift one final edge route all the way back to the original named graph. -/
noncomputable def liftedNamedWalk
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) :
    H.NamedEdgeWalk (C.terminalGraph.left e).1
      (C.terminalGraph.right e).1 := by
  let P := C.core.grouped.history.route e
  have hleft :
      (C.terminalGraph.left e).1 ∈
        C.reduction.fiber (C.core.graph.left e) := by
    rw [← C.map_terminalGraph_left e,
      C.reduction.terminal_fiber (C.terminalGraph.left e)]
    simp
  have hright :
      (C.terminalGraph.right e).1 ∈
        C.reduction.fiber (C.core.graph.right e) := by
    rw [← C.map_terminalGraph_right e,
      C.reduction.terminal_fiber (C.terminalGraph.right e)]
    simp
  exact Classical.choose
    (C.reduction.exists_liftDoubledWalk P hleft hright)

theorem liftedNamedWalk_contained
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) :
    (C.liftedNamedWalk e).ContainedIn
      (C.reduction.fiberUnion
        (C.core.grouped.history.route e).vertexSet) := by
  classical
  unfold liftedNamedWalk
  exact (Classical.choose_spec
    (C.reduction.exists_liftDoubledWalk
      (C.core.grouped.history.route e)
      (by
        rw [← C.map_terminalGraph_left e,
          C.reduction.terminal_fiber (C.terminalGraph.left e)]
        simp)
      (by
        rw [← C.map_terminalGraph_right e,
          C.reduction.terminal_fiber (C.terminalGraph.right e)]
        simp))).1

theorem liftedNamedWalk_isLift
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) :
    C.reduction.IsLiftOf (C.core.grouped.history.route e)
      (C.liftedNamedWalk e) := by
  classical
  unfold liftedNamedWalk
  exact (Classical.choose_spec
    (C.reduction.exists_liftDoubledWalk
      (C.core.grouped.history.route e)
      (by
        rw [← C.map_terminalGraph_left e,
          C.reduction.terminal_fiber (C.terminalGraph.left e)]
        simp)
      (by
        rw [← C.map_terminalGraph_right e,
          C.reduction.terminal_fiber (C.terminalGraph.right e)]
        simp))).2

theorem terminalMapImage_card
    (C : H.RealizedGroupedTerminalCore terminals k) :
    (terminalMapImage C.reduction.terminalMap).card = terminals.card := by
  classical
  rw [terminalMapImage,
    Finset.card_image_of_injective Finset.univ
      C.reduction.terminalMap_injective]
  simp

private theorem direct_fiber_card_le
    (C : H.RealizedGroupedTerminalCore terminals k)
    (f : C.reduction.graph.Edge) :
    (SimpleGraph.ChekuriChuzhoySection5LabelPartition.fiber
      C.core.grouped.label (Sum.inl f)).card ≤ terminals.card := by
  classical
  let items :=
    SimpleGraph.ChekuriChuzhoySection5LabelPartition.fiber
      C.core.grouped.label (Sum.inl f)
  by_cases hitems : items.Nonempty
  · have hsupport :
        items.card ≤ ({(f, false), (f, true)} :
          Finset C.reduction.graph.doubleEdges.Edge).card := by
      apply card_le_card_of_disjoint_nonempty_support items
        C.core.grouped.history.routeEdges
      · intro e he
        exact C.core.grouped.history.routeEdges_nonempty e
      · intro e he f' hf' hef'
        exact C.core.grouped.history.routeEdges_pairwise_disjoint hef'
      · intro e he a ha
        have hlabel :
            C.core.grouped.label e = Sum.inl f := by
          exact SimpleGraph.ChekuriChuzhoySection5LabelPartition.mem_fiber.mp he
        have haf := C.core.grouped.support_direct e f hlabel a ha
        rcases a with ⟨a, tag⟩
        dsimp at haf
        subst a
        cases tag with
        | false =>
            exact Finset.mem_insert_self _ _
        | true =>
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr rfl))
    have htwoImage :
        2 ≤ (terminalMapImage C.reduction.terminalMap).card := by
      rcases hitems with ⟨e, he⟩
      have hlabel :
          C.core.grouped.label e = Sum.inl f :=
        SimpleGraph.ChekuriChuzhoySection5LabelPartition.mem_fiber.mp he
      have hends := C.core.grouped.direct_terminal e f hlabel
      have hsubset :
          ({C.reduction.graph.left f, C.reduction.graph.right f} :
            Finset C.reduction.Vertex) ⊆
            terminalMapImage C.reduction.terminalMap := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        exact hz.elim (fun h => h ▸ hends.1) (fun h => h ▸ hends.2)
      calc
        2 = ({C.reduction.graph.left f, C.reduction.graph.right f} :
          Finset C.reduction.Vertex).card := by
            simp [C.reduction.graph.end_ne f]
        _ ≤ (terminalMapImage C.reduction.terminalMap).card :=
          Finset.card_le_card hsubset
    rw [C.terminalMapImage_card] at htwoImage
    have havailable :
        ({(f, false), (f, true)} :
          Finset C.reduction.graph.doubleEdges.Edge).card = 2 := by
      have hnot :
          (f, false) ∉
            ({(f, true)} :
              Finset C.reduction.graph.doubleEdges.Edge) := by
        intro hmem
        have heq := Finset.mem_singleton.mp hmem
        have hbool := congrArg Prod.snd heq
        cases hbool
      calc
        ({(f, false), (f, true)} :
          Finset C.reduction.graph.doubleEdges.Edge).card =
            ({(f, true)} :
              Finset C.reduction.graph.doubleEdges.Edge).card + 1 :=
          Finset.card_insert_of_notMem hnot
        _ = 2 := by
          have hcard :
              ({(f, true)} :
                Finset C.reduction.graph.doubleEdges.Edge).card = 1 :=
            Finset.card_singleton _
          omega
    rw [havailable] at hsupport
    calc
      items.card ≤ 2 := hsupport
      _ ≤ terminals.card := htwoImage
  · simp only [Finset.not_nonempty_iff_eq_empty] at hitems
    simp [items, hitems]

private theorem split_fiber_card_le
    (C : H.RealizedGroupedTerminalCore terminals k)
    (s : C.reduction.Vertex) :
    (SimpleGraph.ChekuriChuzhoySection5LabelPartition.fiber
      C.core.grouped.label (Sum.inr s)).card ≤ terminals.card := by
  classical
  let items :=
    SimpleGraph.ChekuriChuzhoySection5LabelPartition.fiber
      C.core.grouped.label (Sum.inr s)
  by_cases hitems : items.Nonempty
  · rcases hitems with ⟨e0, he0⟩
    have hlabel0 : C.core.grouped.label e0 = Sum.inr s :=
      SimpleGraph.ChekuriChuzhoySection5LabelPartition.mem_fiber.mp he0
    have hsNonterminal := C.core.grouped.split_nonterminal e0 s hlabel0
    have hmul :
        2 * items.card ≤
          (C.reduction.graph.doubleEdges.incidentEdges s).card := by
      apply mul_card_le_card_of_disjoint_support 2 items
        C.core.grouped.history.routeEdges
      · intro e he
        have hlabel : C.core.grouped.label e = Sum.inr s :=
          SimpleGraph.ChekuriChuzhoySection5LabelPartition.mem_fiber.mp he
        exact C.core.grouped.terminal_split_support_two e s hlabel
          (C.core.edge_endpoints_terminal e).1
          (C.core.edge_endpoints_terminal e).2
      · intro e he f hf hef
        exact C.core.grouped.history.routeEdges_pairwise_disjoint hef
      · intro e he a ha
        rw [C.reduction.graph.doubleEdges.mem_incidentEdges]
        have hlabel : C.core.grouped.label e = Sum.inr s :=
          SimpleGraph.ChekuriChuzhoySection5LabelPartition.mem_fiber.mp he
        exact (C.reduction.graph.mem_incidentEdges s a.1).mp
          (C.core.grouped.support_split e s hlabel a ha)
    have hdegree :
        C.reduction.graph.degree s ≤
          (terminalMapImage C.reduction.terminalMap).card :=
      C.reduction.graph.degree_le_terminalCard_of_terminalStarsSimple
        (terminalMapImage C.reduction.terminalMap)
        C.reduction.every_edge_incident_terminal
        C.reduction.terminal_stars_simple s hsNonterminal
    have hitemsDegree : items.card ≤ C.reduction.graph.degree s := by
      change 2 * items.card ≤
        C.reduction.graph.doubleEdges.degree s at hmul
      rw [C.reduction.graph.doubleEdges_degree s] at hmul
      omega
    rw [C.terminalMapImage_card] at hdegree
    exact hitemsDegree.trans hdegree
  · simp only [Finset.not_nonempty_iff_eq_empty] at hitems
    simp [items, hitems]

/-- Every construction-label group has at most the number of original
terminals. -/
theorem label_fiber_card_le
    (C : H.RealizedGroupedTerminalCore terminals k)
    (key : MaderGroupKey C.reduction.graph) :
    (SimpleGraph.ChekuriChuzhoySection5LabelPartition.fiber
      C.core.grouped.label key).card ≤ terminals.card := by
  cases key with
  | inl f => exact C.direct_fiber_card_le f
  | inr s => exact C.split_fiber_card_le s

/-- A vertex of a lifted route is either an original terminal endpoint or
lies in the one contraction fiber naming its split group. -/
theorem liftedNamedWalk_vertex_classification
    (C : H.RealizedGroupedTerminalCore terminals k)
    (e : C.core.graph.Edge) {v : W}
    (hv : v ∈ (C.liftedNamedWalk e).vertexSet) :
    v = (C.terminalGraph.left e).1 ∨
      v = (C.terminalGraph.right e).1 ∨
      ∃ s, C.core.grouped.label e = Sum.inr s ∧
        v ∈ C.reduction.fiber s := by
  classical
  have hvUnion :=
    (C.liftedNamedWalk_contained e).staysIn hv
  rcases C.reduction.mem_fiberUnion.mp hvUnion with ⟨z, hzRoute, hvFiber⟩
  cases hlabel : C.core.grouped.label e with
  | inl f =>
      have hz := C.core.grouped.route_shape_direct e f hlabel hzRoute
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · left
        have hzMap :
            z = C.reduction.terminalMap (C.terminalGraph.left e) := by
          rw [C.map_terminalGraph_left e]
          exact hz
        rw [hzMap] at hvFiber
        rw [C.reduction.terminal_fiber (C.terminalGraph.left e)] at hvFiber
        simpa using hvFiber
      · right
        left
        have hzMap :
            z = C.reduction.terminalMap (C.terminalGraph.right e) := by
          rw [C.map_terminalGraph_right e]
          exact hz
        rw [hzMap] at hvFiber
        rw [C.reduction.terminal_fiber (C.terminalGraph.right e)] at hvFiber
        simpa using hvFiber
  | inr s =>
      have hz := C.core.grouped.route_shape_split e s hlabel hzRoute
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz | hz
      · left
        have hzMap :
            z = C.reduction.terminalMap (C.terminalGraph.left e) := by
          rw [C.map_terminalGraph_left e]
          exact hz
        rw [hzMap] at hvFiber
        rw [C.reduction.terminal_fiber (C.terminalGraph.left e)] at hvFiber
        simpa using hvFiber
      · right
        left
        have hzMap :
            z = C.reduction.terminalMap (C.terminalGraph.right e) := by
          rw [C.map_terminalGraph_right e]
          exact hz
        rw [hzMap] at hvFiber
        rw [C.reduction.terminal_fiber (C.terminalGraph.right e)] at hvFiber
        simpa using hvFiber
      · exact Or.inr (Or.inr ⟨s, rfl, hz ▸ hvFiber⟩)

end RealizedGroupedTerminalCore

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
