import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# Element Menger for the Hind--Oellermann argument

This file replaces every nonterminal vertex and every named edge by one
vertex of an incidence graph.  A terminal has `k` interchangeable copies.
Thus a vertex separator of cardinality strictly less than `k` cannot delete
all copies of any terminal, and translates to a terminal element cut in the
original edge-indexed graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Vertices of the capacity-expanded incidence graph.  Nonterminals and
named edges have one copy; each terminal has `k` copies. -/
inductive ElementMengerNode (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat)
  | nonterminal : {v : W // v ∉ terminals} -> ElementMengerNode H terminals k
  | terminal : (v : {v : W // v ∈ terminals}) -> Fin k ->
      ElementMengerNode H terminals k
  | edge : H.Edge -> ElementMengerNode H terminals k
  deriving DecidableEq

/-- The explicit finite sum underlying `ElementMengerNode`. -/
def elementMengerNodeEquiv (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) :
    ElementMengerNode H terminals k ≃
      {v : W // v ∉ terminals} ⊕ ({v : W // v ∈ terminals} × Fin k) ⊕ H.Edge where
  toFun
    | .nonterminal v => Sum.inl v
    | .terminal v i => Sum.inr (Sum.inl (v, i))
    | .edge e => Sum.inr (Sum.inr e)
  invFun
    | Sum.inl v => .nonterminal v
    | Sum.inr (Sum.inl vi) => .terminal vi.1 vi.2
    | Sum.inr (Sum.inr e) => .edge e
  left_inv x := by cases x <;> rfl
  right_inv x := by
    cases x with
    | inl v => rfl
    | inr x =>
        cases x with
        | inl vi => cases vi; rfl
        | inr e => rfl

noncomputable instance (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat) :
    Fintype (ElementMengerNode H terminals k) :=
  Fintype.ofEquiv
    ({v : W // v ∉ terminals} ⊕ ({v : W // v ∈ terminals} × Fin k) ⊕ H.Edge)
    (elementMengerNodeEquiv H terminals k).symm

namespace ElementMengerNode

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}

/-- An endpoint-capacity node represents its underlying original vertex. -/
def Represents : ElementMengerNode H terminals k -> W -> Prop
  | .nonterminal v, w => v.1 = w
  | .terminal v _, w => v.1 = w
  | .edge _, _ => False

@[simp] theorem represents_nonterminal (v : {v : W // v ∉ terminals}) (w : W) :
    (ElementMengerNode.nonterminal v : ElementMengerNode H terminals k).Represents w ↔
      v.1 = w := Iff.rfl

@[simp] theorem represents_terminal (v : {v : W // v ∈ terminals})
    (i : Fin k) (w : W) :
    (ElementMengerNode.terminal v i : ElementMengerNode H terminals k).Represents w ↔
      v.1 = w := Iff.rfl

@[simp] theorem not_represents_edge (e : H.Edge) (w : W) :
    ¬(ElementMengerNode.edge e : ElementMengerNode H terminals k).Represents w := by
  simp [Represents]

end ElementMengerNode

/-- The capacity-expanded incidence graph.  A named edge node is adjacent to
every capacity copy representing either endpoint of that named edge. -/
def elementMengerGraph (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) :
    _root_.SimpleGraph (ElementMengerNode H terminals k) where
  Adj x y :=
    (∃ e, x = .edge e ∧
      (y.Represents (H.left e) ∨ y.Represents (H.right e))) ∨
    (∃ e, y = .edge e ∧
      (x.Represents (H.left e) ∨ x.Represents (H.right e)))
  symm := by
    intro x y h
    exact h.elim Or.inr Or.inl
  loopless := ⟨by
    intro x h
    rcases h with ⟨e, rfl, h⟩ | ⟨e, rfl, h⟩ <;>
      simpa using h⟩

namespace ElementMengerGraph

variable {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}

/-- The `k` capacity copies of a specified terminal. -/
noncomputable def terminalCopies (v : W) :
    Finset (ElementMengerNode H terminals k) := by
  classical
  exact Finset.univ.filter fun x => ∃ (hv : v ∈ terminals) (i : Fin k),
    x = .terminal ⟨v, hv⟩ i

@[simp] theorem mem_terminalCopies_iff (v : W)
    (x : ElementMengerNode H terminals k) :
    x ∈ terminalCopies (H := H) (terminals := terminals) (k := k) v ↔
      ∃ (hv : v ∈ terminals) (i : Fin k), x = .terminal ⟨v, hv⟩ i := by
  classical
  simp [terminalCopies]

theorem terminal_mem_terminalCopies (v : W) (hv : v ∈ terminals) (i : Fin k) :
    (.terminal ⟨v, hv⟩ i : ElementMengerNode H terminals k) ∈
      terminalCopies (H := H) (terminals := terminals) (k := k) v := by
  simp [hv]

/-- A terminal has exactly `k` distinct capacity copies. -/
theorem terminalCopies_card (v : W) (hv : v ∈ terminals) :
    (terminalCopies (H := H) (terminals := terminals) (k := k) v).card = k := by
  classical
  let f : Fin k -> ElementMengerNode H terminals k :=
    fun i => .terminal ⟨v, hv⟩ i
  have hcopies : terminalCopies (H := H) (terminals := terminals) (k := k) v =
      Finset.univ.image f := by
    ext x
    simp only [mem_terminalCopies_iff, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hv', i, rfl⟩
      refine ⟨i, ?_⟩
      congr
    · rintro ⟨i, rfl⟩
      exact ⟨hv, i, rfl⟩
  rw [hcopies, Finset.card_image_iff.mpr]
  · simp
  · intro i _hi j _hj hij
    have hij' := congrArg (elementMengerNodeEquiv H terminals k) hij
    simpa [f] using hij'

/-- Incidence with the left endpoint of a named edge. -/
theorem edge_adj_of_represents_left (e : H.Edge)
    {x : ElementMengerNode H terminals k} (hx : x.Represents (H.left e)) :
    (elementMengerGraph H terminals k).Adj (.edge e) x := by
  exact Or.inl ⟨e, rfl, Or.inl hx⟩

/-- Incidence with the right endpoint of a named edge. -/
theorem edge_adj_of_represents_right (e : H.Edge)
    {x : ElementMengerNode H terminals k} (hx : x.Represents (H.right e)) :
    (elementMengerGraph H terminals k).Adj (.edge e) x := by
  exact Or.inl ⟨e, rfl, Or.inr hx⟩

/-- The neighbors of a named-edge node are exactly the capacity nodes
representing one of its two endpoints. -/
@[simp] theorem edge_adj_iff_represents_endpoint (e : H.Edge)
    (x : ElementMengerNode H terminals k) :
    (elementMengerGraph H terminals k).Adj (.edge e) x ↔
      x.Represents (H.left e) ∨ x.Represents (H.right e) := by
  constructor
  · rintro (⟨f, hfe, hrep⟩ | ⟨f, hxf, hrep⟩)
    · have hfe' := congrArg (elementMengerNodeEquiv H terminals k) hfe
      have : f = e := by simpa using hfe'.symm
      simpa [this] using hrep
    · subst x
      simp [ElementMengerNode.Represents] at hrep
  · intro hrep
    exact Or.inl ⟨e, rfl, hrep⟩

theorem nonterminal_left_adj (e : H.Edge) (hleft : H.left e ∉ terminals) :
    (elementMengerGraph H terminals k).Adj (.edge e) (.nonterminal ⟨H.left e, hleft⟩) :=
  edge_adj_of_represents_left e rfl

theorem nonterminal_right_adj (e : H.Edge) (hright : H.right e ∉ terminals) :
    (elementMengerGraph H terminals k).Adj (.edge e) (.nonterminal ⟨H.right e, hright⟩) :=
  edge_adj_of_represents_right e rfl

theorem terminal_left_adj (e : H.Edge) (hleft : H.left e ∈ terminals) (i : Fin k) :
    (elementMengerGraph H terminals k).Adj (.edge e) (.terminal ⟨H.left e, hleft⟩ i) :=
  edge_adj_of_represents_left e rfl

theorem terminal_right_adj (e : H.Edge) (hright : H.right e ∈ terminals) (i : Fin k) :
    (elementMengerGraph H terminals k).Adj (.edge e) (.terminal ⟨H.right e, hright⟩ i) :=
  edge_adj_of_represents_right e rfl

/-- Isolate all vertices in `X`, retaining every other edge. -/
def avoidingGraph (X : Finset (ElementMengerNode H terminals k)) :
    _root_.SimpleGraph (ElementMengerNode H terminals k) where
  Adj x y := (elementMengerGraph H terminals k).Adj x y ∧ x ∉ X ∧ y ∉ X
  symm := by
    intro x y h
    exact ⟨(elementMengerGraph H terminals k).symm h.1, h.2.2, h.2.1⟩
  loopless := ⟨by
    intro x h
    exact (elementMengerGraph H terminals k).loopless.irrefl x h.1⟩

theorem avoidingGraph_le (X : Finset (ElementMengerNode H terminals k)) :
    avoidingGraph (H := H) (terminals := terminals) (k := k) X ≤
      elementMengerGraph H terminals k := fun _ _ h => h.1

theorem avoidingGraph_adj_iff
    (X : Finset (ElementMengerNode H terminals k))
    (x y : ElementMengerNode H terminals k) :
    (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Adj x y ↔
      (elementMengerGraph H terminals k).Adj x y ∧ x ∉ X ∧ y ∉ X := Iff.rfl

/-- Some capacity copy of `v` is reachable from a surviving capacity copy of
`a` after the vertices in `X` are isolated. -/
def TerminalReachable (X : Finset (ElementMengerNode H terminals k))
    (a v : W) : Prop :=
  ∃ (ha : a ∈ terminals) (i : Fin k) (hv : v ∈ terminals) (j : Fin k),
    (.terminal ⟨a, ha⟩ i : ElementMengerNode H terminals k) ∉ X ∧
    (.terminal ⟨v, hv⟩ j : ElementMengerNode H terminals k) ∉ X ∧
    (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Reachable
      (.terminal ⟨a, ha⟩ i) (.terminal ⟨v, hv⟩ j)

/-- The unique node representing a nonterminal is reachable from a surviving
capacity copy of `a`. -/
def NonterminalReachable (X : Finset (ElementMengerNode H terminals k))
    (a v : W) (hv : v ∉ terminals) : Prop :=
  ∃ (ha : a ∈ terminals) (i : Fin k),
    (.terminal ⟨a, ha⟩ i : ElementMengerNode H terminals k) ∉ X ∧
    (.nonterminal ⟨v, hv⟩ : ElementMengerNode H terminals k) ∉ X ∧
    (avoidingGraph (H := H) (terminals := terminals) (k := k) X).Reachable
      (.terminal ⟨a, ha⟩ i) (.nonterminal ⟨v, hv⟩)

/-- Original vertices represented in the reachable side of the expanded
graph. -/
noncomputable def reachableSide
    (X : Finset (ElementMengerNode H terminals k)) (a : W) : Finset W := by
  classical
  exact Finset.univ.filter fun v =>
    if hv : v ∈ terminals then TerminalReachable X a v
    else NonterminalReachable X a v hv

theorem mem_reachableSide_terminal
    (X : Finset (ElementMengerNode H terminals k)) (a v : W)
    (hv : v ∈ terminals) :
    v ∈ reachableSide (H := H) (terminals := terminals) (k := k) X a ↔
      TerminalReachable X a v := by
  classical
  simp [reachableSide, hv]

theorem mem_reachableSide_nonterminal
    (X : Finset (ElementMengerNode H terminals k)) (a v : W)
    (hv : v ∉ terminals) :
    v ∈ reachableSide (H := H) (terminals := terminals) (k := k) X a ↔
      NonterminalReachable X a v hv := by
  classical
  simp [reachableSide, hv]

/-! ## Encoding an original element cut -/

/-- Capacity-one nodes corresponding to the removed nonterminal vertices. -/
noncomputable def removedVertexNodes {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    Finset (ElementMengerNode H terminals k) := by
  classical
  exact C.removedVertices.attach.map
    ⟨fun v => .nonterminal
      ⟨v.1, fun hv => Finset.disjoint_left.mp C.removedVertices_nonterminal v.2 hv⟩,
      by
        intro v w h
        apply Subtype.ext
        have h' := congrArg (elementMengerNodeEquiv H terminals k) h
        simpa using h'⟩

/-- Capacity-one nodes corresponding to the removed named edges. -/
noncomputable def removedEdgeNodes {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    Finset (ElementMengerNode H terminals k) := by
  classical
  exact C.removedEdges.attach.map
    ⟨fun e => .edge e.1, by
      intro e f h
      apply Subtype.ext
      have h' := congrArg (elementMengerNodeEquiv H terminals k) h
      simpa using h'⟩

/-- The encoding vertices removed by an original terminal element cut. -/
noncomputable def elementSet {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    Finset (ElementMengerNode H terminals k) :=
  removedVertexNodes C k ∪ removedEdgeNodes C k

@[simp] theorem mem_removedVertexNodes_nonterminal_iff {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat)
    (v : {v : W // v ∉ terminals}) :
    (.nonterminal v : ElementMengerNode H terminals k) ∈ removedVertexNodes C k ↔
      v.1 ∈ C.removedVertices := by
  classical
  simp only [removedVertexNodes, Finset.mem_map, Finset.mem_attach]
  constructor
  · rintro ⟨w, _, h⟩
    cases h
    exact w.2
  · intro hv
    refine ⟨⟨v.1, hv⟩, by simp, ?_⟩
    rfl

@[simp] theorem mem_removedEdgeNodes_edge_iff {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) (e : H.Edge) :
    (.edge e : ElementMengerNode H terminals k) ∈ removedEdgeNodes C k ↔
      e ∈ C.removedEdges := by
  classical
  simp [removedEdgeNodes]

@[simp] theorem terminal_not_mem_elementSet {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat)
    (v : {v : W // v ∈ terminals}) (i : Fin k) :
    (.terminal v i : ElementMengerNode H terminals k) ∉ elementSet C k := by
  classical
  simp [elementSet, removedVertexNodes, removedEdgeNodes]

@[simp] theorem nonterminal_mem_elementSet_iff {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat)
    (v : {v : W // v ∉ terminals}) :
    (.nonterminal v : ElementMengerNode H terminals k) ∈ elementSet C k ↔
      v.1 ∈ C.removedVertices := by
  classical
  have hnot : (.nonterminal v : ElementMengerNode H terminals k) ∉
      removedEdgeNodes C k := by
    intro h
    rcases Finset.mem_map.mp h with ⟨e, _he, heq⟩
    have heq' := congrArg (elementMengerNodeEquiv H terminals k) heq
    simp at heq'
  rw [elementSet, Finset.mem_union]
  simp [hnot]

@[simp] theorem edge_mem_elementSet_iff {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) (e : H.Edge) :
    (.edge e : ElementMengerNode H terminals k) ∈ elementSet C k ↔
      e ∈ C.removedEdges := by
  classical
  simp [elementSet, removedVertexNodes]

theorem removedVertexNodes_card {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    (removedVertexNodes C k).card = C.removedVertices.card := by
  classical
  simp [removedVertexNodes]

theorem removedEdgeNodes_card {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    (removedEdgeNodes C k).card = C.removedEdges.card := by
  classical
  simp [removedEdgeNodes]

theorem removedVertexNodes_disjoint_removedEdgeNodes {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    Disjoint (removedVertexNodes C k) (removedEdgeNodes C k) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxv hxe
  rcases Finset.mem_map.mp hxv with ⟨v, _, rfl⟩
  simp [removedEdgeNodes] at hxe

/-- The encoded cut has exactly the original element-cut order. -/
theorem elementSet_card {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    (elementSet C k).card = C.order := by
  classical
  rw [elementSet, Finset.card_union_of_disjoint
    (removedVertexNodes_disjoint_removedEdgeNodes C k),
    removedVertexNodes_card, removedEdgeNodes_card]
  rfl

/-- Side label used to propagate an original cut through the incidence graph.
If the left endpoint of an edge was removed, the edge node takes the side of
its right endpoint; otherwise it takes the side of its left endpoint. -/
def NodeOnCutSide {a b : W} (C : TerminalElementCut H terminals a b) :
    ElementMengerNode H terminals k -> Prop
  | .nonterminal v => v.1 ∈ C.side
  | .terminal v _ => v.1 ∈ C.side
  | .edge e => if H.left e ∈ C.removedVertices then H.right e ∈ C.side
      else H.left e ∈ C.side

theorem nodeOnCutSide_eq_of_adj_of_not_mem {a b : W}
    (C : TerminalElementCut H terminals a b)
    {x y : ElementMengerNode H terminals k}
    (hxy : (elementMengerGraph H terminals k).Adj x y)
    (hx : x ∉ elementSet C k) (hy : y ∉ elementSet C k) :
    NodeOnCutSide C x ↔ NodeOnCutSide C y := by
  classical
  have node_side_of_represents : ∀ {z : ElementMengerNode H terminals k} {w : W},
      z.Represents w -> (NodeOnCutSide C z ↔ w ∈ C.side) := by
    intro z w hrep
    cases z with
    | nonterminal v =>
        change v.1 = w at hrep
        subst w
        rfl
    | terminal v i =>
        change v.1 = w at hrep
        subst w
        rfl
    | edge f => simp [ElementMengerNode.Represents] at hrep
  have not_removed_of_represents :
      ∀ {z : ElementMengerNode H terminals k} {w : W},
        z ∉ elementSet C k -> z.Represents w -> w ∉ C.removedVertices := by
    intro z w hz hrep hw
    cases z with
    | nonterminal v =>
        have hvw : v.1 = w := hrep
        exact hz ((nonterminal_mem_elementSet_iff C k v).2 (hvw ▸ hw))
    | terminal v i =>
        have hvw : v.1 = w := hrep
        exact Finset.disjoint_left.mp C.removedVertices_nonterminal
          (hvw ▸ hw) v.2
    | edge f => simp [ElementMengerNode.Represents] at hrep
  have edge_to_node : ∀ (e : H.Edge) (z : ElementMengerNode H terminals k),
      z.Represents (H.left e) ∨ z.Represents (H.right e) ->
      (.edge e : ElementMengerNode H terminals k) ∉ elementSet C k ->
      z ∉ elementSet C k ->
      (NodeOnCutSide C (.edge e : ElementMengerNode H terminals k) ↔
        NodeOnCutSide C z) := by
    intro e z hrep hedge hz
    rcases hrep with hleft | hright
    · have hl : H.left e ∉ C.removedVertices :=
        not_removed_of_represents hz hleft
      rw [node_side_of_represents hleft]
      simp [NodeOnCutSide, hl]
    · have hr : H.right e ∉ C.removedVertices :=
        not_removed_of_represents hz hright
      rw [node_side_of_represents hright]
      by_cases hl : H.left e ∈ C.removedVertices
      · simp [NodeOnCutSide, hl]
      · have hsame : H.left e ∈ C.side ↔ H.right e ∈ C.side := by
          by_contra hne
          have hcross : H.Crosses C.side e := by
            simp only [Crosses]
            tauto
          exact hedge ((edge_mem_elementSet_iff C k e).2
            (C.crossing_removed e hl hr hcross))
        simpa [NodeOnCutSide, hl] using hsame
  rcases hxy with ⟨e, rfl, hyrep⟩ | ⟨e, rfl, hxrep⟩
  · exact edge_to_node e y hyrep hx hy
  · exact (edge_to_node e x hxrep hy hx).symm

theorem walk_nodeOnCutSide_eq_of_avoids {a b : W}
    (C : TerminalElementCut H terminals a b)
    {x y : ElementMengerNode H terminals k}
    (P : (elementMengerGraph H terminals k).Walk x y)
    (hP : ∀ z ∈ P.support, z ∉ elementSet C k) :
    NodeOnCutSide C x ↔ NodeOnCutSide C y := by
  induction P with
  | nil => rfl
  | @cons x y z hxy P ih =>
      have hx : x ∉ elementSet C k := hP x (by simp)
      have hy : y ∉ elementSet C k := hP y (by simp)
      have htail : ∀ w ∈ P.support, w ∉ elementSet C k := by
        intro w hw
        exact hP w (by simp [hw])
      exact (nodeOnCutSide_eq_of_adj_of_not_mem C hxy hx hy).trans (ih htail)

/-- An original terminal element cut blocks every expanded-graph path between
the capacity copies of its two terminals. -/
theorem cut_blocks {a b : W}
    (C : TerminalElementCut H terminals a b) (k : Nat) :
    STSeparator (elementMengerGraph H terminals k)
      (terminalCopies (H := H) (terminals := terminals) (k := k) a)
      (terminalCopies (H := H) (terminals := terminals) (k := k) b)
      (elementSet C k) := by
  classical
  intro P hconnects
  by_contra hno
  push Not at hno
  have havoid : ∀ z ∈ P.walk.support, z ∉ elementSet C k := by
    intro z hz
    exact hno z (by simpa [GraphPath.vertexSet] using hz)
  have hsides := walk_nodeOnCutSide_eq_of_avoids C P.walk havoid
  rcases hconnects with hconnects | hconnects
  · rcases (mem_terminalCopies_iff a P.source).mp hconnects.1 with ⟨ha, i, hi⟩
    rcases (mem_terminalCopies_iff b P.target).mp hconnects.2 with ⟨hb, j, hj⟩
    have hsource : NodeOnCutSide C P.source := by
      rw [hi]
      exact C.source_mem
    have htarget : NodeOnCutSide C P.target := hsides.mp hsource
    rw [hj] at htarget
    exact C.target_not_mem htarget
  · rcases (mem_terminalCopies_iff b P.source).mp hconnects.1 with ⟨hb, i, hi⟩
    rcases (mem_terminalCopies_iff a P.target).mp hconnects.2 with ⟨ha, j, hj⟩
    have htarget : NodeOnCutSide C P.target := by
      rw [hj]
      exact C.source_mem
    have hsource : NodeOnCutSide C P.source := hsides.mpr htarget
    rw [hi] at hsource
    exact C.target_not_mem hsource

end ElementMengerGraph

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
