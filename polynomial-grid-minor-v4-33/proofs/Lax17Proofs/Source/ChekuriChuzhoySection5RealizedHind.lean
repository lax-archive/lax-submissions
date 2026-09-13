import Lax17Proofs.Source.ChekuriChuzhoySection5HindReduction
import Lax17Proofs.Source.ChekuriChuzhoySection5ParallelThinning

namespace Lax17Proofs

universe u v w

/-!
# Realized Hind--Oellermann reduction

The endpoint-only reduction in `ChekuriChuzhoySection5HindReduction` is enough
for connectivity and degree estimates, but journal Theorem 5.10 also needs the
connected subgraph represented by every contracted nonterminal.  This module
retains that realization data and the original name of every surviving edge.

The source also deletes duplicate edges from a terminal to one contracted
nonterminal before applying Mader splitting.  `TerminalStarsSimple` is the
precise normal-form condition needed for the resulting groups to have size at
most the number of terminals.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

namespace NamedEdgeWalk

/-- Every endpoint and every endpoint of a traversed named edge lies in `X`.
This formulation is stable under deletion and contraction lifts. -/
def ContainedIn {H : FiniteEdgeIndexedGraph W} {x y : W}
    (P : H.NamedEdgeWalk x y) (X : Finset W) : Prop :=
  x ∈ X ∧ y ∈ X ∧
    ∀ e ∈ P.edgeList, H.left e ∈ X ∧ H.right e ∈ X

@[simp] theorem containedIn_nil {H : FiniteEdgeIndexedGraph W}
    (x : W) (X : Finset W) :
    (NamedEdgeWalk.nil (H := H) x).ContainedIn X ↔ x ∈ X := by
  simp [ContainedIn]

theorem containedIn_cons_iff {H : FiniteEdgeIndexedGraph W}
    {x y z : W} (e : H.Edge) (he : H.Joins e x y)
    (P : H.NamedEdgeWalk y z) (X : Finset W) :
    (NamedEdgeWalk.cons e he P).ContainedIn X ↔
      x ∈ X ∧ P.ContainedIn X := by
  constructor
  · rintro ⟨hx, hz, hall⟩
    have hedge := hall e (by simp)
    have hy : y ∈ X := by
      rcases he with he | he
      · simpa [he.2] using hedge.2
      · simpa [he.2] using hedge.1
    refine ⟨hx, hy, hz, ?_⟩
    intro f hf
    exact hall f (by simp [hf])
  · rintro ⟨hx, hy, hz, hall⟩
    refine ⟨hx, hz, ?_⟩
    intro f hf
    simp only [edgeList_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · rcases he with he | he
      · simpa [he.1, he.2] using And.intro hx hy
      · simpa [he.1, he.2] using And.intro hy hx
    · exact hall f hf

theorem ContainedIn.append {H : FiniteEdgeIndexedGraph W}
    {x y z : W} {P : H.NamedEdgeWalk x y} {Q : H.NamedEdgeWalk y z}
    {X : Finset W} (hP : P.ContainedIn X) (hQ : Q.ContainedIn X) :
    (P.append Q).ContainedIn X := by
  refine ⟨hP.1, hQ.2.1, ?_⟩
  intro e he
  rw [edgeList_append, List.mem_append] at he
  exact he.elim (hP.2.2 e) (hQ.2.2 e)

theorem ContainedIn.mono {H : FiniteEdgeIndexedGraph W}
    {x y : W} {P : H.NamedEdgeWalk x y} {X Y : Finset W}
    (hP : P.ContainedIn X) (hXY : X ⊆ Y) :
    P.ContainedIn Y := by
  exact ⟨hXY hP.1, hXY hP.2.1, fun e he =>
    ⟨hXY (hP.2.2 e he).1, hXY (hP.2.2 e he).2⟩⟩

/-- Lift a named walk through deletion, forgetting the proof that each edge is
not the deleted copy. -/
def liftDelete {H : FiniteEdgeIndexedGraph W} (e0 : H.Edge) {x y : W} :
    (H.deleteEdge e0).NamedEdgeWalk x y → H.NamedEdgeWalk x y
  | .nil x => .nil x
  | .cons e he tail =>
      .cons e.1 (by simpa [FiniteEdgeIndexedGraph.Joins] using he)
        (liftDelete e0 tail)

@[simp] theorem edgeList_liftDelete {H : FiniteEdgeIndexedGraph W}
    (e0 : H.Edge) {x y : W} (P : (H.deleteEdge e0).NamedEdgeWalk x y) :
    (P.liftDelete e0).edgeList =
      P.edgeList.map (fun e : (H.deleteEdge e0).Edge => e.1) := by
  induction P with
  | nil => rfl
  | cons e he tail ih =>
      simp only [liftDelete, edgeList_cons, ih, List.map_cons]

theorem ContainedIn.liftDelete {H : FiniteEdgeIndexedGraph W}
    (e0 : H.Edge) {x y : W} {P : (H.deleteEdge e0).NamedEdgeWalk x y}
    {X : Finset W} (hP : P.ContainedIn X) :
    (P.liftDelete e0).ContainedIn X := by
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro e he
  rw [edgeList_liftDelete, List.mem_map] at he
  rcases he with ⟨f, hf, rfl⟩
  simpa using hP.2.2 f hf

end NamedEdgeWalk

/-- There is at most one named edge between a terminal and a fixed
nonterminal. -/
def TerminalStarsSimple (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) : Prop :=
  ∀ (t : TerminalVertex terminals) (v : W), v ∉ terminals →
    ∀ (e f : H.Edge), H.Joins e t.1 v → H.Joins f t.1 v → e = f

/-- The terminal endpoint of an edge incident with a nonterminal vertex. -/
noncomputable def incidentTerminal
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (v : W) (hv : v ∉ terminals) (e : H.incidentEdges v) :
    TerminalVertex terminals :=
  if hleft : H.left e.1 ∈ terminals then
    ⟨H.left e.1, hleft⟩
  else
    ⟨H.right e.1, (hedges e.1).resolve_left hleft⟩

theorem incidentTerminal_joins
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (v : W) (hv : v ∉ terminals) (e : H.incidentEdges v) :
    H.Joins e.1 (H.incidentTerminal terminals hedges v hv e).1 v := by
  classical
  have hinc := (H.mem_incidentEdges v e.1).1 e.2
  unfold incidentTerminal
  split_ifs with hleft
  · rcases hinc with hright | hright
    · exact (hv (hright ▸ hleft)).elim
    · exact Or.inl ⟨rfl, hright⟩
  · have hrightTerminal := (hedges e.1).resolve_left hleft
    rcases hinc with hleftEq | hrightEq
    · exact Or.inr ⟨rfl, hleftEq⟩
    · exact (hv (hrightEq ▸ hrightTerminal)).elim

theorem incidentTerminal_injective
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (hsimple : H.TerminalStarsSimple terminals)
    (v : W) (hv : v ∉ terminals) :
    Function.Injective (H.incidentTerminal terminals hedges v hv) := by
  intro e f hef
  apply Subtype.ext
  apply hsimple (H.incidentTerminal terminals hedges v hv e) v hv e.1 f.1
  · exact H.incidentTerminal_joins terminals hedges v hv e
  · have hjoins :=
      H.incidentTerminal_joins terminals hedges v hv f
    simpa [hef] using hjoins

/-- A simple terminal star has degree at most the number of terminals. -/
theorem degree_le_terminalCard_of_terminalStarsSimple
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (hsimple : H.TerminalStarsSimple terminals)
    (v : W) (hv : v ∉ terminals) :
    H.degree v ≤ terminals.card := by
  classical
  have hcard := Fintype.card_le_of_injective
    (H.incidentTerminal terminals hedges v hv)
    (H.incidentTerminal_injective terminals hedges hsimple v hv)
  unfold degree
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact hcard

/-! ## Contraction-fiber walk lifting -/

theorem NamedEdgeWalk.projection_source_eq_merged_of_only_contracted
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) {x y : W}
    (P : H.NamedEdgeWalk x y)
    (honly : ∀ e ∈ P.edgeList, e = e0)
    (hne : P.edgeList ≠ []) :
    ContractVertex.projection
        (p := H.left e0) (q := H.right e0) x =
      ContractVertex.merged := by
  cases P with
  | nil x => simp at hne
  | @cons x y z e he tail =>
      have he0 : e = e0 := honly e (by simp)
      subst e
      rcases he with he | he
      · simpa [he.1]
      · simpa [he.1]

theorem ContractFiberBridge.containedIn_preimage
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge) {x y : W}
    (B : ContractFiberBridge H e0 x y)
    {X : Finset (ContractVertex W (H.left e0) (H.right e0))}
    (hxy : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) x =
        ContractVertex.projection
          (p := H.left e0) (q := H.right e0) y)
    (hx : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) x ∈ X) :
    B.walk.ContainedIn (ContractVertex.preimageFinset X) := by
  classical
  refine ⟨by simpa, ?_, ?_⟩
  · simpa [← hxy]
  · intro e he
    have he0 : e = e0 := B.only_contracted e he
    subst e
    have hmerged :
        (ContractVertex.merged :
          ContractVertex W (H.left e0) (H.right e0)) ∈ X := by
      have hsource :
          ContractVertex.projection
              (p := H.left e0) (q := H.right e0) x =
            ContractVertex.merged := by
        exact B.walk.projection_source_eq_merged_of_only_contracted H e0
          B.only_contracted (by
            intro hnil
            rw [hnil] at he
            simp at he)
      simpa [hsource] using hx
    constructor <;> simpa using hmerged

/-- Lift a contracted named walk between prescribed representatives of its
endpoint fibers.  The lifted walk remains inside the full preimage of every
set containing the contracted walk. -/
theorem exists_liftContract_containedIn
    (H : FiniteEdgeIndexedGraph W) (e0 : H.Edge)
    {a b : ContractVertex W (H.left e0) (H.right e0)}
    (P : (H.contractEdge e0).NamedEdgeWalk a b)
    {X : Finset (ContractVertex W (H.left e0) (H.right e0))}
    (hP : P.ContainedIn X)
    {x y : W}
    (hx : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) x = a)
    (hy : ContractVertex.projection
      (p := H.left e0) (q := H.right e0) y = b) :
    ∃ Q : H.NamedEdgeWalk x y,
      Q.ContainedIn (ContractVertex.preimageFinset X) := by
  classical
  induction P generalizing x with
  | nil a =>
      have hxy :
          ContractVertex.projection
              (p := H.left e0) (q := H.right e0) x =
            ContractVertex.projection
              (p := H.left e0) (q := H.right e0) y := hx.trans hy.symm
      rcases exists_contractFiberBridge H e0 hxy with ⟨B⟩
      exact ⟨B.walk, B.containedIn_preimage H e0 hxy (by simpa [← hx] using hP.1)⟩
  | @cons a c b f hf tail ih =>
      have htail : tail.ContainedIn X :=
        ((NamedEdgeWalk.containedIn_cons_iff f hf tail X).1 hP).2
      have haX : a ∈ X :=
        ((NamedEdgeWalk.containedIn_cons_iff f hf tail X).1 hP).1
      rcases hf with hf | hf
      · have hleft :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.left f.1) = a := by
          simpa using hf.1
        have hright :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.right f.1) = c := by
          simpa using hf.2
        have hxleft :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) x =
              ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.left f.1) :=
          hx.trans hleft.symm
        rcases exists_contractFiberBridge H e0 hxleft with ⟨B⟩
        rcases ih htail hright hy with ⟨Q, hQ⟩
        let E : H.NamedEdgeWalk (H.left f.1) (H.right f.1) :=
          .cons f.1 (Or.inl ⟨rfl, rfl⟩) (.nil _)
        have hEX :
            E.ContainedIn (ContractVertex.preimageFinset X) := by
          rw [NamedEdgeWalk.containedIn_cons_iff]
          constructor
          · simpa [hleft] using haX
          · simpa using hQ.1
        exact ⟨B.walk.append (E.append Q),
          (B.containedIn_preimage H e0 hxleft (by simpa [hx] using haX)).append
            (hEX.append hQ)⟩
      · have hright :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.right f.1) = a := by
          simpa using hf.1
        have hleft :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.left f.1) = c := by
          simpa using hf.2
        have hxright :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) x =
              ContractVertex.projection
                (p := H.left e0) (q := H.right e0) (H.right f.1) :=
          hx.trans hright.symm
        rcases exists_contractFiberBridge H e0 hxright with ⟨B⟩
        rcases ih htail hleft hy with ⟨Q, hQ⟩
        let E : H.NamedEdgeWalk (H.right f.1) (H.left f.1) :=
          .cons f.1 (Or.inr ⟨rfl, rfl⟩) (.nil _)
        have hEX :
            E.ContainedIn (ContractVertex.preimageFinset X) := by
          rw [NamedEdgeWalk.containedIn_cons_iff]
          constructor
          · simpa [hright] using haX
          · simpa using hQ.1
        exact ⟨B.walk.append (E.append Q),
          (B.containedIn_preimage H e0 hxright (by simpa [hx] using haX)).append
            (hEX.append hQ)⟩

/-! ## Realized normal form -/

/-- Hind--Oellermann normal form together with its minor model in the input
named graph.  Fibers are pairwise disjoint connected vertex sets, terminal
fibers are singletons, and every surviving edge retains a unique input edge
name crossing its endpoint fibers. -/
structure RealizedHindReduction (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : FiniteEdgeIndexedGraph Vertex
  terminalMap : TerminalVertex terminals → Vertex
  terminalMap_injective : Function.Injective terminalMap
  element_connected : graph.TerminalElementConnectedAtLeast
    (terminalMapImage terminalMap) k
  terminal_degree_le : ∀ t : TerminalVertex terminals,
    graph.degree (terminalMap t) ≤ H.degree t.1
  every_edge_incident_terminal : ∀ e : graph.Edge,
    graph.left e ∈ terminalMapImage terminalMap ∨
      graph.right e ∈ terminalMapImage terminalMap
  terminal_stars_simple :
    graph.TerminalStarsSimple (terminalMapImage terminalMap)
  fiber : Vertex → Finset W
  fiber_nonempty : ∀ z, (fiber z).Nonempty
  fiber_pairwise_disjoint :
    Pairwise fun x y => Disjoint (fiber x) (fiber y)
  terminal_fiber :
    ∀ t : TerminalVertex terminals, fiber (terminalMap t) = {t.1}
  fiber_connected :
    ∀ (z : Vertex) (x : W), x ∈ fiber z → ∀ (y : W), y ∈ fiber z →
      ∃ P : H.NamedEdgeWalk x y, P.ContainedIn (fiber z)
  edgeOrigin : graph.Edge → H.Edge
  edgeOrigin_injective : Function.Injective edgeOrigin
  edgeOrigin_crosses_fibers : ∀ e : graph.Edge,
    (H.left (edgeOrigin e) ∈ fiber (graph.left e) ∧
      H.right (edgeOrigin e) ∈ fiber (graph.right e)) ∨
    (H.right (edgeOrigin e) ∈ fiber (graph.left e) ∧
      H.left (edgeOrigin e) ∈ fiber (graph.right e))

namespace RealizedHindReduction

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.RealizedHindReduction terminals k) : Fintype R.Vertex :=
  R.vertexFintype

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.RealizedHindReduction terminals k) : DecidableEq R.Vertex :=
  R.vertexDecidableEq

theorem fiber_disjoint_terminals
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.RealizedHindReduction terminals k) {z : R.Vertex}
    (hz : z ∉ terminalMapImage R.terminalMap) :
    Disjoint (R.fiber z) terminals := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwFiber hwTerminal
  let t : TerminalVertex terminals := ⟨w, hwTerminal⟩
  have hzt : z ≠ R.terminalMap t := by
    intro h
    apply hz
    exact mem_terminalMapImage.mpr ⟨t, h.symm⟩
  have hwTerminalFiber : w ∈ R.fiber (R.terminalMap t) := by
    rw [R.terminal_fiber t]
    simp [t]
  exact Finset.disjoint_left.mp (R.fiber_pairwise_disjoint hzt)
    hwFiber hwTerminalFiber

theorem terminal_of_mem_fiber
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (R : H.RealizedHindReduction terminals k) {z : R.Vertex} {w : W}
    (hwFiber : w ∈ R.fiber z) (hwTerminal : w ∈ terminals) :
    z = R.terminalMap ⟨w, hwTerminal⟩ := by
  classical
  by_contra hne
  have hwTerminalFiber : w ∈ R.fiber (R.terminalMap ⟨w, hwTerminal⟩) := by
    rw [R.terminal_fiber ⟨w, hwTerminal⟩]
    simp
  exact Finset.disjoint_left.mp (R.fiber_pairwise_disjoint hne)
    hwFiber hwTerminalFiber

/-- The identity realized reduction for a graph already in the simple-star
normal form. -/
noncomputable def refl
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k)
    (hreduced : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (hsimple : H.TerminalStarsSimple terminals) :
    H.RealizedHindReduction terminals k where
  Vertex := W
  graph := H
  terminalMap := fun t => t.1
  terminalMap_injective := fun x y h => Subtype.ext h
  element_connected := by
    simpa [terminalMapImage] using hconn
  terminal_degree_le := fun _ => le_rfl
  every_edge_incident_terminal := by
    intro e
    simpa [terminalMapImage] using hreduced e
  terminal_stars_simple := by
    intro t v hv e f he hf
    apply hsimple ⟨t.1, by simpa [terminalMapImage] using t.2⟩ v
    · simpa [terminalMapImage] using hv
    · exact he
    · exact hf
  fiber := fun z => {z}
  fiber_nonempty := fun z => ⟨z, by simp⟩
  fiber_pairwise_disjoint := by
    intro x y hxy
    exact Finset.disjoint_singleton.mpr hxy
  terminal_fiber := fun _ => rfl
  fiber_connected := by
    intro z x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact ⟨.nil z, by simp⟩
  edgeOrigin := id
  edgeOrigin_injective := Function.injective_id
  edgeOrigin_crosses_fibers := by
    intro e
    exact Or.inl ⟨by simp, by simp⟩

/-- Lift a realized reduction through deletion of one input edge. -/
noncomputable def ofDelete
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (e0 : H.Edge)
    (R : (H.deleteEdge e0).RealizedHindReduction terminals k) :
    H.RealizedHindReduction terminals k where
  Vertex := R.Vertex
  graph := R.graph
  terminalMap := R.terminalMap
  terminalMap_injective := R.terminalMap_injective
  element_connected := R.element_connected
  terminal_degree_le := fun t =>
    (R.terminal_degree_le t).trans (H.deleteEdge_degree_le e0 t.1)
  every_edge_incident_terminal := R.every_edge_incident_terminal
  terminal_stars_simple := R.terminal_stars_simple
  fiber := R.fiber
  fiber_nonempty := R.fiber_nonempty
  fiber_pairwise_disjoint := R.fiber_pairwise_disjoint
  terminal_fiber := R.terminal_fiber
  fiber_connected := by
    intro z x hx y hy
    rcases R.fiber_connected z x hx y hy with ⟨P, hP⟩
    exact ⟨P.liftDelete e0, hP.liftDelete e0⟩
  edgeOrigin := fun e => (R.edgeOrigin e).1
  edgeOrigin_injective := by
    intro e f hef
    apply R.edgeOrigin_injective
    exact Subtype.ext hef
  edgeOrigin_crosses_fibers := by
    intro e
    simpa using R.edgeOrigin_crosses_fibers e

/-- Lift a realized reduction through contraction of a nonterminal edge. -/
noncomputable def ofContract
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (e0 : H.Edge) (hleft : H.left e0 ∉ terminals)
    (hright : H.right e0 ∉ terminals)
    (R : (H.contractEdge e0).RealizedHindReduction
      (ContractVertex.terminalImage
        (p := H.left e0) (q := H.right e0) terminals) k) :
    H.RealizedHindReduction terminals k := by
  classical
  let T' := ContractVertex.terminalImage
    (p := H.left e0) (q := H.right e0) terminals
  let project := H.contractionTerminalMap terminals e0 hleft hright
  let finalMap : TerminalVertex terminals → R.Vertex :=
    fun t => R.terminalMap (project t)
  have himage : terminalMapImage finalMap =
      terminalMapImage R.terminalMap := by
    ext z
    simp only [mem_terminalMapImage, finalMap]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨project t, rfl⟩
    · rintro ⟨t', rfl⟩
      rcases H.contractionTerminalMap_surjective terminals e0 hleft hright t'
        with ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  let finalFiber : R.Vertex → Finset W :=
    fun z => ContractVertex.preimageFinset (R.fiber z)
  refine {
    Vertex := R.Vertex
    graph := R.graph
    terminalMap := finalMap
    terminalMap_injective :=
      R.terminalMap_injective.comp
        (H.contractionTerminalMap_injective terminals e0 hleft hright)
    element_connected := ?_
    terminal_degree_le := ?_
    every_edge_incident_terminal := ?_
    terminal_stars_simple := ?_
    fiber := finalFiber
    fiber_nonempty := ?_
    fiber_pairwise_disjoint := ?_
    terminal_fiber := ?_
    fiber_connected := ?_
    edgeOrigin := fun e => (R.edgeOrigin e).1
    edgeOrigin_injective := ?_
    edgeOrigin_crosses_fibers := ?_ }
  · rw [himage]
    exact R.element_connected
  · intro t
    refine (R.terminal_degree_le (project t)).trans_eq ?_
    exact H.contractEdge_degree_terminal e0 terminals t.1 t.2 hleft hright
  · intro e
    simpa [himage] using R.every_edge_incident_terminal e
  · intro t v hv e f he hf
    have hv' : v ∉ terminalMapImage R.terminalMap := by
      simpa [himage] using hv
    rcases mem_terminalMapImage.mp t.2 with ⟨a, ha⟩
    have hta : R.terminalMap (project a) = t.1 := by
      simpa [finalMap] using ha
    let ta : TerminalVertex (terminalMapImage R.terminalMap) :=
      ⟨R.terminalMap (project a), mem_terminalMapImage.mpr ⟨project a, rfl⟩⟩
    apply R.terminal_stars_simple ta v hv' e f
    · change R.graph.Joins e (R.terminalMap (project a)) v
      rw [hta]
      exact he
    · change R.graph.Joins f (R.terminalMap (project a)) v
      rw [hta]
      exact hf
  · intro z
    exact ContractVertex.preimageFinset_nonempty (R.fiber_nonempty z)
  · intro x y hxy
    apply Finset.disjoint_left.mpr
    intro w hwx hwy
    have hpx : ContractVertex.projection
        (p := H.left e0) (q := H.right e0) w ∈ R.fiber x := by
      simpa [finalFiber] using hwx
    have hpy : ContractVertex.projection
        (p := H.left e0) (q := H.right e0) w ∈ R.fiber y := by
      simpa [finalFiber] using hwy
    exact Finset.disjoint_left.mp (R.fiber_pairwise_disjoint hxy) hpx hpy
  · intro t
    ext w
    constructor
    · intro hw
      have hproj :
          ContractVertex.projection
              (p := H.left e0) (q := H.right e0) w =
            ContractVertex.projection
              (p := H.left e0) (q := H.right e0) t.1 := by
        have hw' :
            ContractVertex.projection
                (p := H.left e0) (q := H.right e0) w ∈
              R.fiber (R.terminalMap (project t)) := by
          simpa [finalFiber, finalMap] using hw
        rw [R.terminal_fiber (project t)] at hw'
        simpa [project, contractionTerminalMap] using hw'
      exact Finset.mem_singleton.mpr
        (ContractVertex.eq_of_projection_eq_of_right_not_endpoint hproj
          (fun h => hleft (h ▸ t.2)) (fun h => hright (h ▸ t.2)))
    · intro hw
      have hwt : w = t.1 := Finset.mem_singleton.mp hw
      subst w
      simp [finalFiber, finalMap, project, contractionTerminalMap,
        R.terminal_fiber]
  · intro z x hx y hy
    have hpx : ContractVertex.projection
        (p := H.left e0) (q := H.right e0) x ∈ R.fiber z := by
      simpa [finalFiber] using hx
    have hpy : ContractVertex.projection
        (p := H.left e0) (q := H.right e0) y ∈ R.fiber z := by
      simpa [finalFiber] using hy
    rcases R.fiber_connected z _ hpx _ hpy with ⟨P, hP⟩
    exact H.exists_liftContract_containedIn e0 P hP rfl rfl
  · intro e f hef
    apply R.edgeOrigin_injective
    exact Subtype.ext hef
  · intro e
    rcases R.edgeOrigin_crosses_fibers e with h | h
    · exact Or.inl ⟨by simpa [finalFiber] using h.1,
        by simpa [finalFiber] using h.2⟩
    · exact Or.inr ⟨by simpa [finalFiber] using h.1,
        by simpa [finalFiber] using h.2⟩

end RealizedHindReduction

/-- Repeated Hind--Oellermann deletion/contraction followed by source-faithful
parallel-star thinning produces a fully realized normal form. -/
theorem exists_realizedHindReduction
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k) :
    Nonempty (H.RealizedHindReduction terminals k) := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (Z : Type u) [Fintype Z] [DecidableEq Z]
      (K : FiniteEdgeIndexedGraph Z) (T : Finset Z),
      Fintype.card K.Edge = n →
      K.TerminalElementConnectedAtLeast T k →
        Nonempty (K.RealizedHindReduction T k)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Z _ _ K T hcard hconnected
        by_cases hreduced : ∀ e : K.Edge,
            K.left e ∈ T ∨ K.right e ∈ T
        · by_cases hsimple : K.TerminalStarsSimple T
          · exact ⟨RealizedHindReduction.refl
              K T k hconnected hreduced hsimple⟩
          · simp only [TerminalStarsSimple] at hsimple
            push_neg at hsimple
            rcases hsimple with
              ⟨t, v, hv, eDrop, eKeep, hDrop, hKeep, hne⟩
            have hdelete :
                (K.deleteEdge eDrop).TerminalElementConnectedAtLeast T k :=
              hconnected.deleteEdge_of_parallel_terminal_nonterminal
                eDrop eKeep hne t.2 hv hDrop hKeep
            have hlt : Fintype.card (K.deleteEdge eDrop).Edge < n := by
              rw [K.deleteEdge_edgeCard eDrop, hcard]
              have hpos : 0 < n := by
                rw [← hcard]
                exact Fintype.card_pos_iff.mpr ⟨eDrop⟩
              omega
            rcases ih _ hlt Z (K.deleteEdge eDrop) T rfl hdelete with ⟨R⟩
            exact ⟨RealizedHindReduction.ofDelete K T k eDrop R⟩
        · push Not at hreduced
          rcases hreduced with ⟨e, hleft, hright⟩
          rcases hindOellermannDeletionContraction K T k e hleft hright
              hconnected with hdelete | hcontract
          · have hlt : Fintype.card (K.deleteEdge e).Edge < n := by
              rw [K.deleteEdge_edgeCard e, hcard]
              have hpos : 0 < n := by
                rw [← hcard]
                exact Fintype.card_pos_iff.mpr ⟨e⟩
              omega
            rcases ih _ hlt Z (K.deleteEdge e) T rfl hdelete with ⟨R⟩
            exact ⟨RealizedHindReduction.ofDelete K T k e R⟩
          · let T' := ContractVertex.terminalImage
                (p := K.left e) (q := K.right e) T
            have hlt : Fintype.card (K.contractEdge e).Edge < n := by
              rw [← hcard]
              exact K.contractEdge_edgeCard_lt e
            rcases ih _ hlt (ContractVertex Z (K.left e) (K.right e))
                (K.contractEdge e) T' rfl hcontract with ⟨R⟩
            exact ⟨RealizedHindReduction.ofContract
              K T k e hleft hright R⟩
  exact hP (Fintype.card H.Edge) W H terminals rfl hconn

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
