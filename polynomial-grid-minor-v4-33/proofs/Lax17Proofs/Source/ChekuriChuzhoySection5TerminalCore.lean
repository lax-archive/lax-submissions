import Lax17Proofs.Source.ChekuriChuzhoySection5MaderElimination

namespace Lax17Proofs

universe u v w

/-!
# Relabeling the Mader core by the original terminals

Hind--Oellermann contractions change the ambient vertex type.  This module
uses the injective terminal map to restrict and relabel the final graph so its
vertex type is exactly the original terminal subtype.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The unique original terminal represented by a point in the terminal-map
image. -/
noncomputable def terminalPreimage {terminals : Finset W} {Z : Type u}
    [DecidableEq Z] (f : TerminalVertex terminals → Z) {z : Z}
    (hz : z ∈ terminalMapImage f) : TerminalVertex terminals :=
  Classical.choose (mem_terminalMapImage.mp hz)

theorem terminalMap_terminalPreimage {terminals : Finset W} {Z : Type u}
    [DecidableEq Z] (f : TerminalVertex terminals → Z) {z : Z}
    (hz : z ∈ terminalMapImage f) :
    f (terminalPreimage f hz) = z :=
  Classical.choose_spec (mem_terminalMapImage.mp hz)

/-- Relabel the terminal-only core by the original terminal subtype. -/
noncomputable def HindMaderTerminalCore.terminalGraph
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) :
    FiniteEdgeIndexedGraph (TerminalVertex terminals) where
  Edge := C.graph.Edge
  left e := terminalPreimage C.terminalMap
    (C.edge_endpoints_terminal e).1
  right e := terminalPreimage C.terminalMap
    (C.edge_endpoints_terminal e).2
  end_ne := by
    intro e heq
    apply C.graph.end_ne e
    calc
      C.graph.left e = C.terminalMap
          (terminalPreimage C.terminalMap
            (C.edge_endpoints_terminal e).1) :=
        (terminalMap_terminalPreimage C.terminalMap
          (C.edge_endpoints_terminal e).1).symm
      _ = C.terminalMap
          (terminalPreimage C.terminalMap
            (C.edge_endpoints_terminal e).2) := congrArg C.terminalMap heq
      _ = C.graph.right e := terminalMap_terminalPreimage C.terminalMap
        (C.edge_endpoints_terminal e).2

@[simp] theorem HindMaderTerminalCore.map_terminalGraph_left
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) (e : C.graph.Edge) :
    C.terminalMap (C.terminalGraph.left e) = C.graph.left e := by
  exact terminalMap_terminalPreimage C.terminalMap
    (C.edge_endpoints_terminal e).1

@[simp] theorem HindMaderTerminalCore.map_terminalGraph_right
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) (e : C.graph.Edge) :
    C.terminalMap (C.terminalGraph.right e) = C.graph.right e := by
  exact terminalMap_terminalPreimage C.terminalMap
    (C.edge_endpoints_terminal e).2

theorem mem_image_terminalMap_iff
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k)
    (X : Finset (TerminalVertex terminals)) (t : TerminalVertex terminals) :
    C.terminalMap t ∈ X.image C.terminalMap ↔ t ∈ X := by
  classical
  simp [C.terminalMap_injective.eq_iff]

theorem HindMaderTerminalCore.crosses_image_iff
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k)
    (X : Finset (TerminalVertex terminals)) (e : C.graph.Edge) :
    C.graph.Crosses (X.image C.terminalMap) e ↔
      C.terminalGraph.Crosses X e := by
  simp only [Crosses]
  rw [show C.graph.left e = C.terminalMap (C.terminalGraph.left e) by
      exact (C.map_terminalGraph_left e).symm,
    show C.graph.right e = C.terminalMap (C.terminalGraph.right e) by
      exact (C.map_terminalGraph_right e).symm]
  simp only [Crosses, mem_image_terminalMap_iff C]

theorem HindMaderTerminalCore.boundary_image
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k)
    (X : Finset (TerminalVertex terminals)) :
    C.graph.boundary (X.image C.terminalMap) = C.terminalGraph.boundary X := by
  ext e
  rw [C.graph.mem_boundary]
  exact (C.crosses_image_iff X e).trans
    (C.terminalGraph.mem_boundary X e).symm

theorem HindMaderTerminalCore.terminalGraph_pairwise
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) (a b : TerminalVertex terminals)
    (hab : a ≠ b) :
    C.terminalGraph.PairwiseEdgeConnectedAtLeast a b (2 * k) := by
  intro X ha hb
  have hmapa : C.terminalMap a ∈ X.image C.terminalMap :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmapb : C.terminalMap b ∉ X.image C.terminalMap := by
    exact (mem_image_terminalMap_iff C X b).not.mpr hb
  have hcut := C.terminal_pairwise a b hab
    (X.image C.terminalMap) hmapa hmapb
  simpa [C.boundary_image X] using hcut

theorem isEdgeConnected_of_pairwise
    (K : FiniteEdgeIndexedGraph W) (q : Nat)
    (hpair : ∀ a b : W, a ≠ b → K.PairwiseEdgeConnectedAtLeast a b q) :
    K.IsEdgeConnected q := by
  classical
  intro X hX hproper
  rcases hX with ⟨a, ha⟩
  have hex : ∃ b : W, b ∉ X := by
    by_contra h
    push Not at h
    apply hproper
    ext b
    simp [h b]
  rcases hex with ⟨b, hb⟩
  exact hpair a b (fun hab => hb (hab ▸ ha)) X ha hb

theorem HindMaderTerminalCore.terminalGraph_edgeConnected
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) :
    C.terminalGraph.IsEdgeConnected (2 * k) := by
  apply isEdgeConnected_of_pairwise
  intro a b hab
  exact C.terminalGraph_pairwise a b hab

theorem HindMaderTerminalCore.terminalGraph_degree
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) (t : TerminalVertex terminals) :
    C.terminalGraph.degree t = C.graph.degree (C.terminalMap t) := by
  classical
  unfold degree
  congr 1
  ext e
  rw [C.terminalGraph.mem_incidentEdges]
  constructor
  · rintro (h | h)
    · apply (C.graph.mem_incidentEdges (C.terminalMap t) e).2
      exact Or.inl (by
        rw [← C.map_terminalGraph_left e]
        exact congrArg C.terminalMap h)
    · apply (C.graph.mem_incidentEdges (C.terminalMap t) e).2
      exact Or.inr (by
        rw [← C.map_terminalGraph_right e]
        exact congrArg C.terminalMap h)
  · intro hinc
    rcases (C.graph.mem_incidentEdges (C.terminalMap t) e).1 hinc with h | h
    · left
      apply C.terminalMap_injective
      simpa using h
    · right
      apply C.terminalMap_injective
      simpa using h

/-- Final connectivity-and-degree output on exactly the original terminal
labels. -/
structure TerminalConnectivityDegreeOutput (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  graph : FiniteEdgeIndexedGraph (TerminalVertex terminals)
  edge_connected : graph.IsEdgeConnected (2 * k)
  terminal_degree_le : ∀ t : TerminalVertex terminals,
    graph.degree t ≤ 2 * H.degree t.1

/-- Constructive terminal-labeled form of the quantitative part of journal
Theorem 5.10. -/
theorem exists_terminalConnectivityDegreeOutput
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k) :
    Nonempty (H.TerminalConnectivityDegreeOutput terminals k) := by
  rcases H.exists_hindMaderTerminalCore terminals k hconn with ⟨C⟩
  exact ⟨{
    graph := C.terminalGraph
    edge_connected := C.terminalGraph_edgeConnected
    terminal_degree_le := by
      intro t
      rw [C.terminalGraph_degree t]
      exact C.terminal_degree_le t }⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
