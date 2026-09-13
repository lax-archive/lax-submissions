import Lax17Proofs.Source.ChekuriChuzhoySection5GroupedHistory

namespace Lax17Proofs

universe u v w

/-!
# Grouped elimination of every nonterminal

This is the provenance-carrying version of the global elimination in
`ChekuriChuzhoySection5MaderElimination`.  Its output retains the final
terminal multigraph, all quantitative cut and degree conclusions, and the
grouped edge histories needed to realize its edges in the original host.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A terminal-only Mader core retaining grouped routes in the doubled normal
form. -/
structure GroupedTerminalCore (normal : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  graph : FiniteEdgeIndexedGraph W
  grouped : MaderGroupedHistory normal graph terminals
  edge_endpoints_terminal : ∀ e : graph.Edge,
    graph.left e ∈ terminals ∧ graph.right e ∈ terminals
  terminal_pairwise : ∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals →
    a ≠ b → graph.PairwiseEdgeConnectedAtLeast a b (2 * k)
  terminal_degree_le : ∀ t ∈ terminals,
    graph.degree t ≤ 2 * normal.degree t

namespace GroupedTerminalCore

instance {normal : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : normal.GroupedTerminalCore terminals k) : Fintype C.graph.Edge :=
  C.graph.edgeFintype

instance {normal : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : normal.GroupedTerminalCore terminals k) : DecidableEq C.graph.Edge :=
  C.graph.edgeDecidableEq

end GroupedTerminalCore

private theorem exists_groupedTerminalElimination
    (normal current : FiniteEdgeIndexedGraph W)
    (terminals unprocessed : Finset W) (k : Nat)
    (R : MaderGroupedHistory normal current terminals)
    (hunprocessed : ∀ w ∈ unprocessed, w ∉ terminals)
    (hedges : ∀ e : current.Edge,
      current.left e ∈ terminals ∨ current.right e ∈ terminals)
    (hconn : ∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals → a ≠ b →
      current.PairwiseEdgeConnectedAtLeast a b k)
    (hdegree : ∀ t ∈ terminals,
      current.degree t ≤ normal.doubleEdges.degree t)
    (heven : ∀ w ∈ unprocessed, Even (current.degree w))
    (hpaired : ∀ w ∈ unprocessed, ∀ e ∈ current.incidentEdges w,
      current.HasParallelMate e)
    (hisolated : ∀ w, w ∉ terminals → w ∉ unprocessed →
      current.degree w = 0) :
    ∃ (K : FiniteEdgeIndexedGraph W)
        (_ : MaderGroupedHistory normal K terminals),
      (∀ e : K.Edge, K.left e ∈ terminals ∧ K.right e ∈ terminals) ∧
      (∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals → a ≠ b →
        K.PairwiseEdgeConnectedAtLeast a b k) ∧
      (∀ t ∈ terminals, K.degree t ≤ normal.doubleEdges.degree t) := by
  classical
  induction unprocessed using Finset.induction_on generalizing current with
  | empty =>
      refine ⟨current, R, ?_, hconn, hdegree⟩
      intro e
      rcases hedges e with hleft | hright
      · refine ⟨hleft, ?_⟩
        by_contra hrightTerminal
        have hzero := hisolated (current.right e) hrightTerminal (by simp)
        have hpos : 0 < current.degree (current.right e) := by
          unfold degree
          apply Finset.card_pos.mpr
          exact ⟨e, (current.mem_incidentEdges (current.right e) e).2
            (Or.inr rfl)⟩
        omega
      · refine ⟨?_, hright⟩
        by_contra hleftTerminal
        have hzero := hisolated (current.left e) hleftTerminal (by simp)
        have hpos : 0 < current.degree (current.left e) := by
          unfold degree
          apply Finset.card_pos.mpr
          exact ⟨e, (current.mem_incidentEdges (current.left e) e).2
            (Or.inl rfl)⟩
        omega
  | @insert s U hsU ih =>
      have hsTerminal : s ∉ terminals := hunprocessed s (by simp)
      have hno : current.NoIncidentCutEdge s := by
        intro e he
        exact current.not_isNamedCutEdge_of_hasParallelMate
          (hpaired s (by simp) e he)
      rcases exists_maderEvenDecomposition evenMaderPairExistence current s
          (heven s (by simp)) hno with ⟨D⟩
      let next := D.finalGraph
      let Rnext : MaderGroupedHistory normal next terminals :=
        D.groupedHistory hsTerminal R hedges
      have hedgesNext : ∀ e : next.Edge,
          next.left e ∈ terminals ∨ next.right e ∈ terminals :=
        D.final_every_edge_incident_terminal hsTerminal hedges
      apply ih next Rnext
      · intro w hw
        exact hunprocessed w (by simp [hw])
      · exact hedgesNext
      · intro a ha b hb hab
        exact D.final_pairwise_terminal hsTerminal ha hb hab
          (hconn ha hb hab)
      · intro t ht
        exact (D.final_degree_le t).trans (hdegree t ht)
      · intro w hwU
        have hws : w ≠ s := by
          intro h
          subst w
          exact hsU hwU
        rw [D.final_degree_eq_away hsTerminal
          (hunprocessed w (by simp [hwU])) hws hedges]
        exact heven w (by simp [hwU])
      · intro w hwU e he
        have hws : w ≠ s := by
          intro h
          subst w
          exact hsU hwU
        exact D.final_all_incident_hasParallelMate_away hsTerminal
          (hunprocessed w (by simp [hwU])) hws hedges
          (fun f hf => hpaired w (by simp [hwU]) f hf) e he
      · intro w hwTerminal hwU
        by_cases hws : w = s
        · subst w
          exact D.final_degree_eq_zero
        · rw [D.final_degree_eq_away hsTerminal hwTerminal hws hedges]
          exact hisolated w hwTerminal (by simp [hws, hwU])

/-- The full grouped Mader producer for a graph in Hind--Oellermann normal
form. -/
theorem exists_groupedTerminalCore
    (normal : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : normal.TerminalElementConnectedAtLeast terminals k)
    (hedges : ∀ e : normal.Edge,
      normal.left e ∈ terminals ∨ normal.right e ∈ terminals) :
    Nonempty (normal.GroupedTerminalCore terminals k) := by
  classical
  let U := Finset.univ \ terminals
  let R := MaderGroupedHistory.initial normal terminals hedges
  rcases exists_groupedTerminalElimination normal normal.doubleEdges
      terminals U (2 * k) R
      (by simp [U])
      (by
        intro e
        simpa only [doubleEdges_left, doubleEdges_right] using hedges e.1)
      hconn.doubleEdges_terminals
      (by intro t ht; exact le_rfl)
      (by intro w hw; exact normal.doubleEdges_degree_even w)
      (by
        intro w hw e he
        exact normal.doubleEdges_hasParallelMate e)
      (by
        intro w hwTerminal hwU
        simp [U, hwTerminal] at hwU) with
    ⟨K, hgrouped, hends, hpairwise, hdegree⟩
  exact ⟨{
    graph := K
    grouped := hgrouped
    edge_endpoints_terminal := hends
    terminal_pairwise := hpairwise
    terminal_degree_le := by
      intro t ht
      simpa [normal.doubleEdges_degree t] using hdegree t ht }⟩

/-- A realized Hind reduction together with its grouped terminal-only Mader
core. -/
structure RealizedGroupedTerminalCore
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat) where
  reduction : H.RealizedHindReduction terminals k
  core : reduction.graph.GroupedTerminalCore
    (terminalMapImage reduction.terminalMap) k

namespace RealizedGroupedTerminalCore

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.RealizedGroupedTerminalCore terminals k) :
    Fintype C.reduction.Vertex :=
  C.reduction.vertexFintype

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.RealizedGroupedTerminalCore terminals k) :
    DecidableEq C.reduction.Vertex :=
  C.reduction.vertexDecidableEq

end RealizedGroupedTerminalCore

/-- Provenance-carrying Hind--Oellermann/Mader construction. -/
theorem exists_realizedGroupedTerminalCore
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k) :
    Nonempty (H.RealizedGroupedTerminalCore terminals k) := by
  classical
  rcases H.exists_realizedHindReduction terminals k hconn with ⟨R⟩
  rcases R.graph.exists_groupedTerminalCore
      (terminalMapImage R.terminalMap) k R.element_connected
      R.every_edge_incident_terminal with ⟨C⟩
  exact ⟨{ reduction := R, core := C }⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
