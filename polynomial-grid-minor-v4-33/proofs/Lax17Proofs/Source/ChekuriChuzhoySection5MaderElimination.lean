import Lax17Proofs.Source.ChekuriChuzhoySection5Doubling
import Lax17Proofs.Source.MaderEvenDecomposition

namespace Lax17Proofs

universe u v w

/-!
# Eliminating nonterminals by Mader splitting

This module supplies the global bookkeeping between the one-center Mader
decomposition and the terminal multigraph constructed in Chekuri--Chuzhoy
Section 5.  In a graph where every edge has a terminal endpoint, splitting at
a nonterminal creates a terminal--terminal edge.  It therefore leaves every
other nonterminal star literally unchanged.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A named edge has a distinct parallel copy with the same ordered
endpoints. -/
def HasParallelMate (H : FiniteEdgeIndexedGraph W) (e : H.Edge) : Prop :=
  ∃ f : H.Edge, f ≠ e ∧ H.left f = H.left e ∧ H.right f = H.right e

theorem crosses_iff_of_same_endpoints
    (H : FiniteEdgeIndexedGraph W) {e f : H.Edge}
    (hl : H.left f = H.left e) (hr : H.right f = H.right e)
    (X : Finset W) :
    H.Crosses X f ↔ H.Crosses X e := by
  simp only [Crosses, hl, hr]

/-- A parallel mate prevents a named edge from being the sole edge of a
cut. -/
theorem not_isNamedCutEdge_of_hasParallelMate
    (H : FiniteEdgeIndexedGraph W) {e : H.Edge}
    (h : H.HasParallelMate e) : ¬ H.IsNamedCutEdge e := by
  classical
  rintro ⟨X, hX⟩
  rcases h with ⟨f, hfe, hl, hr⟩
  have heBoundary : e ∈ H.boundary X := by simp [hX]
  have hfBoundary : f ∈ H.boundary X := by
    rw [H.mem_boundary, H.crosses_iff_of_same_endpoints hl hr]
    exact (H.mem_boundary X e).mp heBoundary
  have : f = e := by
    have : f ∈ ({e} : Finset H.Edge) := by simpa [hX] using hfBoundary
    simpa using this
  exact hfe this

/-- Every copy in the doubled graph is paired with the copy carrying the
opposite Boolean tag. -/
theorem doubleEdges_hasParallelMate (H : FiniteEdgeIndexedGraph W)
    (e : H.doubleEdges.Edge) : H.doubleEdges.HasParallelMate e := by
  refine ⟨(e.1, !e.2), ?_, rfl, rfl⟩
  intro h
  have htag := congrArg Prod.snd h
  cases e.2 <;> simp at htag

theorem doubleEdges_noIncidentCutEdge (H : FiniteEdgeIndexedGraph W)
    (s : W) : H.doubleEdges.NoIncidentCutEdge s := by
  intro e _he
  exact H.doubleEdges.not_isNamedCutEdge_of_hasParallelMate
    (H.doubleEdges_hasParallelMate e)

/-- At a nonterminal center, the other endpoint of every incident edge is a
terminal. -/
theorem other_mem_of_every_edge_incident_terminal
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s : W} (hs : s ∉ terminals) (e : H.CenterEdge s) :
    e.other ∈ terminals := by
  rcases e.ends with h | h
  · rcases hedges e.edge with ht | ht
    · exact (hs (h.1 ▸ ht)).elim
    · simpa [h.2] using ht
  · rcases hedges e.edge with ht | ht
    · simpa [h.2] using ht
    · exact (hs (h.1 ▸ ht)).elim

theorem MaderSplitPair.firstOther_mem_terminal
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s : W} (hs : s ∉ terminals) (p : H.MaderSplitPair s) :
    p.firstOther ∈ terminals := by
  exact H.other_mem_of_every_edge_incident_terminal hedges hs
    { edge := p.first, other := p.firstOther, ends := p.first_ends }

theorem MaderSplitPair.secondOther_mem_terminal
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s : W} (hs : s ∉ terminals) (p : H.MaderSplitPair s) :
    p.secondOther ∈ terminals := by
  exact H.other_mem_of_every_edge_incident_terminal hedges hs
    { edge := p.second, other := p.secondOther, ends := p.second_ends }

/-- Splitting at a nonterminal preserves the property that every edge has a
terminal endpoint. -/
theorem every_edge_incident_terminal_maderSplit
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s : W} (hs : s ∉ terminals) (p : H.MaderSplitPair s) :
    ∀ e : (H.maderSplit p).Edge,
      (H.maderSplit p).left e ∈ terminals ∨
        (H.maderSplit p).right e ∈ terminals := by
  intro e
  rcases e with old | new
  · simpa only [maderSplit_old_left, maderSplit_old_right] using hedges old.1
  · exact Or.inl (p.firstOther_mem_terminal hedges hs)

/-- Incidence at a different nonterminal is unchanged by a split. -/
noncomputable def maderSplitIncidentEquivAway
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) :
    (H.maderSplit p).incidentEdges w ≃ H.incidentEdges w := by
  classical
  have hfirstOther := p.firstOther_mem_terminal hedges hs
  have hsecondOther := p.secondOther_mem_terminal hedges hs
  have hfirstNotInc : p.first ∉ H.incidentEdges w := by
    rw [H.mem_incidentEdges]
    rcases p.first_ends with h | h
    · rintro (hleft | hright)
      · exact hws (hleft.symm.trans h.1)
      · exact hw ((hright.symm.trans h.2).symm ▸ hfirstOther)
    · rintro (hleft | hright)
      · exact hw ((hleft.symm.trans h.2).symm ▸ hfirstOther)
      · exact hws (hright.symm.trans h.1)
  have hsecondNotInc : p.second ∉ H.incidentEdges w := by
    rw [H.mem_incidentEdges]
    rcases p.second_ends with h | h
    · rintro (hleft | hright)
      · exact hws (hleft.symm.trans h.1)
      · exact hw ((hright.symm.trans h.2).symm ▸ hsecondOther)
    · rintro (hleft | hright)
      · exact hw ((hleft.symm.trans h.2).symm ▸ hsecondOther)
      · exact hws (hright.symm.trans h.1)
  refine
    { toFun := fun e => by
        obtain ⟨value, hvalue⟩ := e
        rcases value with old | new
        · refine ⟨old.1, ?_⟩
          rw [H.mem_incidentEdges]
          simpa only [maderSplit_old_left, maderSplit_old_right] using
            ((H.maderSplit p).mem_incidentEdges w (Sum.inl old)).mp hvalue
        · have hinc := ((H.maderSplit p).mem_incidentEdges w
              (Sum.inr new)).mp hvalue
          simp only [maderSplit_new_left, maderSplit_new_right] at hinc
          exact (hinc.elim (fun h => hw (h ▸ hfirstOther))
            (fun h => hw (h ▸ hsecondOther))).elim
      invFun := fun e => ⟨Sum.inl ⟨e.1, by
          constructor
          · intro heq
            exact hfirstNotInc (by simpa [heq] using e.2)
          · intro heq
            exact hsecondNotInc (by simpa [heq] using e.2)⟩, by
        rw [(H.maderSplit p).mem_incidentEdges]
        simpa only [maderSplit_old_left, maderSplit_old_right] using
          (H.mem_incidentEdges w e.1).mp e.2⟩
      left_inv := by
        rintro ⟨old | new, he⟩
        · rfl
        · have hinc := ((H.maderSplit p).mem_incidentEdges w
              (Sum.inr new)).mp he
          simp only [maderSplit_new_left, maderSplit_new_right] at hinc
          exact (hinc.elim (fun h => hw (h ▸ hfirstOther))
            (fun h => hw (h ▸ hsecondOther))).elim
      right_inv := by intro e; rfl }

@[simp] theorem maderSplitIncidentEquivAway_apply_left
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) (e : (H.maderSplit p).incidentEdges w) :
    H.left (maderSplitIncidentEquivAway hedges hs hw hws p e).1 =
      (H.maderSplit p).left e.1 := by
  classical
  obtain ⟨value, hvalue⟩ := e
  rcases value with old | new
  · rfl
  · have hinc := ((H.maderSplit p).mem_incidentEdges w
        (Sum.inr new)).mp hvalue
    have hfirstOther := p.firstOther_mem_terminal hedges hs
    have hsecondOther := p.secondOther_mem_terminal hedges hs
    simp only [maderSplit_new_left, maderSplit_new_right] at hinc
    exact (hinc.elim (fun h => hw (h ▸ hfirstOther))
      (fun h => hw (h ▸ hsecondOther))).elim

@[simp] theorem maderSplitIncidentEquivAway_apply_right
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) (e : (H.maderSplit p).incidentEdges w) :
    H.right (maderSplitIncidentEquivAway hedges hs hw hws p e).1 =
      (H.maderSplit p).right e.1 := by
  classical
  obtain ⟨value, hvalue⟩ := e
  rcases value with old | new
  · rfl
  · have hinc := ((H.maderSplit p).mem_incidentEdges w
        (Sum.inr new)).mp hvalue
    have hfirstOther := p.firstOther_mem_terminal hedges hs
    have hsecondOther := p.secondOther_mem_terminal hedges hs
    simp only [maderSplit_new_left, maderSplit_new_right] at hinc
    exact (hinc.elim (fun h => hw (h ▸ hfirstOther))
      (fun h => hw (h ▸ hsecondOther))).elim

@[simp] theorem maderSplitIncidentEquivAway_symm_left
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) (e : H.incidentEdges w) :
    (H.maderSplit p).left
        ((maderSplitIncidentEquivAway hedges hs hw hws p).symm e).1 =
      H.left e.1 := rfl

@[simp] theorem maderSplitIncidentEquivAway_symm_right
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) (e : H.incidentEdges w) :
    (H.maderSplit p).right
        ((maderSplitIncidentEquivAway hedges hs hw hws p).symm e).1 =
      H.right e.1 := rfl

theorem maderSplit_degree_eq_away
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s) :
    (H.maderSplit p).degree w = H.degree w := by
  unfold degree
  rw [← Fintype.card_coe,
    Fintype.card_congr (maderSplitIncidentEquivAway hedges hs hw hws p),
    Fintype.card_coe]

/-- Parallel pairing at every edge of a nonterminal star is preserved when a
different nonterminal is split. -/
theorem all_incident_hasParallelMate_maderSplit_away
    {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    {s w : W} (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (p : H.MaderSplitPair s)
    (hpaired : ∀ e ∈ H.incidentEdges w, H.HasParallelMate e) :
    ∀ e ∈ (H.maderSplit p).incidentEdges w,
      (H.maderSplit p).HasParallelMate e := by
  classical
  let E := maderSplitIncidentEquivAway hedges hs hw hws p
  intro e he
  let ePost : (H.maderSplit p).incidentEdges w := ⟨e, he⟩
  let ePre : H.incidentEdges w := E ePost
  rcases hpaired ePre.1 ePre.2 with ⟨f, hfe, hleft, hright⟩
  have hfInc : f ∈ H.incidentEdges w := by
    have hePre := (H.mem_incidentEdges w ePre.1).mp ePre.2
    rw [H.mem_incidentEdges]
    rcases hePre with h | h
    · exact Or.inl (hleft.trans h)
    · exact Or.inr (hright.trans h)
  let fPre : H.incidentEdges w := ⟨f, hfInc⟩
  let fPost : (H.maderSplit p).incidentEdges w := E.symm fPre
  refine ⟨fPost.1, ?_, ?_, ?_⟩
  · intro hEq
    have hSubtype : fPost = ePost := Subtype.ext hEq
    have hPreEq : fPre = ePre := by
      calc
        fPre = E fPost := (E.apply_symm_apply fPre).symm
        _ = E ePost := congrArg E hSubtype
        _ = ePre := rfl
    exact hfe (congrArg Subtype.val hPreEq)
  · change (H.maderSplit p).left (E.symm fPre).1 =
      (H.maderSplit p).left e
    calc
      _ = H.left f := maderSplitIncidentEquivAway_symm_left
        hedges hs hw hws p fPre
      _ = H.left ePre.1 := hleft
      _ = _ := maderSplitIncidentEquivAway_apply_left
        hedges hs hw hws p ePost
  · change (H.maderSplit p).right (E.symm fPre).1 =
      (H.maderSplit p).right e
    calc
      _ = H.right f := maderSplitIncidentEquivAway_symm_right
        hedges hs hw hws p fPre
      _ = H.right ePre.1 := hright
      _ = _ := maderSplitIncidentEquivAway_apply_right
        hedges hs hw hws p ePost

namespace MaderEvenDecomposition

/-- The graph at the end of a complete one-center decomposition. -/
def finalGraph {s : W} {H : FiniteEdgeIndexedGraph W} :
    MaderEvenDecomposition s H → FiniteEdgeIndexedGraph W
  | .done K _ => K
  | .step _ _ _ tail => tail.finalGraph

theorem final_degree_eq_zero {s : W} {H : FiniteEdgeIndexedGraph W}
    (D : MaderEvenDecomposition s H) : D.finalGraph.degree s = 0 := by
  induction D with
  | done K hzero => exact hzero
  | step K p hadm tail ih => exact ih

theorem final_degree_le {s : W} {H : FiniteEdgeIndexedGraph W}
    (D : MaderEvenDecomposition s H) (w : W) :
    D.finalGraph.degree w ≤ H.degree w := by
  induction D with
  | done K hzero => exact le_rfl
  | step K p hadm tail ih =>
      exact ih.trans (K.maderSplit_degree_le p w)

theorem final_pairwise_terminal
    {s : W} {H : FiniteEdgeIndexedGraph W}
    {terminals : Finset W} (hs : s ∉ terminals)
    (D : MaderEvenDecomposition s H)
    {a b : W} (ha : a ∈ terminals) (hb : b ∈ terminals) (hab : a ≠ b)
    {k : Nat} (hconn : H.PairwiseEdgeConnectedAtLeast a b k) :
    D.finalGraph.PairwiseEdgeConnectedAtLeast a b k := by
  induction D with
  | done K hzero => exact hconn
  | step K p hadm tail ih =>
      apply ih
      exact (hadm a b (fun h => hs (h ▸ ha)) (fun h => hs (h ▸ hb))
        hab k).mp hconn

theorem final_every_edge_incident_terminal
    {s : W} {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hs : s ∉ terminals) (D : MaderEvenDecomposition s H)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals) :
    ∀ e : D.finalGraph.Edge,
      D.finalGraph.left e ∈ terminals ∨ D.finalGraph.right e ∈ terminals := by
  induction D with
  | done K hzero => exact hedges
  | step K p hadm tail ih =>
      exact ih (every_edge_incident_terminal_maderSplit hedges hs p)

theorem final_degree_eq_away
    {s w : W} {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (D : MaderEvenDecomposition s H)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals) :
    D.finalGraph.degree w = H.degree w := by
  induction D with
  | done K hzero => rfl
  | step K p hadm tail ih =>
      change tail.finalGraph.degree w = K.degree w
      rw [ih (every_edge_incident_terminal_maderSplit hedges hs p),
        maderSplit_degree_eq_away hedges hs hw hws p]

theorem final_all_incident_hasParallelMate_away
    {s w : W} {H : FiniteEdgeIndexedGraph W} {terminals : Finset W}
    (hs : s ∉ terminals) (hw : w ∉ terminals) (hws : w ≠ s)
    (D : MaderEvenDecomposition s H)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals)
    (hpaired : ∀ e ∈ H.incidentEdges w, H.HasParallelMate e) :
    ∀ e ∈ D.finalGraph.incidentEdges w, D.finalGraph.HasParallelMate e := by
  induction D with
  | done K hzero => exact hpaired
  | step K p hadm tail ih =>
      exact ih (every_edge_incident_terminal_maderSplit hedges hs p)
        (all_incident_hasParallelMate_maderSplit_away
          hedges hs hw hws p hpaired)

end MaderEvenDecomposition

/-- The connectivity-and-degree part of the terminal multigraph produced by
the Hind--Oellermann/Mader construction. -/
structure TerminalMultigraphCore (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  graph : FiniteEdgeIndexedGraph W
  edge_endpoints_terminal : ∀ e : graph.Edge,
    graph.left e ∈ terminals ∧ graph.right e ∈ terminals
  terminal_pairwise : ∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals →
    a ≠ b → graph.PairwiseEdgeConnectedAtLeast a b k
  terminal_degree_le : ∀ t ∈ terminals, graph.degree t ≤ 2 * H.degree t

/-- The proved even-degree Mader theorem supplies the pair selected at each
recursive stage. -/
theorem evenMaderPairExistence : EvenMaderPairExistence (W := W) := by
  intro H s htwo heven hno
  exact maderAdmissiblePair H s htwo (even_ne_three heven) hno

private theorem exists_terminalElimination
    (base current : FiniteEdgeIndexedGraph W)
    (terminals unprocessed : Finset W) (k : Nat)
    (hunprocessed : ∀ w ∈ unprocessed, w ∉ terminals)
    (hedges : ∀ e : current.Edge,
      current.left e ∈ terminals ∨ current.right e ∈ terminals)
    (hconn : ∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals → a ≠ b →
      current.PairwiseEdgeConnectedAtLeast a b k)
    (hdegree : ∀ t ∈ terminals, current.degree t ≤ base.degree t)
    (heven : ∀ w ∈ unprocessed, Even (current.degree w))
    (hpaired : ∀ w ∈ unprocessed, ∀ e ∈ current.incidentEdges w,
      current.HasParallelMate e)
    (hisolated : ∀ w, w ∉ terminals → w ∉ unprocessed →
      current.degree w = 0) :
    ∃ K : FiniteEdgeIndexedGraph W,
      (∀ e : K.Edge, K.left e ∈ terminals ∧ K.right e ∈ terminals) ∧
      (∀ ⦃a⦄, a ∈ terminals → ∀ ⦃b⦄, b ∈ terminals → a ≠ b →
        K.PairwiseEdgeConnectedAtLeast a b k) ∧
      (∀ t ∈ terminals, K.degree t ≤ base.degree t) := by
  classical
  induction unprocessed using Finset.induction_on generalizing current with
  | empty =>
      refine ⟨current, ?_, hconn, hdegree⟩
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
      have hedgesNext : ∀ e : next.Edge,
          next.left e ∈ terminals ∨ next.right e ∈ terminals :=
        D.final_every_edge_incident_terminal hsTerminal hedges
      apply ih next
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
        rw [D.final_degree_eq_away hsTerminal (hunprocessed w (by simp [hwU]))
          hws hedges]
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

/-- Concrete Mader producer for a Hind--Oellermann normal-form graph.  It
doubles every copy, completely splits every nonterminal star, and proves the
paper's `2 * k` connectivity and factor-two terminal-degree conclusions. -/
theorem exists_terminalMultigraphCore
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals) :
    Nonempty (H.TerminalMultigraphCore terminals (2 * k)) := by
  classical
  let U := Finset.univ \ terminals
  rcases exists_terminalElimination H.doubleEdges H.doubleEdges terminals U
      (2 * k) (by simp [U])
      (by
        intro e
        simpa only [doubleEdges_left, doubleEdges_right] using hedges e.1)
      hconn.doubleEdges_terminals
      (by intro t ht; exact le_rfl)
      (by intro w hw; exact H.doubleEdges_degree_even w)
      (by
        intro w hw e he
        exact H.doubleEdges_hasParallelMate e)
      (by
        intro w hwTerminal hwU
        simp [U, hwTerminal] at hwU) with ⟨K, hends, hpairwise, hdegree⟩
  exact ⟨{
    graph := K
    edge_endpoints_terminal := hends
    terminal_pairwise := hpairwise
    terminal_degree_le := by
      intro t ht
      simpa [H.doubleEdges_degree t] using hdegree t ht }⟩

/-- Output of the complete Hind--Oellermann/Mader connectivity-and-degree
construction.  The terminal map records the changed vertex type caused by
contractions. -/
structure HindMaderTerminalCore (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (k : Nat) where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : FiniteEdgeIndexedGraph Vertex
  terminalMap : TerminalVertex terminals → Vertex
  terminalMap_injective : Function.Injective terminalMap
  edge_endpoints_terminal : ∀ e : graph.Edge,
    graph.left e ∈ terminalMapImage terminalMap ∧
      graph.right e ∈ terminalMapImage terminalMap
  terminal_pairwise : ∀ (a b : TerminalVertex terminals), a ≠ b →
    graph.PairwiseEdgeConnectedAtLeast (terminalMap a) (terminalMap b) (2 * k)
  terminal_degree_le : ∀ t : TerminalVertex terminals,
    graph.degree (terminalMap t) ≤ 2 * H.degree t.1

namespace HindMaderTerminalCore

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) : Fintype C.Vertex :=
  C.vertexFintype

instance {H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {k : Nat}
    (C : H.HindMaderTerminalCore terminals k) : DecidableEq C.Vertex :=
  C.vertexDecidableEq

end HindMaderTerminalCore

/-- Axiom-free producer for the two quantitative conclusions of journal
Theorem 5.10 (called Theorem 5.12 in the earlier project notes). -/
theorem exists_hindMaderTerminalCore
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (k : Nat)
    (hconn : H.TerminalElementConnectedAtLeast terminals k) :
    Nonempty (H.HindMaderTerminalCore terminals k) := by
  classical
  rcases H.exists_hindReduction terminals k hconn with ⟨R⟩
  rcases R.graph.exists_terminalMultigraphCore
      (terminalMapImage R.terminalMap) k R.element_connected
      R.every_edge_incident_terminal with ⟨C⟩
  exact ⟨{
    Vertex := R.Vertex
    graph := C.graph
    terminalMap := R.terminalMap
    terminalMap_injective := R.terminalMap_injective
    edge_endpoints_terminal := C.edge_endpoints_terminal
    terminal_pairwise := by
      intro a b hab
      apply C.terminal_pairwise
      · exact mem_terminalMapImage.mpr ⟨a, rfl⟩
      · exact mem_terminalMapImage.mpr ⟨b, rfl⟩
      · exact R.terminalMap_injective.ne hab
    terminal_degree_le := by
      intro t
      exact (C.terminal_degree_le (R.terminalMap t)
        (mem_terminalMapImage.mpr ⟨t, rfl⟩)).trans
          (Nat.mul_le_mul_left 2 (R.terminal_degree_le t)) }⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
