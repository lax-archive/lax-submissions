import Lax17Proofs.Source.ChekuriChuzhoySection5MaderHistory
import Lax17Proofs.Source.ChekuriChuzhoySection5MaderElimination

namespace Lax17Proofs

universe u v w

/-!
# Grouped histories for the terminal skeleton

Journal Theorem 5.10 groups a final terminal edge either with the other
parallel copy of one original terminal--terminal edge, or with all edges
created while splitting one nonterminal star.  This module carries that group
key through the Mader splitting sequence.  It also records the exact route
shape used by the host-realization argument.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A direct group is named by an edge of the undoubled normal form.  A split
group is named by the nonterminal whose star was split. -/
abbrev MaderGroupKey (normal : FiniteEdgeIndexedGraph W) :=
  normal.Edge ⊕ W

/-- The initial key of a doubled edge. -/
def initialMaderGroupKey (normal : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (e : normal.doubleEdges.Edge) :
    MaderGroupKey normal :=
  if normal.left e.1 ∈ terminals then
    if normal.right e.1 ∈ terminals then Sum.inl e.1
    else Sum.inr (normal.right e.1)
  else Sum.inr (normal.left e.1)

/-- Edge histories enriched with the group and route-shape invariants used in
the proof of journal Theorem 5.10. -/
structure MaderGroupedHistory
    (normal current : FiniteEdgeIndexedGraph W) (terminals : Finset W) where
  history : MaderEdgeHistory normal.doubleEdges current
  label : current.Edge → MaderGroupKey normal
  direct_terminal :
    ∀ e f, label e = Sum.inl f →
      normal.left f ∈ terminals ∧ normal.right f ∈ terminals
  split_nonterminal :
    ∀ e s, label e = Sum.inr s → s ∉ terminals
  support_direct :
    ∀ e f, label e = Sum.inl f →
      ∀ a ∈ history.routeEdges e, a.1 = f
  support_split :
    ∀ e s, label e = Sum.inr s →
      ∀ a ∈ history.routeEdges e,
        a.1 ∈ normal.incidentEdges s
  nonterminal_endpoint_label :
    ∀ e w, (current.left e = w ∨ current.right e = w) →
      w ∉ terminals → label e = Sum.inr w
  route_shape_direct :
    ∀ e f, label e = Sum.inl f →
      (history.route e).vertexSet ⊆
        {current.left e, current.right e}
  route_shape_split :
    ∀ e s, label e = Sum.inr s →
      (history.route e).vertexSet ⊆
        {current.left e, current.right e, s}
  terminal_split_support_two :
    ∀ e s, label e = Sum.inr s →
      current.left e ∈ terminals → current.right e ∈ terminals →
        2 ≤ (history.routeEdges e).card

namespace MaderEdgeHistory

@[simp] theorem routeAlong_vertexSet
    {base current : FiniteEdgeIndexedGraph W}
    (R : MaderEdgeHistory base current)
    (e : current.Edge) {a b : W} (he : current.Joins e a b) :
    (R.routeAlong e he).vertexSet = (R.route e).vertexSet := by
  by_cases hleft : current.left e = a
  · simp [routeAlong, hleft]
  · simp [routeAlong, hleft]

end MaderEdgeHistory

namespace MaderGroupedHistory

variable {normal current : FiniteEdgeIndexedGraph W}
variable {terminals : Finset W}

/-- The grouped history before any split. -/
noncomputable def initial
    (normal : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hedges : ∀ e : normal.Edge,
      normal.left e ∈ terminals ∨ normal.right e ∈ terminals) :
    MaderGroupedHistory normal normal.doubleEdges terminals where
  history := MaderEdgeHistory.identity normal.doubleEdges
  label := initialMaderGroupKey normal terminals
  direct_terminal := by
    intro e f hlabel
    simp only [initialMaderGroupKey] at hlabel
    split at hlabel <;> rename_i hleft
    · split at hlabel <;> rename_i hright
      · have hef : e.1 = f := Sum.inl.inj hlabel
        subst f
        exact ⟨hleft, hright⟩
      · simp at hlabel
    · simp at hlabel
  split_nonterminal := by
    intro e s hlabel
    simp only [initialMaderGroupKey] at hlabel
    split at hlabel <;> rename_i hleft
    · split at hlabel <;> rename_i hright
      · simp at hlabel
      · have hrs : normal.right e.1 = s := Sum.inr.inj hlabel
        simpa [← hrs] using hright
    · have hls : normal.left e.1 = s := Sum.inr.inj hlabel
      simpa [← hls] using hleft
  support_direct := by
    intro e f hlabel a ha
    simp only [MaderEdgeHistory.identity, MaderEdgeHistory.routeEdges,
      NamedEdgeWalk.edgeList_cons, NamedEdgeWalk.edgeList_nil,
      List.toFinset_cons, List.toFinset_nil] at ha
    have hae : a = e := by simpa using ha
    subst a
    simp only [initialMaderGroupKey] at hlabel
    split at hlabel <;> rename_i hleft
    · split at hlabel <;> rename_i hright
      · exact Sum.inl.inj hlabel
      · simp at hlabel
    · simp at hlabel
  support_split := by
    intro e s hlabel a ha
    simp only [MaderEdgeHistory.identity, MaderEdgeHistory.routeEdges,
      NamedEdgeWalk.edgeList_cons, NamedEdgeWalk.edgeList_nil,
      List.toFinset_cons, List.toFinset_nil] at ha
    have hae : a = e := by simpa using ha
    subst a
    rw [normal.mem_incidentEdges]
    simp only [initialMaderGroupKey] at hlabel
    split at hlabel <;> rename_i hleft
    · split at hlabel <;> rename_i hright
      · simp at hlabel
      · exact Or.inr (Sum.inr.inj hlabel)
    · exact Or.inl (Sum.inr.inj hlabel)
  nonterminal_endpoint_label := by
    intro e w hew hw
    change normal.left e.1 = w ∨ normal.right e.1 = w at hew
    rcases hew with hleft | hright
    · subst w
      have hw' : normal.left e.1 ∉ terminals := by simpa using hw
      simp [initialMaderGroupKey, hw']
    · subst w
      have hw' : normal.right e.1 ∉ terminals := by simpa using hw
      by_cases hleft : normal.left e.1 ∈ terminals
      · simp [initialMaderGroupKey, hleft, hw']
      · rcases hedges e.1 with ht | ht
        · exact (hleft ht).elim
        · exact (hw' ht).elim
  route_shape_direct := by
    intro e f hlabel
    intro w hw
    simpa [MaderEdgeHistory.identity] using hw
  route_shape_split := by
    intro e s hlabel
    intro w hw
    have hw' : w ∈ ({normal.left e.1, normal.right e.1} : Finset W) := by
      simpa [MaderEdgeHistory.identity] using hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw' ⊢
    exact hw'.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
  terminal_split_support_two := by
    intro e s hlabel hleft hright
    have hleft' : normal.left e.1 ∈ terminals := by simpa using hleft
    have hright' : normal.right e.1 ∈ terminals := by simpa using hright
    simp [initialMaderGroupKey, hleft', hright'] at hlabel

/-- Transport a group label through one split. -/
def splitLabel (R : MaderGroupedHistory normal current terminals)
    {s : W} (p : current.MaderSplitPair s)
    (e : (current.maderSplit p).Edge) : MaderGroupKey normal :=
  match e with
  | .inl f => R.label f.1
  | .inr _ => Sum.inr s

@[simp] theorem splitLabel_old
    (R : MaderGroupedHistory normal current terminals)
    {s : W} (p : current.MaderSplitPair s)
    (e : {e : current.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    R.splitLabel p (.inl e) = R.label e.1 :=
  rfl

@[simp] theorem splitLabel_new
    (R : MaderGroupedHistory normal current terminals)
    {s : W} (p : current.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    R.splitLabel p (.inr u) = Sum.inr s :=
  rfl

private theorem pair_label
    (R : MaderGroupedHistory normal current terminals)
    {s : W} (hs : s ∉ terminals) (p : current.MaderSplitPair s) :
    R.label p.first = Sum.inr s ∧ R.label p.second = Sum.inr s := by
  constructor
  · exact R.nonterminal_endpoint_label p.first s
      (p.first_ends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hs
  · exact R.nonterminal_endpoint_label p.second s
      (p.second_ends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hs

private theorem route_shape_of_incident
    (R : MaderGroupedHistory normal current terminals)
    {s : W} (hs : s ∉ terminals) (e : current.Edge) (other : W)
    (he : current.Joins e s other) :
    (R.history.route e).vertexSet ⊆ {s, other} := by
  have hlabel := R.nonterminal_endpoint_label e s
    (he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hs
  have hshape := R.route_shape_split e s hlabel
  intro w hw
  have hw' := hshape hw
  rcases he with he | he
  · simp only [he.1, he.2, Finset.mem_insert,
      Finset.mem_singleton] at hw' ⊢
    tauto
  · simp only [he.1, he.2, Finset.mem_insert,
      Finset.mem_singleton] at hw' ⊢
    tauto

/-- One Mader split preserves all grouping and route-shape invariants. -/
noncomputable def split
    (R : MaderGroupedHistory normal current terminals)
    {s : W} (hs : s ∉ terminals)
    (hedges : ∀ e : current.Edge,
      current.left e ∈ terminals ∨ current.right e ∈ terminals)
    (p : current.MaderSplitPair s) :
    MaderGroupedHistory normal (current.maderSplit p) terminals where
  history := R.history.split p
  label := R.splitLabel p
  direct_terminal := by
    intro e f hlabel
    cases e with
    | inl e => exact R.direct_terminal e.1 f hlabel
    | inr u => simp at hlabel
  split_nonterminal := by
    intro e w hlabel
    cases e with
    | inl e => exact R.split_nonterminal e.1 w hlabel
    | inr u =>
        change (Sum.inr s : MaderGroupKey normal) = Sum.inr w at hlabel
        have : w = s := (Sum.inr.inj hlabel).symm
        simpa [this] using hs
  support_direct := by
    intro e f hlabel a ha
    cases e with
    | inl e =>
        exact R.support_direct e.1 f hlabel a ha
    | inr u => simp at hlabel
  support_split := by
    intro e w hlabel a ha
    cases e with
    | inl e =>
        exact R.support_split e.1 w hlabel a ha
    | inr u =>
        change (Sum.inr s : MaderGroupKey normal) = Sum.inr w at hlabel
        have hws : w = s := (Sum.inr.inj hlabel).symm
        subst w
        rw [R.history.split_routeEdges_new p u] at ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact R.support_split p.first s (R.pair_label hs p).1 a ha
        · exact R.support_split p.second s (R.pair_label hs p).2 a ha
  nonterminal_endpoint_label := by
    intro e w hew hw
    cases e with
    | inl e =>
        exact R.nonterminal_endpoint_label e.1 w hew hw
    | inr u =>
        have hfirst := p.firstOther_mem_terminal hedges hs
        have hsecond := p.secondOther_mem_terminal hedges hs
        rcases hew with h | h
        · exact (hw (h ▸ hfirst)).elim
        · exact (hw (h ▸ hsecond)).elim
  route_shape_direct := by
    intro e f hlabel
    cases e with
    | inl e =>
        exact R.route_shape_direct e.1 f hlabel
    | inr u => simp at hlabel
  route_shape_split := by
    intro e w hlabel
    cases e with
    | inl e =>
        exact R.route_shape_split e.1 w hlabel
    | inr u =>
        change (Sum.inr s : MaderGroupKey normal) = Sum.inr w at hlabel
        have hws : w = s := (Sum.inr.inj hlabel).symm
        subst w
        rw [MaderEdgeHistory.split_route_new]
        intro z hz
        change z ∈
          ((R.history.routeAlong p.first
              ((current.joins_comm p.first s p.firstOther).mp p.first_ends)).append
            (R.history.routeAlong p.second p.second_ends)).vertexSet at hz
        rw [NamedEdgeWalk.vertexSet_append] at hz
        simp only [MaderEdgeHistory.routeAlong_vertexSet] at hz
        rcases Finset.mem_union.mp hz with hz | hz
        · have hshape := R.route_shape_of_incident hs p.first p.firstOther
            p.first_ends
          have hz' := hshape hz
          simp only [FiniteEdgeIndexedGraph.maderSplit_new_left,
            FiniteEdgeIndexedGraph.maderSplit_new_right,
            Finset.mem_insert, Finset.mem_singleton] at hz' ⊢
          rcases hz' with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
        · have hshape := R.route_shape_of_incident hs p.second p.secondOther
            p.second_ends
          have hz' := hshape hz
          simp only [FiniteEdgeIndexedGraph.maderSplit_new_left,
            FiniteEdgeIndexedGraph.maderSplit_new_right,
            Finset.mem_insert, Finset.mem_singleton] at hz' ⊢
          rcases hz' with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
  terminal_split_support_two := by
    intro e w hlabel hleft hright
    cases e with
    | inl e =>
        exact R.terminal_split_support_two e.1 w hlabel hleft hright
    | inr u =>
        rw [R.history.split_routeEdges_new p u]
        have hdisjoint :=
          R.history.routeEdges_pairwise_disjoint p.edge_ne
        change Disjoint (R.history.routeEdges p.first)
          (R.history.routeEdges p.second) at hdisjoint
        rw [Finset.card_union_of_disjoint hdisjoint]
        have hfirst := R.history.routeEdges_nonempty p.first
        have hsecond := R.history.routeEdges_nonempty p.second
        exact Nat.add_le_add
          (Finset.one_le_card.mpr hfirst)
          (Finset.one_le_card.mpr hsecond)

end MaderGroupedHistory

/-! ## Iteration through one center -/

namespace MaderEvenDecomposition

/-- Carry a grouped history through a complete split-off at one center. -/
noncomputable def groupedHistory
    {normal H : FiniteEdgeIndexedGraph W} {terminals : Finset W} {s : W}
    (hs : s ∉ terminals)
    (D : MaderEvenDecomposition s H)
    (R : MaderGroupedHistory normal H terminals)
    (hedges : ∀ e : H.Edge,
      H.left e ∈ terminals ∨ H.right e ∈ terminals) :
    MaderGroupedHistory normal D.finalGraph terminals :=
  match D with
  | .done _ _ => R
  | .step _ p _ tail =>
      tail.groupedHistory hs (R.split hs hedges p)
        (every_edge_incident_terminal_maderSplit hedges hs p)

end MaderEvenDecomposition

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
