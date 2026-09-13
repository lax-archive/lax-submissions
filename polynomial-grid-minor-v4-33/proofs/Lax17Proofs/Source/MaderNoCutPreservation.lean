import Lax17Proofs.Source.MaderDangerous

namespace Lax17Proofs

universe u v w

/-!
# Preservation of non-cut center edges under admissible splitting

At an even-degree center, a nonempty incidence set after one split has at
least two copies.  Two such copies force local connectivity at least two
between their other endpoints; admissibility then rules out either copy
becoming a named cut edge.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- An incident named edge together with its endpoint other than the center. -/
structure CenterEdge (H : FiniteEdgeIndexedGraph W) (s : W) where
  edge : H.Edge
  other : W
  ends :
    (H.left edge = s ∧ H.right edge = other) ∨
      (H.right edge = s ∧ H.left edge = other)

namespace CenterEdge

theorem edge_mem_incidentEdges {H : FiniteEdgeIndexedGraph W} {s : W}
    (e : H.CenterEdge s) : e.edge ∈ H.incidentEdges s := by
  rw [H.mem_incidentEdges]
  rcases e.ends with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem other_ne_center {H : FiniteEdgeIndexedGraph W} {s : W}
    (e : H.CenterEdge s) : e.other ≠ s := by
  rcases e.ends with h | h
  · intro heq
    exact H.end_ne e.edge (h.1.trans (h.2.trans heq).symm)
  · intro heq
    exact H.end_ne e.edge ((h.2.trans heq).trans h.1.symm)

theorem crosses_iff_of_center_not_mem
    {H : FiniteEdgeIndexedGraph W} {s : W} (e : H.CenterEdge s)
    {X : Finset W} (hs : s ∉ X) :
    H.Crosses X e.edge ↔ e.other ∈ X := by
  rcases e.ends with h | h <;> simp [Crosses, h.1, h.2, hs]

end CenterEdge

/-- Recover the other endpoint of an arbitrary named incident copy. -/
noncomputable def incidentCenterEdge (H : FiniteEdgeIndexedGraph W) (s : W)
    (e : H.incidentEdges s) : H.CenterEdge s := by
  classical
  by_cases hleft : H.left e.1 = s
  · exact ⟨e.1, H.right e.1, Or.inl ⟨hleft, rfl⟩⟩
  · have hright : H.right e.1 = s :=
      ((H.mem_incidentEdges s e.1).mp e.2).resolve_left hleft
    exact ⟨e.1, H.left e.1, Or.inr ⟨hright, rfl⟩⟩

@[simp] theorem incidentCenterEdge_edge
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : H.incidentEdges s) :
    (H.incidentCenterEdge s e).edge = e.1 := by
  classical
  simp only [incidentCenterEdge]
  split <;> rfl

theorem maderSplit_incidentEdge_is_old
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (e : (H.maderSplit p).Edge) (he : e ∈ (H.maderSplit p).incidentEdges s) :
    ∃ old : {g : H.Edge // g ≠ p.first ∧ g ≠ p.second}, e = Sum.inl old := by
  rcases e with old | new
  · exact ⟨old, rfl⟩
  · have hinc := ((H.maderSplit p).mem_incidentEdges s (Sum.inr new)).mp he
    simp only [maderSplit_new_left, maderSplit_new_right] at hinc
    exact (hinc.elim p.firstOther_ne_center p.secondOther_ne_center).elim

/-- Two distinct center copies with distinct other endpoints have local edge
connectivity at least two when no center copy is a named cut edge. -/
theorem pairwiseEdgeConnectedAtLeast_two_of_centerEdges
    {H : FiniteEdgeIndexedGraph W} {s : W} (hno : H.NoIncidentCutEdge s)
    (e f : H.CenterEdge s) (hef : e.edge ≠ f.edge)
    (hother : e.other ≠ f.other) :
    H.PairwiseEdgeConnectedAtLeast e.other f.other 2 := by
  intro X heX hfX
  by_cases hs : s ∈ X
  · have hcross : H.Crosses X f.edge := by
      rcases f.ends with h | h
      · exact Or.inl ⟨by simpa [h.1] using hs, by simpa [h.2] using hfX⟩
      · exact Or.inr ⟨by simpa [h.1] using hs, by simpa [h.2] using hfX⟩
    have hmem : f.edge ∈ H.boundary X := (H.mem_boundary X f.edge).2 hcross
    exact hno.two_le_boundary f.edge_mem_incidentEdges hmem
  · have hcross : H.Crosses X e.edge :=
      (e.crosses_iff_of_center_not_mem hs).2 heX
    have hmem : e.edge ∈ H.boundary X := (H.mem_boundary X e.edge).2 hcross
    exact hno.two_le_boundary e.edge_mem_incidentEdges hmem

/-- An admissible split preserves the no-incident-cut-edge hypothesis whenever
the remaining center degree is either zero or at least two. -/
theorem maderAdmissible_preserves_noIncidentCutEdge
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (hno : H.NoIncidentCutEdge s) (hadm : H.MaderAdmissible p)
    (hdegree : (H.maderSplit p).degree s = 0 ∨
      2 ≤ (H.maderSplit p).degree s) :
    (H.maderSplit p).NoIncidentCutEdge s := by
  intro e heInc hcut
  rcases hdegree with hzero | htwo
  · have : (H.maderSplit p).incidentEdges s = ∅ :=
      Finset.card_eq_zero.mp (by simpa [degree] using hzero)
    simpa [this] using heInc
  · classical
    let eSub : (H.maderSplit p).incidentEdges s := ⟨e, heInc⟩
    have herase :
        (((H.maderSplit p).incidentEdges s).erase e).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem heInc]
      simpa [degree] using (show 0 < (H.maderSplit p).degree s - 1 by omega)
    rcases herase with ⟨f, hfErase⟩
    have hfInc : f ∈ (H.maderSplit p).incidentEdges s :=
      Finset.mem_of_mem_erase hfErase
    have hfe : f ≠ e := Finset.ne_of_mem_erase hfErase
    let fSub : (H.maderSplit p).incidentEdges s := ⟨f, hfInc⟩
    let ce := (H.maderSplit p).incidentCenterEdge s eSub
    let cf := (H.maderSplit p).incidentCenterEdge s fSub
    have hceEdge : ce.edge = e := by simp [ce, eSub]
    have hcfEdge : cf.edge = f := by simp [cf, fSub]
    have hedge : ce.edge ≠ cf.edge := by
      intro h
      exact hfe (hcfEdge.symm.trans (h.symm.trans hceEdge))
    rcases hcut with ⟨X, hboundary⟩
    have heBoundary : e ∈ (H.maderSplit p).boundary X := by simp [hboundary]
    have heCross := ((H.maderSplit p).mem_boundary X e).mp heBoundary
    have hfNotBoundary : cf.edge ∉ (H.maderSplit p).boundary X := by
      rw [hboundary]
      simp [hcfEdge, hceEdge, hfe]
    have hfNotCross : ¬ (H.maderSplit p).Crosses X cf.edge := by
      simpa only [(H.maderSplit p).mem_boundary] using hfNotBoundary
    by_cases hsame : ce.other = cf.other
    · have hfCross : (H.maderSplit p).Crosses X cf.edge := by
        simp only [Crosses] at heCross ⊢
        rcases ce.ends with he | he <;> rcases cf.ends with hf | hf <;>
          simp_all only [hceEdge, hcfEdge] <;> tauto
      exact hfNotCross hfCross
    · have hpreTwo : H.PairwiseEdgeConnectedAtLeast ce.other cf.other 2 := by
        rcases H.maderSplit_incidentEdge_is_old p ce.edge
            ce.edge_mem_incidentEdges with ⟨ceOld, hceOldEq⟩
        rcases H.maderSplit_incidentEdge_is_old p cf.edge
            cf.edge_mem_incidentEdges with ⟨cfOld, hcfOldEq⟩
        apply H.pairwiseEdgeConnectedAtLeast_two_of_centerEdges hno
          { edge := ceOld.1
            other := ce.other
            ends := by
              rcases ce.ends with h | h
              · exact Or.inl ⟨by simpa [hceOldEq] using h.1,
                  by simpa [hceOldEq] using h.2⟩
              · exact Or.inr ⟨by simpa [hceOldEq] using h.1,
                  by simpa [hceOldEq] using h.2⟩ }
          { edge := cfOld.1
            other := cf.other
            ends := by
              rcases cf.ends with h | h
              · exact Or.inl ⟨by simpa [hcfOldEq] using h.1,
                  by simpa [hcfOldEq] using h.2⟩
              · exact Or.inr ⟨by simpa [hcfOldEq] using h.1,
                  by simpa [hcfOldEq] using h.2⟩ }
          (by
            intro h
            apply hedge
            rw [hceOldEq, hcfOldEq]
            exact congrArg Sum.inl (Subtype.ext h)) hsame
      have hpostTwo :
          (H.maderSplit p).PairwiseEdgeConnectedAtLeast ce.other cf.other 2 :=
        (hadm ce.other cf.other ce.other_ne_center cf.other_ne_center hsame 2).1
          hpreTwo
      by_cases hsX : s ∈ X
      · have hsCompl : s ∉ Xᶜ := by simp [hsX]
        have hceCrossCompl : (H.maderSplit p).Crosses Xᶜ ce.edge := by
          rw [(H.maderSplit p).crosses_compl]
          simpa [hceEdge] using heCross
        have hceOutside : ce.other ∉ X := by
          have := (ce.crosses_iff_of_center_not_mem hsCompl).mp hceCrossCompl
          simpa using this
        have hcfInside : cf.other ∈ X := by
          by_contra hcf
          have hcfCrossCompl : (H.maderSplit p).Crosses Xᶜ cf.edge :=
            (cf.crosses_iff_of_center_not_mem hsCompl).2 (by simpa using hcf)
          exact hfNotCross (((H.maderSplit p).crosses_compl X cf.edge).mp hcfCrossCompl)
        have hcutTwo := hpostTwo Xᶜ (by simpa using hceOutside) (by simpa using hcfInside)
        simpa [hboundary] using hcutTwo
      · have hceInside : ce.other ∈ X := by
          exact (ce.crosses_iff_of_center_not_mem hsX).mp (by simpa [hceEdge] using heCross)
        have hcfOutside : cf.other ∉ X := by
          intro hcf
          exact hfNotCross (cf.crosses_iff_of_center_not_mem hsX |>.2 hcf)
        have hcutTwo := hpostTwo X hceInside hcfOutside
        simpa [hboundary] using hcutTwo

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
