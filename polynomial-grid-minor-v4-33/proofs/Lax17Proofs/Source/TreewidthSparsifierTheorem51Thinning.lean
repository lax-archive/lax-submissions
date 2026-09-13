import Lax17Proofs.Source.TreewidthSparsifierThinningOutcome

namespace Lax17Proofs

universe u v w

/-!
# Simultaneous quotient-cut preservation

This module applies the finite thinning estimate to the whole-rail quotient
constructed from the physical cut-matching transcript.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open ChekuriChuzhoySection5TerminalSkeleton
open ThinningConcentration


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

/-- Physical owner-crossing edges crossing an abstract quotient cut. -/
noncomputable def ownerBoundaryEdges
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) : Finset (Sym2 V) := by
  classical
  exact (ownerCrossingEdges H owner).filter fun e =>
    (owner e.out.1 ∈ S ∧ owner e.out.2 ∉ S) ∨
      (owner e.out.2 ∈ S ∧ owner e.out.1 ∉ S)

@[simp] theorem mem_ownerBoundaryEdges
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) (e : Sym2 V) :
    e ∈ ownerBoundaryEdges H owner S ↔
      e ∈ ownerCrossingEdges H owner ∧
        ((owner e.out.1 ∈ S ∧ owner e.out.2 ∉ S) ∨
          (owner e.out.2 ∈ S ∧ owner e.out.1 ∉ S)) := by
  classical
  simp [ownerBoundaryEdges]

theorem ownerBoundaryEdges_subset_edgeFinset
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) :
    ownerBoundaryEdges H owner S ⊆ H.edgeFinset := by
  intro e he
  have he' :=
    (Finset.mem_filter.mp
      (mem_ownerBoundaryEdges H owner S e |>.mp he).1).1
  simpa only [_root_.SimpleGraph.mem_edgeFinset] using he'

/-- Quotient boundary indices and their physical owner-crossing edges are in
canonical bijection. -/
noncomputable def ownerBoundaryEquiv
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) :
    {q : (ownerQuotient H owner).Edge //
      q ∈ (ownerQuotient H owner).boundary S} ≃
      {e : Sym2 V // e ∈ ownerBoundaryEdges H owner S} where
  toFun q := by
    let e := ownerCrossingEdgeAt H owner q.1
    refine ⟨e, ?_⟩
    rw [mem_ownerBoundaryEdges]
    refine ⟨(ownerCrossingEdges H owner).equivFin.symm q.1 |>.2, ?_⟩
    exact ((ownerQuotient H owner).mem_boundary S q.1).mp q.2
  invFun e := by
    have hecross :
        e.1 ∈ ownerCrossingEdges H owner :=
      (mem_ownerBoundaryEdges H owner S e.1).mp e.2 |>.1
    let q := ownerQuotientIndex H owner e.1 hecross
    refine ⟨q, ?_⟩
    exact ((ownerQuotient H owner).mem_boundary S q).mpr
      (ownerQuotientIndex_crosses H owner S e.1 hecross
        ((mem_ownerBoundaryEdges H owner S e.1).mp e.2 |>.2))
  left_inv q := by
    apply Subtype.ext
    simp [ownerQuotientIndex, ownerCrossingEdgeAt]
  right_inv e := by
    apply Subtype.ext
    simp [ownerQuotientIndex, ownerCrossingEdgeAt]

theorem ownerBoundaryEdges_card
    (H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) :
    (ownerBoundaryEdges H owner S).card =
      ((ownerQuotient H owner).boundary S).card := by
  classical
  calc
    (ownerBoundaryEdges H owner S).card =
        Fintype.card
          {e : Sym2 V // e ∈ ownerBoundaryEdges H owner S} := by
      rw [Fintype.card_coe]
    _ = Fintype.card
        {q : (ownerQuotient H owner).Edge //
          q ∈ (ownerQuotient H owner).boundary S} :=
      Fintype.card_congr (ownerBoundaryEquiv H owner S).symm
    _ = ((ownerQuotient H owner).boundary S).card := by
      rw [Fintype.card_coe]

/-- The part of an ambient physical quotient boundary surviving in a
subgraph.  Keeping the classical edge-set decision inside this definition
avoids exposing a noncanonical `Fintype` instance in theorem statements. -/
noncomputable def survivingOwnerBoundaryEdges
    (K H : _root_.SimpleGraph V) (owner : V → Fin h)
    (S : Finset (Fin h)) : Finset (Sym2 V) := by
  classical
  exact (ownerBoundaryEdges H owner S).filter fun e =>
    e ∈ K.edgeSet

/-- Passing to a spanning subgraph simply filters the physical quotient
boundary by the surviving edge set. -/
theorem ownerBoundaryEdges_of_le
    (K H : _root_.SimpleGraph V) (hKH : K ≤ H)
    (owner : V → Fin h) (S : Finset (Fin h)) :
    ownerBoundaryEdges K owner S =
      survivingOwnerBoundaryEdges K H owner S := by
  classical
  unfold survivingOwnerBoundaryEdges
  ext e
  rw [Finset.mem_filter]
  rw [mem_ownerBoundaryEdges, mem_ownerBoundaryEdges]
  constructor
  · rintro ⟨heK, hcross⟩
    have heKfin :
        e ∈ K.edgeFinset :=
      (Finset.mem_filter.mp heK).1
    have heKset : e ∈ K.edgeSet := by
      simpa only [_root_.SimpleGraph.mem_edgeFinset] using heKfin
    have heHset : e ∈ H.edgeSet :=
      _root_.SimpleGraph.edgeSet_mono hKH heKset
    have heHfin : e ∈ H.edgeFinset := by
      simpa only [_root_.SimpleGraph.mem_edgeFinset] using heHset
    exact
      ⟨⟨Finset.mem_filter.mpr
          ⟨heHfin, (Finset.mem_filter.mp heK).2⟩, hcross⟩,
        heKset⟩
  · rintro ⟨⟨heH, hcross⟩, heKset⟩
    have heKfin : e ∈ K.edgeFinset := by
      simpa only [_root_.SimpleGraph.mem_edgeFinset] using heKset
    exact
      ⟨Finset.mem_filter.mpr
        ⟨heKfin, (Finset.mem_filter.mp heH).2⟩, hcross⟩

/-- The physical retained-edge count is exactly the boundary size in the
whole-rail quotient of the thinned graph. -/
theorem retainedEdgeCount_ownerBoundary
    {H : _root_.SimpleGraph V}
    (I : BlueThinningInput H) (owner : V → Fin h)
    (S : Finset (Fin h))
    (outcome : BlueThinningInput.Outcome (H := H)) :
    retainedEdgeCount I (ownerBoundaryEdges H owner S) outcome =
      ((ownerQuotient (I.thinnedGraph outcome) owner).boundary S).card := by
  classical
  rw [← ownerBoundaryEdges_card]
  rw [ownerBoundaryEdges_of_le
    (I.thinnedGraph outcome) H (I.thinnedGraph_le outcome)]
  unfold retainedEdgeCount
  rfl

namespace BuildState.ExpanderBlocks

/-- Every owner-crossing edge of the assembled support is blue: red edges
have equal rail owners. -/
theorem ownerBoundaryEdges_blue
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h))
    (e : Sym2 V)
    (he : e ∈ ownerBoundaryEdges
      (E.assembledSupport hbudget)
      (E.railOwner hbudget fallback) S)
    (heH : e ∈ (E.assembledSupport hbudget).edgeSet) :
    (⟨e, heH⟩ :
        (E.assembledSupport hbudget).edgeSet) ∈
      (E.blueThinningInput hbudget).blue := by
  classical
  have howners :
      E.railOwner hbudget fallback e.out.1 ≠
        E.railOwner hbudget fallback e.out.2 := by
    exact Finset.mem_filter.mp
      ((mem_ownerBoundaryEdges
        (E.assembledSupport hbudget)
        (E.railOwner hbudget fallback) S e).mp he).1 |>.2
  have hadj :
      (E.assembledSupport hbudget).Adj e.out.1 e.out.2 := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk] using heH
  have hblueAdj : E.blueSupport.Adj e.out.1 e.out.2 := by
    rcases hadj with hred | hblue
    · exact False.elim
        (howners
          (E.railOwner_eq_of_redSupport_adj
            hbudget fallback hred))
    · exact hblue
  change
    (⟨e, heH⟩ :
      (E.assembledSupport hbudget).edgeSet) ∈
      edgesOfSubgraph
        (E.assembledSupport hbudget) E.blueSupport
        (by exact le_sup_right)
  rw [mem_edgesOfSubgraph]
  change e ∈ E.blueSupport.edgeSet
  rw [← show s(e.out.1, e.out.2) = e by
    rw [Sym2.mk, e.out_eq]]
  rw [_root_.SimpleGraph.mem_edgeSet]
  exact hblueAdj

/-- For a fixed quotient cut, fewer than a `1/128` fraction of its physical
crossing edges survive only on the exponentially small set of outcomes
supplied by the thinning estimate. -/
theorem quotientBoundary_bad_mul_failureFactor_le_total
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) (S : Finset (Fin h)) :
    let H := E.assembledSupport hbudget
    let owner := E.railOwner hbudget fallback
    let I := E.blueThinningInput hbudget
    let t := ((ownerQuotient H owner).boundary S).card / 128
    ((Finset.univ.filter fun outcome :
        BlueThinningInput.Outcome (H := H) =>
          ((ownerQuotient (I.thinnedGraph outcome) owner).boundary S).card <
            t).card) *
        4 ^ (t + 1) ≤
      Fintype.card (BlueThinningInput.Outcome (H := H)) := by
  classical
  dsimp only
  have hfixed :=
    retainedEdgeCount_bad_mul_failureFactor_le_total
      (E.blueThinningInput hbudget)
      (ownerBoundaryEdges
        (E.assembledSupport hbudget)
        (E.railOwner hbudget fallback) S)
      (ownerBoundaryEdges_subset_edgeFinset
        (E.assembledSupport hbudget)
        (E.railOwner hbudget fallback) S)
      (E.ownerBoundaryEdges_blue hbudget fallback S)
  rw [ownerBoundaryEdges_card] at hfixed
  simpa only [retainedEdgeCount_ownerBoundary] using hfixed

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
