import Lax17Proofs.Source.ChekuriChuzhoySection5SplitOff

namespace Lax17Proofs

universe u v w

/-!
# Exact named-multigraph cut identities for Mader split-off

This module records the exact cut bookkeeping used around Mader's split-off
operation.  All corrections count named edge copies, so parallel edges retain
their multiplicity.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Named edges between two vertex sets -/

/-- Named edge copies with one endpoint in `A` and the other in `B`.
The definition is symmetric in the endpoint order stored by the graph. -/
noncomputable def edgesBetween (H : FiniteEdgeIndexedGraph W)
    (A B : Finset W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (H.left e ∈ A ∧ H.right e ∈ B) ∨
      (H.right e ∈ A ∧ H.left e ∈ B)

@[simp] theorem mem_edgesBetween (H : FiniteEdgeIndexedGraph W)
    (A B : Finset W) (e : H.Edge) :
    e ∈ H.edgesBetween A B ↔
      (H.left e ∈ A ∧ H.right e ∈ B) ∨
        (H.right e ∈ A ∧ H.left e ∈ B) := by
  simp [edgesBetween]

/-- The `0`--`1` contribution of a named edge to a cut. -/
private noncomputable def cutIndicator (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) (e : H.Edge) : Nat := by
  classical
  exact if H.Crosses X e then 1 else 0

private theorem boundary_card_eq_sum_cutIndicator
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    (H.boundary X).card = ∑ e : H.Edge, cutIndicator H X e := by
  classical
  rw [boundary, Finset.card_filter]
  simp [cutIndicator]

private theorem edgesBetween_card_eq_sum_indicator
    (H : FiniteEdgeIndexedGraph W) (A B : Finset W) :
    (H.edgesBetween A B).card =
      ∑ e : H.Edge, if e ∈ H.edgesBetween A B then 1 else 0 := by
  classical
  rw [edgesBetween, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp [edgesBetween]

/-! ## Exact boundary behavior of one Mader split -/

private theorem maderSplit_boundary_indicator_sum
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) :
    ((H.maderSplit p).boundary X).card =
      ∑ e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second},
          cutIndicator H X e.1 +
        (if p.firstOther ≠ p.secondOther ∧
            ((p.firstOther ∈ X ∧ p.secondOther ∉ X) ∨
              (p.secondOther ∈ X ∧ p.firstOther ∉ X)) then 1 else 0) := by
  classical
  rw [boundary_card_eq_sum_cutIndicator]
  change (∑ e :
      {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
        {u : Unit // p.firstOther ≠ p.secondOther},
      cutIndicator (H.maderSplit p) X e) = _
  rw [Fintype.sum_sum_type]
  have hold :
      (∑ e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second},
          cutIndicator (H.maderSplit p) X (Sum.inl e)) =
        ∑ e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second},
          cutIndicator H X e.1 := by
    apply Finset.sum_congr rfl
    intro e _
    simp [cutIndicator, Crosses]
  rw [hold]
  congr 1
  by_cases hother : p.firstOther ≠ p.secondOther
  · letI : Unique {u : Unit // p.firstOther ≠ p.secondOther} :=
      { default := ⟨(), hother⟩
        uniq := fun u => Subtype.ext (Subsingleton.elim u.1 ()) }
    rw [Fintype.sum_unique]
    simp [cutIndicator, Crosses, hother]
  · simp [hother]

private theorem original_boundary_indicator_sum
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) :
    (H.boundary X).card =
      ∑ e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second},
          cutIndicator H X e.1 +
        cutIndicator H X p.first + cutIndicator H X p.second := by
  classical
  rw [boundary_card_eq_sum_cutIndicator]
  have hfirst : p.first ∈ (Finset.univ : Finset H.Edge) := Finset.mem_univ _
  have hsecond : p.second ∈ (Finset.univ.erase p.first : Finset H.Edge) := by
    simp [p.edge_ne.symm]
  calc
    ∑ e : H.Edge, cutIndicator H X e =
        (∑ e ∈ (Finset.univ.erase p.first).erase p.second,
          cutIndicator H X e) +
          cutIndicator H X p.second + cutIndicator H X p.first := by
      rw [← Finset.sum_erase_add _ _ hfirst,
        ← Finset.sum_erase_add _ _ hsecond]
    _ = (∑ e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second},
          cutIndicator H X e.1) +
          cutIndicator H X p.first + cutIndicator H X p.second := by
      rw [Finset.sum_subtype
        ((Finset.univ.erase p.first).erase p.second)
        (p := fun e => e ≠ p.first ∧ e ≠ p.second)
        (fun e => by simp [and_comm]) (cutIndicator H X)]
      omega

private theorem splitPair_first_crosses_of_center_not_mem
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X) :
    H.Crosses X p.first ↔ p.firstOther ∈ X := by
  rcases p.first_ends with h | h <;>
    simp [Crosses, h.1, h.2, hs]

private theorem splitPair_second_crosses_of_center_not_mem
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X) :
    H.Crosses X p.second ↔ p.secondOther ∈ X := by
  rcases p.second_ends with h | h <;>
    simp [Crosses, h.1, h.2, hs]

/-- Exact additive form of the split-off cut change away from the center.
The old cut has two additional named edges exactly when both other endpoints
lie in `X`; in every other membership configuration the cardinalities agree.
This includes the equal-other-endpoint case, where the would-be loop is
discarded. -/
theorem boundary_card_maderSplit_add_two_iff
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X) :
    (H.boundary X).card =
      ((H.maderSplit p).boundary X).card +
        if p.firstOther ∈ X ∧ p.secondOther ∈ X then 2 else 0 := by
  classical
  rw [original_boundary_indicator_sum H p X,
    maderSplit_boundary_indicator_sum H p X]
  have hfirst := splitPair_first_crosses_of_center_not_mem H p X hs
  have hsecond := splitPair_second_crosses_of_center_not_mem H p X hs
  by_cases h₁ : p.firstOther ∈ X
  · by_cases h₂ : p.secondOther ∈ X
    · simp [cutIndicator, hfirst, hsecond, h₁, h₂]
    · have hother : p.firstOther ≠ p.secondOther := by
        intro heq
        exact h₂ (by simpa [heq] using h₁)
      simp [cutIndicator, hfirst, hsecond, h₁, h₂, hother]
  · by_cases h₂ : p.secondOther ∈ X
    · have hother : p.firstOther ≠ p.secondOther := by
        intro heq
        exact h₁ (by simpa [heq] using h₂)
      simp [cutIndicator, hfirst, hsecond, h₁, h₂, hother]
    · simp [cutIndicator, hfirst, hsecond, h₁, h₂]

/-- If both other endpoints lie in `X`, splitting drops the cut cardinality by
exactly two.  This remains true when those endpoints coincide and no loop is
stored. -/
theorem maderSplit_boundary_card_of_both_mem
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X)
    (hfirst : p.firstOther ∈ X) (hsecond : p.secondOther ∈ X) :
    ((H.maderSplit p).boundary X).card = (H.boundary X).card - 2 := by
  have h := boundary_card_maderSplit_add_two_iff H p X hs
  simp [hfirst, hsecond] at h
  omega

/-- Unless both other endpoints lie in `X`, splitting leaves the cut
cardinality unchanged. -/
theorem maderSplit_boundary_card_of_not_both_mem
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X)
    (hnot : ¬ (p.firstOther ∈ X ∧ p.secondOther ∈ X)) :
    ((H.maderSplit p).boundary X).card = (H.boundary X).card := by
  simpa [hnot] using (boundary_card_maderSplit_add_two_iff H p X hs).symm

/-! ## Exact undirected cut identities -/

/-- Correction edges for the union/intersection identity: named edges joining
the two opposite parts `X \ Y` and `Y \ X`. -/
noncomputable def unionInterCorrectionEdges (H : FiniteEdgeIndexedGraph W)
    (X Y : Finset W) : Finset H.Edge :=
  H.edgesBetween (X \ Y) (Y \ X)

/-- Correction edges for the two-differences identity: named edges joining
`X ∩ Y` to the outside of `X ∪ Y`. -/
noncomputable def sdiffCorrectionEdges (H : FiniteEdgeIndexedGraph W)
    (X Y : Finset W) : Finset H.Edge :=
  H.edgesBetween (X ∩ Y) (X ∪ Y)ᶜ

private theorem cutIndicator_union_inter_pointwise
    (H : FiniteEdgeIndexedGraph W) (X Y : Finset W) (e : H.Edge) :
    cutIndicator H X e + cutIndicator H Y e =
      cutIndicator H (X ∩ Y) e + cutIndicator H (X ∪ Y) e +
        2 * (if e ∈ H.unionInterCorrectionEdges X Y then 1 else 0) := by
  by_cases hlX : H.left e ∈ X <;> by_cases hrX : H.right e ∈ X <;>
    by_cases hlY : H.left e ∈ Y <;> by_cases hrY : H.right e ∈ Y <;>
      simp [cutIndicator, Crosses, unionInterCorrectionEdges, hlX, hrX, hlY, hrY]

private theorem cutIndicator_sdiff_pointwise
    (H : FiniteEdgeIndexedGraph W) (X Y : Finset W) (e : H.Edge) :
    cutIndicator H X e + cutIndicator H Y e =
      cutIndicator H (X \ Y) e + cutIndicator H (Y \ X) e +
        2 * (if e ∈ H.sdiffCorrectionEdges X Y then 1 else 0) := by
  by_cases hlX : H.left e ∈ X <;> by_cases hrX : H.right e ∈ X <;>
    by_cases hlY : H.left e ∈ Y <;> by_cases hrY : H.right e ∈ Y <;>
      simp [cutIndicator, Crosses, sdiffCorrectionEdges, hlX, hrX, hlY, hrY]

/-- Exact union/intersection cut identity for an undirected named multigraph.
The correction counts parallel edge copies between the opposite differences. -/
theorem boundary_union_inter_card_identity
    (H : FiniteEdgeIndexedGraph W) (X Y : Finset W) :
    (H.boundary X).card + (H.boundary Y).card =
      (H.boundary (X ∩ Y)).card + (H.boundary (X ∪ Y)).card +
        2 * (H.unionInterCorrectionEdges X Y).card := by
  classical
  rw [boundary_card_eq_sum_cutIndicator H X,
    boundary_card_eq_sum_cutIndicator H Y,
    boundary_card_eq_sum_cutIndicator H (X ∩ Y),
    boundary_card_eq_sum_cutIndicator H (X ∪ Y)]
  rw [unionInterCorrectionEdges,
    edgesBetween_card_eq_sum_indicator H (X \ Y) (Y \ X)]
  change (∑ e : H.Edge, cutIndicator H X e) +
      (∑ e : H.Edge, cutIndicator H Y e) =
    (∑ e : H.Edge, cutIndicator H (X ∩ Y) e) +
      (∑ e : H.Edge, cutIndicator H (X ∪ Y) e) +
        2 * (∑ e : H.Edge,
          if e ∈ H.unionInterCorrectionEdges X Y then 1 else 0)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ =>
    cutIndicator_union_inter_pointwise H X Y e

/-- Exact two-differences cut identity for an undirected named multigraph.
The correction counts parallel edge copies from the intersection to outside
the union. -/
theorem boundary_sdiff_card_identity
    (H : FiniteEdgeIndexedGraph W) (X Y : Finset W) :
    (H.boundary X).card + (H.boundary Y).card =
      (H.boundary (X \ Y)).card + (H.boundary (Y \ X)).card +
        2 * (H.sdiffCorrectionEdges X Y).card := by
  classical
  rw [boundary_card_eq_sum_cutIndicator H X,
    boundary_card_eq_sum_cutIndicator H Y,
    boundary_card_eq_sum_cutIndicator H (X \ Y),
    boundary_card_eq_sum_cutIndicator H (Y \ X)]
  rw [sdiffCorrectionEdges,
    edgesBetween_card_eq_sum_indicator H (X ∩ Y) (X ∪ Y)ᶜ]
  change (∑ e : H.Edge, cutIndicator H X e) +
      (∑ e : H.Edge, cutIndicator H Y e) =
    (∑ e : H.Edge, cutIndicator H (X \ Y) e) +
      (∑ e : H.Edge, cutIndicator H (Y \ X) e) +
        2 * (∑ e : H.Edge,
          if e ∈ H.sdiffCorrectionEdges X Y then 1 else 0)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ =>
    cutIndicator_sdiff_pointwise H X Y e

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
