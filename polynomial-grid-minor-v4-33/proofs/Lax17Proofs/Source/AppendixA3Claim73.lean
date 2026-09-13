import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3ClusterSplit
import Lax17Proofs.Source.AppendixA3DeletableEdge
import Lax17Proofs.Source.AppendixA3CutSubmodularity

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Claim 7.3: the cut exposed by deleting an edge

This file formalizes the first step of Claim 7.3 in Chuzhoy's proof of
Theorem 6.3.  It is the cut-counting form of the source's Observation 2.4:
when deleting one edge destroys scaled well-linkedness, a sparse cut can be
oriented toward its smaller terminal side, and the deleted edge crosses it.
-/

namespace SimpleGraph
namespace AppendixA3Claim73


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Deleting one edge removes exactly that edge from every finite cut
boundary.  If the edge does not cross the cut, `erase` leaves the boundary
unchanged. -/
theorem edgeBoundary_deleteEdges_singleton
    (H : _root_.SimpleGraph V) (X Y : Finset V) (e : Sym2 V) :
    Section44.edgeBoundary
        (H.deleteEdges ({e} : Set (Sym2 V))) X Y =
      (Section44.edgeBoundary H X Y).erase e := by
  classical
  ext f
  simp only [Section44.mem_edgeBoundary,
    _root_.SimpleGraph.edgeSet_deleteEdges, Set.mem_diff,
    Set.mem_singleton_iff, Finset.mem_erase]
  tauto

/-- Proof data extracted from the failure of well-linkedness after deleting
one edge.  `A` is oriented to be the side containing no more terminals than
`B`; `deleted_boundary_failure` is the stronger inequality in the graph with
the edge removed. -/
structure DeleteEdgeFailureCut
    (H : _root_.SimpleGraph V) (T : Finset V)
    (alphaNum alphaDen : ℕ) (a b : V) where
  /-- The side with fewer terminals. -/
  A : Finset V
  /-- The other side of the cut. -/
  B : Finset V
  /-- The two sides cover the full vertex set. -/
  cover : A ∪ B = (Finset.univ : Finset V)
  /-- The two sides are disjoint. -/
  disjoint : Disjoint A B
  /-- The cut is oriented toward its smaller terminal side. -/
  terminal_card_le : (A ∩ T).card ≤ (B ∩ T).card
  /-- The strict cut inequality witnessing failure in the deleted graph. -/
  deleted_boundary_failure :
    alphaDen *
          (Section44.edgeBoundary
            (H.deleteEdges ({s(a, b)} : Set (Sym2 V))) A B).card <
      alphaNum * (A ∩ T).card
  /-- The exact relation between the deleted and original cut boundaries. -/
  boundary_after_delete :
    Section44.edgeBoundary
        (H.deleteEdges ({s(a, b)} : Set (Sym2 V))) A B =
      (Section44.edgeBoundary H A B).erase s(a, b)
  /-- The removed pair is an edge of the original graph. -/
  deleted_edge_adj : H.Adj a b
  /-- The deleted edge crosses the selected cut. -/
  deleted_edge_mem_boundary : s(a, b) ∈ Section44.edgeBoundary H A B
  /-- Observation 2.4 in ratio-cleared natural-number form. -/
  source_inequality :
    alphaDen * (Section44.edgeBoundary H A B).card <
      alphaNum * (A ∩ T).card + alphaDen

namespace DeleteEdgeFailureCut

variable {H : _root_.SimpleGraph V} {T : Finset V}
variable {alphaNum alphaDen : ℕ} {a b : V}

/-- The exact boundary relation also gives the corresponding cardinality
equation because the deleted edge crosses the cut. -/
theorem deleted_boundary_card_add_one
    (cut : DeleteEdgeFailureCut H T alphaNum alphaDen a b) :
    (Section44.edgeBoundary
          (H.deleteEdges ({s(a, b)} : Set (Sym2 V))) cut.A cut.B).card + 1 =
      (Section44.edgeBoundary H cut.A cut.B).card := by
  rw [cut.boundary_after_delete]
  exact Finset.card_erase_add_one cut.deleted_edge_mem_boundary

/-- In a partition of `univ`, the second side is the complement of the first. -/
theorem univ_sdiff_A
    (cut : DeleteEdgeFailureCut H T alphaNum alphaDen a b) :
    (Finset.univ : Finset V) \ cut.A = cut.B := by
  calc
    (Finset.univ : Finset V) \ cut.A = (cut.A ∪ cut.B) \ cut.A :=
      congrArg (fun S : Finset V => S \ cut.A) cut.cover.symm
    _ = cut.B := Finset.union_sdiff_cancel_left cut.disjoint

/-- Bridge from the selected two-sided cut to the ambient cluster-boundary
API used by the submodularity and posimodularity inequalities. -/
theorem clusterBoundary_eq_edgeBoundary
    (cut : DeleteEdgeFailureCut H T alphaNum alphaDen a b) :
    Section44.clusterBoundary H cut.A =
      Section44.edgeBoundary H cut.A cut.B := by
  rw [Section44.clusterBoundary, cut.univ_sdiff_A]

/-- The source inequality restated with the one-set boundary consumed by the
two cut inequalities in `AppendixA3CutSubmodularity`. -/
theorem clusterBoundary_source_inequality
    (cut : DeleteEdgeFailureCut H T alphaNum alphaDen a b) :
    alphaDen * (Section44.clusterBoundary H cut.A).card <
      alphaNum * (cut.A ∩ T).card + alphaDen := by
  rw [cut.clusterBoundary_eq_edgeBoundary]
  exact cut.source_inequality

end DeleteEdgeFailureCut

/-- Chuzhoy Claim 7.3 / Observation 2.4, first source-faithful slice.

If deleting an edge destroys scaled cut well-linkedness, the failed cut can be
oriented toward its smaller terminal side.  The deleted edge must cross this
cut: otherwise the exact boundary identity above would make the original and
deleted cut inequalities contradictory. -/
theorem exists_deleteEdgeFailureCut_of_not_scaledEdgeWellLinkedIn_deleteEdges
    (H : _root_.SimpleGraph V) (T : Finset V)
    (alphaNum alphaDen : ℕ) {a b : V}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) T alphaNum alphaDen)
    (hab : H.Adj a b)
    (hfail :
      ¬ Section46.ScaledEdgeWellLinkedIn
        (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
        (Finset.univ : Finset V) T alphaNum alphaDen) :
    Nonempty (DeleteEdgeFailureCut H T alphaNum alphaDen a b) := by
  classical
  let Hdel := H.deleteEdges ({s(a, b)} : Set (Sym2 V))
  have hcutFailure :
      ¬ ∀ X Y : Finset V,
        X ⊆ (Finset.univ : Finset V) →
          Y ⊆ (Finset.univ : Finset V) →
            X ∪ Y = (Finset.univ : Finset V) →
              Disjoint X Y →
                alphaNum * min (X ∩ T).card (Y ∩ T).card ≤
                  alphaDen * (Section44.edgeBoundary Hdel X Y).card := by
    intro hcuts
    apply hfail
    exact ⟨hwell.1, hwell.2.1, hwell.2.2.1, hcuts⟩
  push Not at hcutFailure
  rcases hcutFailure with
    ⟨X, Y, _hX, _hY, hcover, hdisjoint, hdeletedFailure⟩

  have buildCut (A B : Finset V)
      (hABcover : A ∪ B = (Finset.univ : Finset V))
      (hABdisjoint : Disjoint A B)
      (hsmall : (A ∩ T).card ≤ (B ∩ T).card)
      (hdeleted :
        alphaDen * (Section44.edgeBoundary Hdel A B).card <
          alphaNum * (A ∩ T).card) :
      Nonempty (DeleteEdgeFailureCut H T alphaNum alphaDen a b) := by
    have hboundaryAfterDelete :
        Section44.edgeBoundary Hdel A B =
          (Section44.edgeBoundary H A B).erase s(a, b) := by
      simpa [Hdel] using
        edgeBoundary_deleteEdges_singleton H A B s(a, b)
    have hwellCut :
        alphaNum * (A ∩ T).card ≤
          alphaDen * (Section44.edgeBoundary H A B).card := by
      have hmain := hwell.2.2.2 A B (by simp) (by simp)
        hABcover hABdisjoint
      simpa [Nat.min_eq_left hsmall] using hmain
    have hedge : s(a, b) ∈ Section44.edgeBoundary H A B := by
      by_contra hedgeNot
      have hsame :
          Section44.edgeBoundary Hdel A B =
            Section44.edgeBoundary H A B := by
        rw [hboundaryAfterDelete, Finset.erase_eq_of_notMem hedgeNot]
      rw [hsame] at hdeleted
      exact (Nat.not_lt_of_ge hwellCut) hdeleted
    have hcard :
        (Section44.edgeBoundary Hdel A B).card + 1 =
          (Section44.edgeBoundary H A B).card := by
      rw [hboundaryAfterDelete]
      exact Finset.card_erase_add_one hedge
    have hsource :
        alphaDen * (Section44.edgeBoundary H A B).card <
          alphaNum * (A ∩ T).card + alphaDen := by
      calc
        alphaDen * (Section44.edgeBoundary H A B).card =
            alphaDen *
              ((Section44.edgeBoundary Hdel A B).card + 1) := by
          rw [hcard]
        _ = alphaDen * (Section44.edgeBoundary Hdel A B).card +
            alphaDen := by simp [Nat.mul_add]
        _ < alphaNum * (A ∩ T).card + alphaDen :=
          Nat.add_lt_add_right hdeleted alphaDen
    exact ⟨{
      A := A
      B := B
      cover := hABcover
      disjoint := hABdisjoint
      terminal_card_le := hsmall
      deleted_boundary_failure := by simpa [Hdel] using hdeleted
      boundary_after_delete := by simpa [Hdel] using hboundaryAfterDelete
      deleted_edge_adj := hab
      deleted_edge_mem_boundary := hedge
      source_inequality := hsource }⟩

  by_cases hsmall : (X ∩ T).card ≤ (Y ∩ T).card
  · apply buildCut X Y hcover hdisjoint hsmall
    simpa [Nat.min_eq_left hsmall] using hdeletedFailure
  · have hsmall' : (Y ∩ T).card ≤ (X ∩ T).card := by omega
    apply buildCut Y X (by simpa [Finset.union_comm] using hcover)
      hdisjoint.symm hsmall'
    simpa [Hdel, Nat.min_eq_right hsmall',
      Section44.edgeBoundary_comm (G := Hdel) Y X] using hdeletedFailure

end AppendixA3Claim73
end SimpleGraph

end Lax17Proofs
