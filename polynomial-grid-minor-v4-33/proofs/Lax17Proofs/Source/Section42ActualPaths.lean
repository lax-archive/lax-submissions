import Lax17Proofs.Source.Theorem46
import Lax17Proofs.Source.Observation44Reduction

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4.2 with the actual retained paths

This module combines the source-faithful contraction proof of Observation 4.4
with Theorem 4.6.  It is deliberately downstream of both modules, avoiding a
dependency cycle through the later Section 4 files.
-/

namespace SimpleGraph


namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D M w : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- Source-faithful Observation 4.4 plus Theorem 4.6.  In contrast with the
older contact-vertex shortcut, `Qpack` consists of the actual retained
subpaths of the original auxiliary packing, and Property I1 is preserved
quantitatively. -/
theorem section42_slicing_minor_of_pseudoGrid_actualPaths
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤ Gamma.goodQSet.card) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          ∃ sigma : PathSlicing R M,
            IsMinor H G ∧
              MaxDegreeAtMost H 4 ∧
              R.IsUniqueLinkage ∧
                R.card = Gamma.rowPacking.card ∧
                  Qpack.card = Gamma.goodQSet.card ∧
                    (∀ q : Qpack.Index,
                      D ≤
                        ((Finset.univ : Finset R.Index).filter fun r =>
                          ¬ Disjoint (Qpack.path q).vertexSet
                            (R.path r).vertexSet).card) ∧
                      sigma.WidthAtLeast Qpack w := by
  classical
  have hgoodPos : 0 < Gamma.goodQSet.card := by
    have hMw : 0 < M * w := Nat.mul_pos hM hw
    exact hMw.trans_le
      ((Nat.le_add_right (M * w)
        ((M + 1) * Gamma.rowPacking.card)).trans hcard)
  have hgood : Gamma.goodQSet.Nonempty := Finset.card_pos.mp hgoodPos
  have hN : 0 < Gamma.rowPacking.card := by
    have hDle := Gamma.depth_le_reservedUnion_card_of_goodQSet_nonempty hgood
    have hrowCard :
        Gamma.rowPacking.card = Gamma.reservedUnion.card :=
      Gamma.rowPacking_card
    omega
  rcases
      Section4Reduction.PseudoGrid.exists_observation44_reduced_state
        Gamma hminimal hD with
    ⟨State, hReduced⟩
  let H := State.reducedGraph hReduced
  let R := State.reducedRow hReduced
  let Qpack := State.reducedRetained hReduced
  have hunique : R.IsUniqueLinkage := by
    simpa [R] using State.reducedRow_isUniqueLinkage hReduced hN
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage R Qpack := by
    simpa [R, Qpack] using
      State.reducedRetained_intersects_reducedRow hReduced hD
  have hRcard : R.card = Gamma.rowPacking.card := by
    simp [R]
  have hQcard : Qpack.card = Gamma.goodQSet.card := by
    calc
      Qpack.card = Gamma.goodQPathPacking.card := by
        exact State.reducedRetained_card hReduced
      _ = Gamma.goodQSet.card := Gamma.goodQPathPacking_card
  have hcard' : M * w + (M + 1) * R.card ≤ Qpack.card := by
    calc
      M * w + (M + 1) * R.card =
          M * w + (M + 1) * Gamma.rowPacking.card := by rw [hRcard]
      _ ≤ Gamma.goodQSet.card := hcard
      _ = Qpack.card := hQcard.symm
  rcases
      PathSlicing.theorem46 R Qpack M w hM hw hunique hintersects hcard' with
    ⟨sigma, hwidth⟩
  refine
    ⟨State.RowVertex, inferInstance, inferInstance, H,
      PathPacking.subtypeFinset State.Arow
        State.row.toPathPacking.vertexSet State.Arow_subset_row_vertexSet,
      PathPacking.subtypeFinset State.Brow
        State.row.toPathPacking.vertexSet State.Brow_subset_row_vertexSet,
      Finset.univ, Finset.univ, R, Qpack, sigma, ?_, ?_, hunique, hRcard,
      hQcard, ?_, hwidth⟩
  · simpa [H] using State.reducedGraph_isMinor hReduced
  · simpa [H] using State.reducedGraph_maxDegreeAtMost_four hReduced
  · intro q
    simpa [R, Qpack] using
      State.reducedRetained_metRows_card hReduced q

end PseudoGrid

end SimpleGraph

end Lax17Proofs
