import Lax17Proofs.Source.Exponent7.AmortizedPipeline
import Lax17Proofs.Source.Exponent8.RootedSection42
import Lax17Proofs.Source.MinorTransitivity

namespace Lax17Proofs

/-!
# Amortized pseudo-grid exit

In the no-crossbar branch, rooted Observation 4.4 and Theorem 4.6 construct
the initial slicing. The amortized Section 5 controller then produces a grid
minor, which is transferred through the contraction minor model.
-/

namespace SimpleGraph
namespace Exponent7

open Exponent8 Section4Reduction

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}
variable {q D ell g reserve : ℕ}

/-- The complete no-crossbar pseudo-grid branch, conditional only on the clean
prescribed-matching dichotomy. -/
theorem gridMinor_of_pseudoGrid_noCrossbar
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    (Gamma : PseudoGrid G A B X q D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hNlower : 64 * q ^ 4 ≤ Gamma.rowPacking.card)
    (hNupper : Gamma.rowPacking.card ≤ 64 * q ^ 6)
    (hDscale : 64 * q ^ 4 ≤ D)
    (hgood :
      exponentSevenUniformSlices q ell *
            Gamma.rowPacking.card +
          (exponentSevenUniformSlices q ell + 1) *
            Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2)))
    (hell : 0 < ell)
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hreserve : 0 < reserve)
    (hscaledWidth :
      20000 * (reserve * g ^ 2) ≤ q ^ 2) :
    ContainsGridMinor G g := by
  have hNpos : 0 < Gamma.rowPacking.card := by
    have : 0 < 64 * q ^ 4 := by positivity
    exact this.trans_le hNlower
  have hMpos :
      0 < exponentSevenUniformSlices q ell :=
    exponentSevenUniformSlices_pos hell
  have hDpos : 0 < D := by
    have : 0 < 64 * q ^ 4 := by positivity
    exact this.trans_le hDscale
  have hDhatPos : 0 < 32 * q ^ 4 := by positivity
  have hmass :
      2 * Gamma.rowPacking.card * (4 * q ^ 2) ≤
        (32 * q ^ 4) * Gamma.rowPacking.card := by
    have hsmall : 2 * (4 * q ^ 2) ≤ 32 * q ^ 4 := by
      have hq2 : 1 ≤ q ^ 2 :=
        Nat.one_le_pow 2 q (by omega)
      nlinarith
    calc
      2 * Gamma.rowPacking.card * (4 * q ^ 2) =
          Gamma.rowPacking.card * (2 * (4 * q ^ 2)) := by ring
      _ ≤ Gamma.rowPacking.card * (32 * q ^ 4) :=
        Nat.mul_le_mul_left Gamma.rowPacking.card hsmall
      _ = (32 * q ^ 4) * Gamma.rowPacking.card := by ring
  obtain ⟨Root, hReduced, ⟨L0⟩⟩ :=
    exists_initialRecursiveSliceLayer_of_pseudoGrid
      Gamma hminimal hDpos hMpos hNpos hgood
      hDhatPos
      (by
        simpa only [show 2 * (32 * q ^ 4) = 64 * q ^ 4 by ring]
          using hDscale)
      hmass hXdisjoint
  let H := Root.state.reducedGraph hReduced
  let Rbar := Root.state.reducedRow hReduced
  let Qbar := Root.state.reducedRetained hReduced
  have hRcard :
      Rbar.card = Gamma.rowPacking.card := by
    simp [Rbar]
  have hRlower : 64 * q ^ 4 ≤ Rbar.card := by
    simpa [hRcard] using hNlower
  have hRupper : Rbar.card ≤ 64 * q ^ 6 := by
    simpa [hRcard] using hNupper
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar := by
    simpa [Rbar, Qbar] using
      Root.state.reducedRetained_intersects_reducedRow hReduced hDpos
  let C :=
    Root.recursiveSlicingContext
      hReduced hNpos hDhatPos
        (by
          simpa only [show 2 * (32 * q ^ 4) = 64 * q ^ 4 by ring]
            using hDscale)
        hXdisjoint
  let L0' : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices q ell)
      Rbar.card (4 * q ^ 2) (32 * q ^ 4) := by
    simpa [H, Rbar, Qbar, hRcard] using L0
  have hgrid : ContainsGridMinor H g :=
    gridMinor_of_uniformAmortizedPipeline
      hDichotomy C L0' hintersects
      (by
        simpa [H] using
          Root.state.reducedGraph_maxDegreeAtMost_four hReduced)
      hq hpow hell hRlower hRupper hnoCrossbar
      hg hlen hreserve hscaledWidth
  exact ContainsGridMinor.of_minor hgrid
    (by
      simpa [H] using Root.state.reducedGraph_isMinor hReduced)

end Exponent7
end SimpleGraph

end Lax17Proofs
