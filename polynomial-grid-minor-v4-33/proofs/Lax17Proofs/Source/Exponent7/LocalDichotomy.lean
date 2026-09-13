import Lax17Proofs.Source.Exponent7.PseudoGridAmortized
import Lax17Proofs.Source.Theorem41

namespace Lax17Proofs

/-!
# Exponent-seven local crossbar-or-grid dichotomy

Chuzhoy--Tan Theorem 4.1 is combined with the amortized Section 5 branch under
the hypothesis `CleanMatchingDichotomyStatement reserve`.

The slicing cost uses the uniform pseudo-grid row bound `64*q^6`.
`NumericalBounds` bounds this expression by
`C * q^6 * ell * (log_2 q + 1)^3`.
-/

namespace SimpleGraph
namespace Exponent7

open Finset
open Section4Reduction

universe u

/-- The uniform Theorem 4.6 cost before the factor-four pseudo-grid
retention loss. -/
def exponentSevenLocalCost (q ell : ℕ) : ℕ :=
  exponentSevenUniformSlices q ell * (64 * q ^ 6) +
    (exponentSevenUniformSlices q ell + 1) * (64 * q ^ 6)

/-- The exact local threshold.  The factor eight simultaneously pays for the
pseudo-grid discarded paths and the complete uniform slicing cost. -/
def exponentSevenLocalThreshold (q ell : ℕ) : ℕ :=
  8 * exponentSevenLocalCost q ell

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {q ell kappa : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- Every pseudo-grid row linkage is bounded by the uniform `64*q^6` row
budget used in the local cost. -/
theorem rowPacking_card_le_uniformBound
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q) :
    Gamma.rowPacking.card ≤ 64 * q ^ 6 := by
  calc
    Gamma.rowPacking.card = Gamma.reservedUnion.card := by simp
    _ ≤ (64 * q ^ 4) * q ^ 2 := Gamma.reservedUnion_card_le
    _ = 64 * q ^ 6 := by ring

/-- The Theorem 4.6 slicing cost is bounded by the uniform cost, independently
of how many rows survive the pseudo-grid construction. -/
theorem slicingCost_le_uniformCost
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q) :
    exponentSevenUniformSlices q ell * Gamma.rowPacking.card +
          (exponentSevenUniformSlices q ell + 1) *
            Gamma.rowPacking.card ≤
      exponentSevenLocalCost q ell := by
  unfold exponentSevenLocalCost
  exact Nat.add_le_add
    (Nat.mul_le_mul_left _
      (rowPacking_card_le_uniformBound Gamma))
    (Nat.mul_le_mul_left _
      (rowPacking_card_le_uniformBound Gamma))

/-- The paths discarded before Observation 4.4 fit inside the same uniform
cost. -/
theorem discardCost_le_uniformCost
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q)
    (hell : 0 < ell) :
    (64 * q ^ 4) * (2 * q ^ 2) ≤
      exponentSevenLocalCost q ell := by
  have hM :
      2 ≤ exponentSevenUniformSlices q ell + 1 := by
    have := exponentSevenUniformSlices_pos
      (q := q) (ell := ell) hell
    omega
  calc
    (64 * q ^ 4) * (2 * q ^ 2) =
        2 * (64 * q ^ 6) := by ring
    _ ≤ (exponentSevenUniformSlices q ell + 1) *
          (64 * q ^ 6) :=
      Nat.mul_le_mul_right (64 * q ^ 6) hM
    _ ≤ exponentSevenUniformSlices q ell * (64 * q ^ 6) +
          (exponentSevenUniformSlices q ell + 1) *
            (64 * q ^ 6) :=
      Nat.le_add_left _ _
    _ = exponentSevenLocalCost q ell := rfl

/-- The uniform local threshold leaves enough retained pseudo-grid paths for
the complete amortized slicing construction. -/
theorem uniform_slicing_budget
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q)
    (hell : 0 < ell)
    (hlarge : exponentSevenLocalThreshold q ell ≤ kappa)
    (hPcard : P.card = kappa) :
    exponentSevenUniformSlices q ell * Gamma.rowPacking.card +
          (exponentSevenUniformSlices q ell + 1) *
            Gamma.rowPacking.card ≤
      Gamma.goodQSet.card := by
  let actual :=
    exponentSevenUniformSlices q ell * Gamma.rowPacking.card +
      (exponentSevenUniformSlices q ell + 1) *
        Gamma.rowPacking.card
  let cost := exponentSevenLocalCost q ell
  let discarded := (64 * q ^ 4) * (2 * q ^ 2)
  have hactual : actual ≤ cost := by
    simpa [actual, cost] using
      slicingCost_le_uniformCost (ell := ell) Gamma
  have hdiscard : discarded ≤ cost := by
    simpa [discarded, cost] using
      discardCost_le_uniformCost (ell := ell) Gamma hell
  have htotal : 4 * (discarded + actual) ≤ kappa := by
    calc
      4 * (discarded + actual) ≤ 4 * (cost + cost) :=
        Nat.mul_le_mul_left 4 (Nat.add_le_add hdiscard hactual)
      _ = exponentSevenLocalThreshold q ell := by
        simp [exponentSevenLocalThreshold, cost]
        ring
      _ ≤ kappa := hlarge
  apply Gamma.goodQSet_card_lower_bound_of_packing_bound
  rw [hPcard]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  simpa [discarded, actual, Nat.mul_comm] using htotal

/-- Under the same threshold the retained pseudo-grid family is nonempty.
This is kept separate from `uniform_slicing_budget`, since the actual slicing
cost could be zero before row nonemptiness has been recovered. -/
theorem goodQSet_nonempty_of_uniformThreshold
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q)
    (hq : 2 ≤ q)
    (hell : 0 < ell)
    (hlarge : exponentSevenLocalThreshold q ell ≤ kappa)
    (hPcard : P.card = kappa) :
    Gamma.goodQSet.Nonempty := by
  have hcostPos : 0 < exponentSevenLocalCost q ell := by
    unfold exponentSevenLocalCost
    have hq6 : 0 < 64 * q ^ 6 := by positivity
    exact Nat.add_pos_right _ (Nat.mul_pos (by omega) hq6)
  have hdiscard :=
    discardCost_le_uniformCost (ell := ell) Gamma hell
  have hone : 1 ≤ exponentSevenLocalCost q ell := hcostPos
  have htotal :
      4 * ((64 * q ^ 4) * (2 * q ^ 2) + 1) ≤ kappa := by
    calc
      4 * ((64 * q ^ 4) * (2 * q ^ 2) + 1)
          ≤ 4 *
              (exponentSevenLocalCost q ell +
                exponentSevenLocalCost q ell) :=
        Nat.mul_le_mul_left 4 (Nat.add_le_add hdiscard hone)
      _ = exponentSevenLocalThreshold q ell := by
        simp [exponentSevenLocalThreshold]
        ring
      _ ≤ kappa := hlarge
  have honeGood : 1 ≤ Gamma.goodQSet.card := by
    apply Gamma.goodQSet_card_lower_bound_of_packing_bound
    rw [hPcard]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
    simpa [Nat.mul_comm] using htotal
  exact Finset.card_pos.mp (by omega)

end PseudoGrid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Local Chuzhoy--Tan dichotomy at the exponent-seven parameters.

If Theorem 4.1 does not return a `q^2` crossbar, the pseudo-grid branch runs
the uniform amortized recursion and the short-wide consumer, producing the
target `g`-grid. -/
theorem localCrossbar_or_grid
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V)
    {q g reserve kappa : ℕ}
    {A B X : Finset V}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hg : 2 ≤ g)
    (hreserve : 0 < reserve)
    (hscaledWidth : 20000 * (reserve * g ^ 2) ≤ q ^ 2)
    (hA : A.card = kappa)
    (hB : B.card = kappa)
    (hX : X.card = kappa)
    (hAB : Disjoint A B)
    (hAX : Disjoint A X)
    (hBX : Disjoint B X)
    (hlarge :
      exponentSevenLocalThreshold q (2 * g) ≤ kappa)
    (hdegree : ∀ x ∈ X, DegreeEquals H x 1)
    (Pab : PathPacking H A B)
    (hPab : Pab.card = kappa)
    (Pax : PathPacking H A X)
    (hPax : Pax.card = kappa) :
    Nonempty (Crossbar H A B X (q ^ 2)) ∨
      ContainsGridMinor H g := by
  have hell : 0 < 2 * g := by omega
  have hdiscardCost :
      (64 * q ^ 4) * (2 * q ^ 2) ≤
        exponentSevenLocalCost q (2 * g) := by
    have hM :
        2 ≤ exponentSevenUniformSlices q (2 * g) + 1 := by
      have := exponentSevenUniformSlices_pos
        (q := q) (ell := 2 * g) hell
      omega
    calc
      (64 * q ^ 4) * (2 * q ^ 2) =
          2 * (64 * q ^ 6) := by ring
      _ ≤ (exponentSevenUniformSlices q (2 * g) + 1) *
            (64 * q ^ 6) :=
        Nat.mul_le_mul_right (64 * q ^ 6) hM
      _ ≤ exponentSevenLocalCost q (2 * g) := by
        unfold exponentSevenLocalCost
        exact Nat.le_add_left _ _
  have hdepthCost :
      (64 * q ^ 4) * (2 * q ^ 2) ≤ kappa := by
    calc
      (64 * q ^ 4) * (2 * q ^ 2)
          ≤ exponentSevenLocalCost q (2 * g) := hdiscardCost
      _ ≤ 8 * exponentSevenLocalCost q (2 * g) := by omega
      _ = exponentSevenLocalThreshold q (2 * g) := rfl
      _ ≤ kappa := hlarge
  have hDle :
      64 * q ^ 4 ≤ kappa / (2 * q ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * q ^ 2)).2
    exact hdepthCost
  rcases
      theorem_four_one_of_pathPackings
        H hq hpow hA hB hX hAB hAX hBX hdegree
        Pab hPab Pax hPax
        (Nat.succ_le_of_lt (by positivity))
        hDle with
    ⟨P, Q, hPcard, hQcard, hminimal, hconclusion⟩
  rcases hconclusion with hcross | hpseudo
  · exact Or.inl hcross
  · by_cases hcross : Nonempty (Crossbar H A B X (q ^ 2))
    · exact Or.inl hcross
    · rcases hpseudo with ⟨Gamma⟩
      have hXdisjoint :
          ∀ p : P.Index, Disjoint X (P.path p).vertexSet := by
        let Setup : Theorem41Setup
            H A B X q kappa (64 * q ^ 4) P Q :=
          { two_le_g := hq
            g_power_two := hpow
            A_card := hA
            B_card := hB
            X_card := hX
            disjoint_A_B := hAB
            disjoint_A_X := hAX
            disjoint_B_X := hBX
            degree_X := hdegree
            P_card := hPcard
            Q_card := hQcard
            minimal_pair := hminimal
            D_pos := by
              have : 0 < 64 * q ^ 4 := by positivity
              omega
            D_le := hDle }
        intro p
        exact (Setup.P_path_disjoint_X p).symm
      have hgood :
          exponentSevenUniformSlices q (2 * g) *
                Gamma.rowPacking.card +
              (exponentSevenUniformSlices q (2 * g) + 1) *
            Gamma.rowPacking.card ≤
            Gamma.goodQSet.card :=
        SimpleGraph.Exponent7.PseudoGrid.uniform_slicing_budget
          Gamma hell hlarge hPcard
      have hgoodNonempty : Gamma.goodQSet.Nonempty :=
        SimpleGraph.Exponent7.PseudoGrid.goodQSet_nonempty_of_uniformThreshold
          Gamma
          hq hell hlarge hPcard
      have hrowBounds :
          64 * q ^ 4 ≤ Gamma.rowPacking.card ∧
            Gamma.rowPacking.card ≤ 64 * q ^ 6 := by
        have h :=
          Gamma.rowPacking_card_bounds_of_goodQSet_nonempty
            hgoodNonempty
        constructor
        · exact h.1
        · simpa only [
            show (64 * q ^ 4) * q ^ 2 = 64 * q ^ 6 by ring]
            using h.2
      have hgrid : ContainsGridMinor H g :=
        SimpleGraph.Exponent7.gridMinor_of_pseudoGrid_noCrossbar
          (q := q) (D := 64 * q ^ 4) (ell := 2 * g)
          (g := g) (reserve := reserve)
          hDichotomy Gamma hminimal hq hpow
          hrowBounds.1 hrowBounds.2 le_rfl hgood
          hXdisjoint hcross hell hg le_rfl hreserve
          hscaledWidth
      exact Or.inr hgrid

end Exponent7
end SimpleGraph

end Lax17Proofs
