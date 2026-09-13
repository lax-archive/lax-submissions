import Lax17Proofs.Source.Exponent7.LocalDichotomy
import Lax17Proofs.Source.Exponent7.AmortizedPipeline
import Lax17Proofs.Source.Exponent7.NumericalBounds
import Lax17Proofs.Source.Exponent8.RootedSection42
import Lax17Proofs.Source.Section4Assembly

namespace Lax17Proofs

/-!
# Exact exponent-eight local crossbar dichotomy

The logarithmic-depth additive slicing controller is specialized to a square
Path-of-Sets output. Its general local cost is

$$
O\bigl(q^6 \ell (\log_2 q + 1)^3\bigr).
$$

Taking $\ell = q^2$ gives the threshold

$$
O\bigl(q^8 (\log_2 q + 1)^3\bigr).
$$

The weak square system is strongified by Section 4.6. In the crossbar branch,
`SliceLocalizationInvariant.lastHitCrossbar_direct` constructs each spoke as
a suffix of an original rooted `A`--`X` path after its last visit to a selected
full `A`--`B` row.
-/

namespace SimpleGraph
namespace Exponent8Polylog

universe u

open Finset
open Section4Reduction
open Exponent8
open Exponent7

/-- Exact local threshold before simplifying it to a monomial. -/
def exponentEightPolylogLocalThreshold (q : ℕ) : ℕ :=
  Exponent7.exponentSevenLocalThreshold q (q ^ 2)

/-- Explicit coefficient in the monomial local bound. -/
def exponentEightPolylogLocalConstant : ℕ := 2 ^ 37

/-- The amortized local cost has polynomial exponent eight. -/
theorem exponentEightPolylogLocalThreshold_le
    {q : ℕ} (hq : 0 < q) :
    exponentEightPolylogLocalThreshold q ≤
      exponentEightPolylogLocalConstant * q ^ 8 *
        (Nat.log 2 q + 1) ^ 3 := by
  calc
    exponentEightPolylogLocalThreshold q
        = Exponent7.exponentSevenLocalThreshold q (q ^ 2) := rfl
    _ ≤ Exponent7.exponentSevenLocalConstant * q ^ 6 * (q ^ 2) *
          (Nat.log 2 q + 1) ^ 3 :=
      Exponent7.exponentSevenLocalThreshold_le (by positivity)
    _ = exponentEightPolylogLocalConstant * q ^ 8 *
          (Nat.log 2 q + 1) ^ 3 := by
      simp [Exponent7.exponentSevenLocalConstant,
        exponentEightPolylogLocalConstant]
      ring

/-- Theorem 4.1's complete separator depth fits inside the exact local
threshold. -/
theorem theorem41_depthCost_le_exponentEightPolylogLocalThreshold
    {q : ℕ} (hq : 0 < q) :
    (64 * q ^ 4) * (2 * q ^ 2) ≤
      exponentEightPolylogLocalThreshold q := by
  have hM :
      2 ≤ Exponent7.exponentSevenUniformSlices q (q ^ 2) + 1 := by
    have hpos :=
      Exponent7.exponentSevenUniformSlices_pos
        (q := q) (ell := q ^ 2) (by positivity)
    omega
  calc
    (64 * q ^ 4) * (2 * q ^ 2) = 2 * (64 * q ^ 6) := by ring
    _ ≤ (Exponent7.exponentSevenUniformSlices q (q ^ 2) + 1) *
          (64 * q ^ 6) :=
      Nat.mul_le_mul_right (64 * q ^ 6) hM
    _ ≤ Exponent7.exponentSevenLocalCost q (q ^ 2) := by
      unfold Exponent7.exponentSevenLocalCost
      exact Nat.le_add_left _ _
    _ ≤ 8 * Exponent7.exponentSevenLocalCost q (q ^ 2) := by omega
    _ = exponentEightPolylogLocalThreshold q := rfl

/-- Structural input at the exponent-eight local threshold. -/
def CrossbarDichotomyInput8 (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {q kappa : ℕ}
    {A B X : Finset V},
      2 ≤ q →
        CrossbarContract.IsPowerOfTwo q →
          A.card = kappa →
            B.card = kappa →
              X.card = kappa →
                Disjoint A B →
                  Disjoint A X →
                    Disjoint B X →
                      exponentEightPolylogLocalThreshold q ≤ kappa →
                        (∀ x ∈ X, DegreeEquals H x 1) →
                          (Pab : PathPacking H A B) →
                            Pab.card = kappa →
                              (Pax : PathPacking H A X) →
                                Pax.card = kappa →
                                  Nonempty (Crossbar H A B X (q ^ 2)) ∨
                                    ∃ ell w : ℕ,
                                      q ^ 2 ≤ c * ell ∧
                                        q ^ 2 ≤ c * w ∧
                                          CrossbarContract.HasStrongPathOfSetsMinor
                                            H ell w

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {q kappa : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- The no-crossbar pseudo-grid branch produces a square strong
Path-of-Sets minor using the logarithmic-depth controller. -/
theorem hasStrongPathOfSetsMinor_of_noCrossbar
    (Gamma : PseudoGrid G A B X q (64 * q ^ 4) P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hlarge : exponentEightPolylogLocalThreshold q ≤ kappa)
    (hPcard : P.card = kappa)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (q ^ 2))) :
    ∃ ell w : ℕ,
      q ^ 2 ≤ 20000 * ell ∧
        q ^ 2 ≤ 20000 * w ∧
          CrossbarContract.HasStrongPathOfSetsMinor G ell w := by
  have hell : 0 < q ^ 2 := by positivity
  have hbudget :
      Exponent7.exponentSevenUniformSlices q (q ^ 2) *
            Gamma.rowPacking.card +
          (Exponent7.exponentSevenUniformSlices q (q ^ 2) + 1) *
            Gamma.rowPacking.card ≤
        Gamma.goodQSet.card := by
    apply Exponent7.PseudoGrid.uniform_slicing_budget
        (ell := q ^ 2) Gamma hell
    · simpa [exponentEightPolylogLocalThreshold] using hlarge
    · exact hPcard
  have hgood : Gamma.goodQSet.Nonempty :=
    Exponent7.PseudoGrid.goodQSet_nonempty_of_uniformThreshold
      (ell := q ^ 2) Gamma hq hell
      (by simpa [exponentEightPolylogLocalThreshold] using hlarge)
      hPcard
  have hrowBounds :
      64 * q ^ 4 ≤ Gamma.rowPacking.card ∧
        Gamma.rowPacking.card ≤ 64 * q ^ 6 := by
    have h := Gamma.rowPacking_card_bounds_of_goodQSet_nonempty hgood
    constructor
    · exact h.1
    · simpa only [show (64 * q ^ 4) * q ^ 2 = 64 * q ^ 6 by ring]
        using h.2
  have hNpos : 0 < Gamma.rowPacking.card := by
    have : 0 < 64 * q ^ 4 := by positivity
    exact this.trans_le hrowBounds.1
  have hMpos :
      0 < Exponent7.exponentSevenUniformSlices q (q ^ 2) :=
    Exponent7.exponentSevenUniformSlices_pos hell
  have hDpos : 0 < 64 * q ^ 4 := by positivity
  have hDhatPos : 0 < 32 * q ^ 4 := by positivity
  have hmass :
      2 * Gamma.rowPacking.card * (4 * q ^ 2) ≤
        (32 * q ^ 4) * Gamma.rowPacking.card := by
    have hsmall : 2 * (4 * q ^ 2) ≤ 32 * q ^ 4 := by
      have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      nlinarith
    calc
      2 * Gamma.rowPacking.card * (4 * q ^ 2) =
          Gamma.rowPacking.card * (2 * (4 * q ^ 2)) := by ring
      _ ≤ Gamma.rowPacking.card * (32 * q ^ 4) :=
        Nat.mul_le_mul_left Gamma.rowPacking.card hsmall
      _ = (32 * q ^ 4) * Gamma.rowPacking.card := by ring
  obtain ⟨Root, hReduced, ⟨L0⟩⟩ :=
    Exponent8.exists_initialRecursiveSliceLayer_of_pseudoGrid
      Gamma hminimal hDpos hMpos hNpos hbudget hDhatPos
      (by
        rw [show 2 * (32 * q ^ 4) = 64 * q ^ 4 by ring])
      hmass hXdisjoint
  let H := Root.state.reducedGraph hReduced
  let Rbar := Root.state.reducedRow hReduced
  let Qbar := Root.state.reducedRetained hReduced
  have hRcard : Rbar.card = Gamma.rowPacking.card := by
    simp [Rbar]
  have hRlower : 64 * q ^ 4 ≤ Rbar.card := by
    simpa [hRcard] using hrowBounds.1
  have hRupper : Rbar.card ≤ 64 * q ^ 6 := by
    simpa [hRcard] using hrowBounds.2
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar := by
    simpa [Rbar, Qbar] using
      Root.state.reducedRetained_intersects_reducedRow hReduced hDpos
  let C :=
    Root.recursiveSlicingContext
      hReduced hNpos hDhatPos
        (by
          rw [show 2 * (32 * q ^ 4) = 64 * q ^ 4 by ring])
        hXdisjoint
  let L0' : Exponent8.RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (Exponent7.exponentSevenUniformSlices q (q ^ 2))
      Rbar.card (4 * q ^ 2) (32 * q ^ 4) := by
    simpa [H, Rbar, Qbar, hRcard] using L0
  obtain ⟨Pweak⟩ :=
    Exponent7.weakPathOfSetsSystem_of_uniformAmortizedPipeline
      C L0' hintersects hq hpow hell hRlower hRupper hnoCrossbar
  let w := Section4Assembly.strongifiedWidth (q ^ 2)
  let Dstrong :=
    Section4Assembly.strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
      Pweak (Root.state.reducedGraph_maxDegreeAtMost_four hReduced)
  let Pstrong : StrongPathOfSetsSystem H (q ^ 2) w :=
    Section46.strong_pathOfSetsSystem_of_strongificationData Pweak Dstrong
  refine ⟨q ^ 2, w, ?_, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_left (q ^ 2) (by norm_num)
  · exact
      Section4Assembly.le_twentyThousand_mul_strongifiedWidth
        (by positivity)
  · exact
      ⟨Root.state.RowVertex, inferInstance, inferInstance,
        H, by simpa [H] using Root.state.reducedGraph_isMinor hReduced,
        ⟨Pstrong⟩⟩

end PseudoGrid

/-- Exponent-eight local structural theorem. -/
theorem crossbarDichotomyInput8_proved :
    CrossbarDichotomyInput8.{u} 20000 := by
  intro V _ _ H q kappa A B X hq hpow hA hB hX hAB hAX hBX
    hlarge hdegree Pab hPab Pax hPax
  have hdepthCost :
      (64 * q ^ 4) * (2 * q ^ 2) ≤ kappa :=
    (theorem41_depthCost_le_exponentEightPolylogLocalThreshold
      (by omega)).trans hlarge
  have hDle :
      64 * q ^ 4 ≤ kappa / (2 * q ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * q ^ 2)).2
    exact hdepthCost
  rcases
      theorem_four_one_of_pathPackings
        H hq hpow hA hB hX hAB hAX hBX hdegree
        Pab hPab Pax hPax
        (by
          have : 0 < 64 * q ^ 4 := by positivity
          omega)
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
      exact Or.inr <|
        PseudoGrid.hasStrongPathOfSetsMinor_of_noCrossbar
          Gamma hminimal hq hpow hlarge hPcard hXdisjoint hcross

end Exponent8Polylog
end SimpleGraph

end Lax17Proofs
